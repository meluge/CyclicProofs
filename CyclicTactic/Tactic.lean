import Lean
import CyclicTactic.ProofTree
import CyclicTactic.SizeChange
import CyclicTactic.InductionOrder
import CyclicTactic.Build

/-!
# v0.4 of the tactic-mode cyclic proof API

Real cyclic proof system. Key design:

  * `cyclic_thm name (binders) : type by tactics` — a *command* that
    desugars to `def name : ∀ binders, type := by tactics`. The body
    is a recursive function; the recursive calls (= back-edges) are
    inserted by `back`.
  * `cyclic <label>` — records the current goal as the companion
    sequent under `<label>`. Doesn't change the goal.
  * `back <label> [{σ}]` — closes the current goal via a *recursive
    call* to the enclosing theorem. `back R {n := n'}` becomes
    `exact <thmName> n'` (with σ values mapped to binder positions).
  * Soundness: Lean's existing recursion-termination check guarantees
    the proof is well-founded. SCT validation runs as a parallel
    side-check (catches issues sooner than termination would).

This is genuinely cyclic — no `induction`, no implicit IH binding.
`cases` is a real case-split, `back R {σ}` is a real back-edge that
closes the goal by recursive descent.

Limitations of v0.4:

  * Lean's structural recursion handles single-argument inductive
    descent only. For lex-style termination (Ackermann), we'd need to
    emit `termination_by` from SCT analysis. Future v0.5.
  * No path-inferred σ (the user must spell it out).
  * No per-arm tracking in `cyc_cases` (deferred until needed).
-/

namespace CyclicTactic

open Lean Elab Tactic Meta
open CyclicTactic.Proof   -- for SubjectTerm, Sequent, etc.

/-! ### Cyclic state

The state types (`SubstEntry`, `CyclicEvent`, `CyclicState`) and
state-management helpers (`getCyclicState`, `pushEvent`, …) live in
`CyclicTactic.Build` so the tree builder there can operate on them
without an import cycle. They're in scope here via the import. -/

/-! ### Per-`cyclic_thm` context

When the `cyclic_thm` command is elaborating, we record the theorem's
name + binder names so the `back` tactic can build the correct
recursive call. -/

structure ThmContext where
  /-- The theorem being elaborated (the recursive function's name). -/
  thmName : Lean.Name
  /-- The binders in declaration order. `back R {σ}` maps σ entries to
      these positions. -/
  binders : List Lean.Name
  deriving Inhabited

initialize currentThmRef : IO.Ref (Option ThmContext) ← IO.mkRef none

def setCurrentThm (ctx : Option ThmContext) : IO Unit := currentThmRef.set ctx
def getCurrentThm : IO (Option ThmContext) := currentThmRef.get

/-! ### Mutual-block context

When elaborating a `cyclic_mutual ... end` block, we need to resolve
back-edges that target a *different* theorem's induction hypothesis.

  * `mutualThmCtxsRef` — list of every `ThmContext` in the current
    block (consulted by the hidden `_set_active` tactic).
  * `mutualCompanionTargetRef` — companion-label → target-`ThmContext`
    map, populated by `cyclic R` and consulted by `back R {σ}`. A
    cross-companion back-edge resolves R to the theorem that owns it,
    whose binders + name are then used to construct the recursive
    call. For non-mutual `cyclic_thm` the table is empty and `back`
    falls through to `currentThmRef` (existing behaviour). -/

initialize mutualThmCtxsRef : IO.Ref (List ThmContext) ← IO.mkRef []
initialize mutualCompanionTargetRef : IO.Ref (List (String × ThmContext)) ← IO.mkRef []

def setMutualThmCtxs (cs : List ThmContext) : IO Unit := mutualThmCtxsRef.set cs
def getMutualThmCtxs : IO (List ThmContext) := mutualThmCtxsRef.get
def addMutualCompanion (label : String) (ctx : ThmContext) : IO Unit :=
  mutualCompanionTargetRef.modify fun ts => (label, ctx) :: ts
def lookupMutualCompanion (label : String) : IO (Option ThmContext) := do
  let ts ← mutualCompanionTargetRef.get
  return (ts.find? (·.1 == label)).map (·.2)
def resetMutualState : IO Unit := do
  mutualThmCtxsRef.set []
  mutualCompanionTargetRef.set []

-- (modifyCyclicState and pushEvent live in CyclicTactic.Build)

/-! ### `cyclic <label>` tactic

Resets the cyclic state to a fresh one with `<label>` as the sole
companion at the current goal. v0.2: still no IH binding — `back`
closes via `sorry`. -/

syntax (name := cyclicTac) "cyclic " ident : tactic

@[tactic cyclicTac]
def evalCyclic : Tactic := fun stx => do
  match stx with
  | `(tactic| cyclic $label:ident) =>
    let labelStr := label.getId.toString
    let goal ← getMainGoal
    let target ← goal.getType
    let seq : Sequent ← match ← getCurrentThm with
      | some ctx =>
        let predName := ctx.thmName.toString
        let args : List SubjectTerm := ctx.binders.map fun b => .var b.toString
        pure (Sequent.succ1 { pred := predName, args := args })
      | none =>
        Build.exprToSequent target
    -- Extract the goal's head constant (e.g. `btPred` for
    -- `btPred t n`) so the Unravel emission can use it as the
    -- defaultSimpPred — needed to unfold the predicate at leaves
    -- and inside `branch` preludes.
    let target' ← Lean.instantiateMVars target
    let goalHeadName : Option String := match target'.consumeMData.getAppFn with
      | .const n _ => some n.toString
      | _          => none
    -- Append (don't replace) so multiple companions accumulate across
    -- the entries of a `cyclic_mutual` block. For single-`cyclic_thm`
    -- the state is reset by the command itself before elaboration, so
    -- this still produces a singleton list there.
    let st ← getCyclicState
    cyclicStateRef.set {
      st with
      companions := st.companions ++ [(labelStr, seq)]
      events := .companion labelStr seq :: st.events
      goalHeadName := st.goalHeadName.orElse (fun _ => goalHeadName)
    }
    -- Resolve the *active* theorem for this `cyclic R` call. In a
    -- `cyclic_mutual` block, multiple defs share the same elabCommand
    -- invocation; we identify which one we're inside via the current
    -- decl name (Lean tracks this for recursion-detection purposes).
    -- For single `cyclic_thm`, the mutual table is empty and we fall
    -- back to `currentThmRef`.
    let mutCtxs ← getMutualThmCtxs
    let activeCtx? : Option ThmContext ← do
      match (← Lean.Elab.Term.getDeclName?) with
      | some declName =>
        match mutCtxs.find? (·.thmName == declName) with
        | some c => pure (some c)
        | none   => getCurrentThm
      | none => getCurrentThm
    if let some ctx := activeCtx? then
      -- Set as current so `back R {σ}` (without a target lookup hit)
      -- still works inside this body, and register R → ctx.
      setCurrentThm (some ctx)
      addMutualCompanion labelStr ctx
    logInfoAt label m!"[cyclic] companion '{labelStr}' = {target}"
  | _ => throwUnsupportedSyntax

/-! ### `back <label> [{σ}]` tactic

Closes the current goal via a *recursive call to the enclosing
theorem*. The recursive call's args come from σ — each σ entry
matched by name to a binder of the enclosing `cyclic_thm`.

`back R {n := n'}` (inside `cyclic_thm zeroAddT (n : Nat) : ... by ...`)
becomes `exact zeroAddT n'`. Lean's recursion-termination check
verifies the call terminates (structural recursion for single-arg
descent; `termination_by` would be needed for lex — future work).

This is the back-edge primitive. No IH from `induction`, no `sorry`.
The proof IS recursive descent — Lean's kernel checks termination. -/

syntax substItem := ident " := " term
syntax cycSubst := "{" substItem,* "}"

syntax (name := backTac) "back " ident (cycSubst)? : tactic

/-- Parse a σ as a list of (var, value-Expr) pairs. -/
private def parseSubstExprs (stx : Lean.Syntax) : TacticM (List (String × Lean.Expr)) := do
  Lean.Elab.Tactic.withMainContext do
    match stx with
    | `(cycSubst| { $items:substItem,* }) =>
      items.getElems.toList.mapM fun (item : Lean.TSyntax `CyclicTactic.substItem) => do
        match item with
        | `(substItem| $v:ident := $t:term) =>
          let value ← Lean.Elab.Term.elabTerm t none
          return (v.getId.toString, value)
        | _ => throwError "back: malformed substitution item"
    | _ => throwError "back: expected substitution braces"

@[tactic backTac]
def evalBack : Tactic := fun stx => do
  match stx with
  | `(tactic| back $label:ident $[$σStx?]?) =>
    let labelStr := label.getId.toString
    Lean.Elab.Tactic.withMainContext do
      let goal ← getMainGoal
      let target ← goal.getType
      let st ← getCyclicState
      -- The companion must exist either in the live `cyclicStateRef`
      -- (registered by a prior `cyclic R` call) or in the mutual
      -- table (pre-registered by `cyclic_mutual` from syntax). Without
      -- the second branch, a `back R_E` from inside the first entry
      -- of a mutual block — before R_E's defining `cyclic` has run —
      -- would falsely report R_E as out-of-scope.
      let liveCompanion := st.companions.find? (·.1 == labelStr)
      let mutCompanion ← lookupMutualCompanion labelStr
      if liveCompanion.isNone ∧ mutCompanion.isNone then
        let availLive := st.companions.map (·.1)
        let availMut := (← mutualCompanionTargetRef.get).map (·.1)
        throwError s!"back: no companion '{labelStr}' in scope. \
          Available (live): {availLive}; (mutual): {availMut}"
      -- Parse σ as raw (var, Expr) pairs.
      let σExprs : List (String × Lean.Expr) ← match σStx? with
        | none     => pure []
        | some stx => parseSubstExprs stx
      -- Resolve the *target* theorem for this back-edge. In a
      -- `cyclic_mutual` block, R may belong to a different theorem
      -- than the one currently elaborating; the mutual companion table
      -- records (R → target-ThmContext). For a plain `cyclic_thm`,
      -- the table either has the lookup (registered when `cyclic R`
      -- ran) or is empty, in which case we fall back to the enclosing
      -- theorem's context.
      let resolved ← lookupMutualCompanion labelStr
      let thmCtx : ThmContext ← match resolved with
        | some ctx => pure ctx
        | none =>
          match ← getCurrentThm with
          | some ctx => pure ctx
          | none =>
            throwError "back: not inside a `cyclic_thm` or \
              `cyclic_mutual` command."
      -- Map σ entries to binder positions for the recursive call.
      let argExprs : Array Lean.Expr ← thmCtx.binders.toArray.mapM fun bname => do
        match σExprs.find? (·.1 == bname.toString) with
        | some (_, e) => pure e
        | none   =>
          throwError s!"back: σ missing entry for binder '{bname}' \
            (theorem '{thmCtx.thmName}' takes binders [{thmCtx.binders.map toString}])"
      -- Issue the recursive call.
      let recCall := Lean.mkAppN (Lean.mkConst thmCtx.thmName) argExprs
      let recCallStx ← Lean.PrettyPrinter.delab recCall
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact $recCallStx))
      -- Record back-edge as `<thmName>(σ-mapped-binder-values)` so the
      -- sequent matches the companion's shape. SCT then sees clean
      -- per-binder descent.
      let σData : CyclicTactic.Proof.Subst ← σExprs.mapM fun (v, e) => do
        return (v, ← Build.exprToSubject e)
      let bSeq : Sequent :=
        let bArgs : List SubjectTerm := thmCtx.binders.map fun b =>
          (σData.lookup b.toString).getD (.var b.toString)
        Sequent.succ1 { pred := thmCtx.thmName.toString, args := bArgs }
      let _ := target  -- unused now (we use thm-name shape, not goal)
      let pos : Nat := match stx.getPos? with
        | some p => p.byteIdx
        | none   => 0
      -- Capture the back call's source text so the tree builder can
      -- substitute it with `recurse` inside the arm prelude.
      let sourceText : String := (stx.reprint).getD ""
      pushEvent (.back labelStr bSeq σData pos sourceText.trim)
      let σDoc : MessageData :=
        MessageData.joinSep (σData.map fun (v, t) => m!"{v} := {t}") ", "
      let σLine := if σData.isEmpty then m!"" else m!"\n  σ: {σDoc}"
      logInfoAt label m!"[back] {labelStr} → recursive call to '{thmCtx.thmName}' ({argExprs.size} arg(s)){σLine}"
  | _ => throwUnsupportedSyntax

/-! ### `cyc_cases <var> with | <pat> => <tac> | …` tactic

Performs a case-split on `<var>` AND records `caseSplitStart` /
`armStart` / `armEnd` / `caseSplitEnd` events into the cyclic state,
delimiting each arm's body so the Phase-B tree builder can attribute
back-edges to the correct arm.

Implementation: instead of delegating to Lean's `cases` tactic
wholesale (which would lose per-arm boundaries), we manually do the
case-split via `MVarId.cases` and elaborate each arm body in the
right subgoal context — pushing arm-boundary events around each. -/

syntax (name := cycCasesTac) "cyc_cases " ident " with " (Lean.Parser.Tactic.inductionAlt)+ : tactic

/-- Recursive search for the first `ident` Syntax in a tree. Robust to
    position-shift variations in surrounding syntax wrappers. -/
private partial def findFirstIdent : Lean.Syntax → Option Lean.Name
  | .ident _ _ n _ => some n
  | .node _ _ args =>
    args.foldl (init := none) fun acc c =>
      match acc with
      | some _ => acc
      | none   => findFirstIdent c
  | _              => none

/-- Collect ALL idents recursively from a Syntax tree, in source order. -/
private partial def collectAllIdents : Lean.Syntax → List Lean.Name
  | .ident _ _ n _ => [n]
  | .node _ _ args =>
    args.foldl (init := []) fun acc c => acc ++ collectAllIdents c
  | _              => []

@[tactic cycCasesTac]
def evalCycCases : Tactic := fun stx => do
  match stx with
  | `(tactic| cyc_cases $var:ident with $arms:inductionAlt*) =>
    let varName := var.getId.toString
    let goal ← getMainGoal
    let target ← goal.getType
    -- Same thm-name-shape sequent as `cyclic` produces.
    let seq : Sequent ← match ← getCurrentThm with
      | some ctx =>
        let args : List SubjectTerm := ctx.binders.map fun b => .var b.toString
        pure (Sequent.succ1 { pred := ctx.thmName.toString, args := args })
      | none =>
        Build.exprToSequent target
    -- Extract per-arm constructor + binder names + source range from
    -- each inductionAlt's syntax. The LHS area (`arm.raw[1]`) contains
    -- the constructor + binders; we walk it to collect all idents in
    -- source order — first is ctor, rest are binders. The range is
    -- used by the tree builder for back-edge attribution.
    -- inductionAlt's syntax tree has 2 args:
    --   arg 0 = inductionAltLHS+ (the constructor + binders)
    --   arg 1 = body (termOrTacticSeq)
    -- (The `|` and `=>` are pretty-printer tokens, not syntax-tree
    -- atoms — that's why the `numArgs == 2` is surprising.)
    let armInfos : List ArmInfo := arms.toList.map fun arm =>
      let lhsArea := arm.raw[0]
      let bodyArea := arm.raw[1]
      let allIdents := collectAllIdents lhsArea
      let (ctor, binders) := match allIdents with
        | []         => (Lean.Name.anonymous, [])
        | x :: rest  => (x, rest)
      let binders := binders.filter (· != var.getId)
      let range : SourceRange :=
        match arm.raw.getRange? with
        | some r => { startPos := r.start.byteIdx, endPos := r.stop.byteIdx }
        | none   => { startPos := 0, endPos := 0 }
      -- Capture the body's source text for Unravel emission. Used as
      -- the leaf's closeTactic when the arm has no back-edge, or as
      -- the prelude (with the back call's text replaced by `recurse`)
      -- when the arm has one. `Syntax.reprint` reconstructs the source.
      -- The reprint sometimes includes the leading `=>` separator
      -- because the parser combines it with the body; strip it.
      let bodyTextRaw : String := (bodyArea.reprint).getD ""
      let trimmed : String := bodyTextRaw.trim
      let bodyText : String :=
        if trimmed.startsWith "=>" then ((trimmed.drop 2).trim : String.Slice).toString
        else trimmed
      { ctor := ctor, binders := binders, range := range, bodyText := bodyText }
    pushEvent (.caseSplitStart varName seq armInfos)
    -- Delegate arm-body elaboration to Lean's standard cases.
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| cases $var:ident with $arms:inductionAlt*))
    pushEvent .caseSplitEnd
  | _ => throwUnsupportedSyntax

/-! ### `cyclic_thm` command

The entry point. Parses `cyclic_thm name (binders) : type by tactics`
and elaborates as `def name : ∀ binders, type := by tactics`. While
the body elaborates, `back R {σ}` can issue recursive calls to
`name`. Lean's recursion-termination check accepts the def iff the
back-edges descend (structural recursion for v0.4; lex needs
`termination_by` from SCT — future). -/

/-- One bracketed binder group `(x y z : T)`. -/
syntax cycThmBinder := "(" ident+ " : " term ")"

syntax (name := cyclicThmCmd)
  "cyclic_thm " ident cycThmBinder+ " : " term " by " Lean.Parser.Tactic.tacticSeq
  : command

@[command_elab cyclicThmCmd]
def elabCyclicThm : Lean.Elab.Command.CommandElab := fun stx => do
  match stx with
  | `(cyclic_thm $name:ident $binders:cycThmBinder* : $type:term by $tacs:tacticSeq) => do
    -- Extract binder names + reconstruct standard bracketed-binder syntax
    -- so we can hand it to Lean's def elaborator.
    let mut flatBinderNames : List Lean.Name := []
    let mut binderTypes : List (Lean.Name × Lean.TSyntax `term) := []
    let mut bracketedBinders : Array (Lean.TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
    for b in binders do
      match b with
      | `(cycThmBinder| ($vs:ident* : $bt:term)) =>
        for v in vs do
          flatBinderNames := flatBinderNames ++ [v.getId]
          binderTypes := binderTypes ++ [(v.getId, bt)]
        let bb ← `(Lean.Parser.Term.bracketedBinderF| ($vs* : $bt))
        bracketedBinders := bracketedBinders.push bb
      | _ =>
        Lean.throwErrorAt b "cyclic_thm: malformed binder"
    -- Architectural completion: `<name>` is the only declaration we
    -- ever add. We elaborate it as a recursive `def` first (so the
    -- InfoView shows real Lean goals during writing AND we capture
    -- cyclic events from the firing tactics). If the Unravel emission
    -- subsequently elaborates cleanly, we ROLL BACK env to before the
    -- recursive elaboration and replace `<name>` with the canonical
    -- Unravel form. If Unravel fails, the recursive form stands as the
    -- fallback. Either way: one name, one declaration.
    --
    -- `back R {σ}` issues `exact <name> σ` — recursive call to the
    -- user's name. This works because Lean's `def` allows the body to
    -- reference the def's own name.
    let envBefore ← Lean.getEnv
    -- Fresh recorder + companion state per `cyclic_thm`. `cyclic R`
    -- now appends rather than resets, so leakage from a previous
    -- command would otherwise contaminate this one's tree.
    resetCyclicState
    resetMutualState
    setCurrentThm (some { thmName := name.getId, binders := flatBinderNames })
    Lean.Elab.Command.elabCommand
      (← `(def $name:ident $bracketedBinders* : $type:term := by $tacs:tacticSeq))
    -- Phase B: build a ProofTree from recorded events.
    let st ← getCyclicState
    let events := st.events.reverse
    let tree := Build.eventsToTree events
    -- Phase C: run SCT validation (extractTraceSCGsLabeled →
    -- checkMultiSCT → findInductionOrder Wehr 3.2.4) on the tree.
    let labeled := Proof.extractTraceSCGsLabeled tree
    let graphs := labeled.map (·.2)
    let rootSeq := tree.sequent
    let arity : Nat :=
      let ns := rootSeq.antecedents.map (·.args.length) ++
                rootSeq.succedents.map (·.args.length)
      ns.foldl (· + ·) 0
    let sctOk := SCGraph.checkMultiSCT graphs
    let order := InductionOrder.findInductionOrder tree labeled arity
    let sctMsg := if sctOk then "PASS ✓" else "FAIL ✗"
    let orderMsg : String := match order with
      | some asg =>
        let asgStr := String.intercalate ", "
          (asg.map fun (lbl, p) => s!"{lbl}→a{p}")
        let lexOrder := InductionOrder.lexOrderFromAssignment asg
        let lexStr := String.intercalate " ≻ " (lexOrder.map fun p => s!"a{p}")
        s!"Wehr 3.2.4 order: lex [{lexStr}]; per-bud: {asgStr}"
      | none => "Wehr 3.2.4: no lex induction order"
    let graphsStr :=
      if labeled.isEmpty then "  (no back-edges)"
      else String.intercalate "\n" (labeled.map fun (l, g) => s!"  {l}: {g}")
    Lean.logInfoAt name m!"[cyclic_thm {name.getId}] SCT: {sctMsg}\n{orderMsg}\nback-edge SCGs:\n{graphsStr}\n\nProofTree:\n{Build.renderTree tree}"
    -- Snapshot env-with-recursive so we can restore the recursive
    -- form if Unravel emission fails.
    let envWithRecursive ← Lean.getEnv
    -- Phase E: try Unravel canonical. On success, we roll back env to
    -- BEFORE the recursive elaboration and commit Unravel as <name>.
    -- On failure, we restore envWithRecursive so the recursive form
    -- stands as the user-facing declaration.
    if sctOk then
      let varSorts ← Lean.Elab.Command.liftTermElabM <| do
        binderTypes.mapM fun (bname, btStx) => do
          let typeExpr ← Lean.Elab.Term.elabType btStx
          let si ← Build.buildSortInfo typeExpr
          return (bname.toString, si)
      let goalTypeStr := type.raw.reprint.getD "<unknown-goal>"
      let script := Unravel.translate
        (defaultSimpPred := st.goalHeadName)
        (goalType := goalTypeStr)
        (thmName := name.getId.toString)
        (varSorts := varSorts)
        tree
      Lean.logInfoAt name m!"[cyclic_thm {name.getId}] Unravel-emitted script:\n{script}"
      match Lean.Parser.runParserCategory envWithRecursive `command script with
      | .ok cmdStx =>
        -- Roll back env to before the recursive form, then try
        -- Unravel. Snapshot message log so we can restore on failure.
        Lean.setEnv envBefore
        let beforeMsgs := (← getThe Lean.Elab.Command.State).messages
        try Lean.Elab.Command.elabCommand cmdStx catch _ => pure ()
        let envAfter ← Lean.getEnv
        let hasGoodValue : Bool :=
          match envAfter.find? name.getId with
          | some di =>
            match di.value? with
            | some v => !v.hasSorry
            | none   => true
          | none    => false
        if hasGoodValue then
          Lean.logInfoAt name m!"[cyclic_thm {name.getId}] canonical form: Unravel emission ✓"
        else
          -- Restore env-with-recursive (Unravel produced sorries) and
          -- drop any messages from the failed canonical attempt.
          Lean.setEnv envWithRecursive
          modifyThe Lean.Elab.Command.State fun s => { s with messages := beforeMsgs }
          Lean.logWarningAt name m!"[cyclic_thm {name.getId}] Unravel emission produced sorries; keeping recursive form as `{name.getId}`."
      | .error msg =>
        Lean.logWarningAt name m!"[cyclic_thm {name.getId}] Unravel script parse failed ({msg}); keeping recursive form."
    setCurrentThm none
  | _ => Lean.throwError "cyclic_thm: malformed syntax"

/-! ### `cyc_state` debug tactic

Walks the event stream and renders it as an indented tree where each
`caseSplitStart`/`armStart` increases indent and the matching `End`
events decrease it. This mirrors the (Phase-B) tree shape that the
finalizer will reconstruct. -/

syntax (name := cycStateTac) "cyc_state" : tactic

@[tactic cycStateTac]
def evalCycState : Tactic := fun _ => do
  let st ← getCyclicState
  let companionsStr := String.intercalate ", " (st.companions.map fun (l, _) => l)
  -- Render events with running indent.
  let mut indent : Nat := 0
  let mut lines : List String := []
  for e in st.events.reverse do
    let pad := String.ofList (List.replicate (indent * 2) ' ')
    match e with
    | .companion l _ =>
      lines := lines ++ [s!"{pad}companion {l}"]
    | .caseSplitStart v _ arms =>
      let armNames := arms.map (·.ctor.toString)
      lines := lines ++ [s!"{pad}cases {v} (arms: {String.intercalate ", " armNames})"]
      indent := indent + 1
    | .caseSplitEnd =>
      indent := indent - 1
    | .back anc _ σ pos _ =>
      let σStr := if σ.isEmpty then "" else
        " {" ++ String.intercalate ", " (σ.map fun (v, _) => s!"{v} := …") ++ "}"
      lines := lines ++ [s!"{pad}back@{pos} R={anc}{σStr}"]
  let body := if lines.isEmpty then "  (no events)" else String.intercalate "\n" lines
  logInfo m!"[cyc_state] companions = [{companionsStr}]\n{body}"

/-! ### `cyclic_mutual ... end` — mutual cyclic theorems

Closes the mutual / cross-predicate cyclic-proof gap (the README's
flagged biggest limitation). Lets the user write a *coupled* cyclic
proof — multiple companions, back-edges that cross from one
companion to another — typeset as a single `cyclic_mutual` block.

Surface form:
```
cyclic_mutual
  thm name₁ (binders) : type₁ by
    cyclic R₁
    … back R_j {σ}     -- may target any companion in the block
  thm name₂ (binders) : type₂ by
    cyclic R₂
    …
end
```

Soundness: the synthesised body desugars to a `mutual def … end`
block, so Lean's mutual-recursion termination check provides the
soundness guarantee (cross-call structural descent). MVP: SCT
validation across mutual companions is *not* run yet — Lean's
termination check is authoritative for now. Adding mutual SCT is
local follow-up work (per-theorem trace extraction → a single
multi-graph `checkMultiSCT` over (theorem, position) vertices).

`back R {σ}` resolves R via the mutual companion table, then issues
`exact <R's-thm-name> args-mapped-from-σ-to-that-thm's-binders`.
The hidden `_set_active` tactic, prepended to each body, switches
`currentThmRef` so events fire under the right ownership. -/

syntax (name := setActiveTac) "_set_active " ident : tactic

@[tactic setActiveTac]
def evalSetActive : Tactic := fun stx => do
  match stx with
  | `(tactic| _set_active $name:ident) =>
    let ctxs ← getMutualThmCtxs
    match ctxs.find? (·.thmName == name.getId) with
    | some ctx => setCurrentThm (some ctx)
    | none =>
      throwError s!"_set_active: no theorem '{name.getId}' in current \
        mutual block (available: {ctxs.map (·.thmName.toString)})"
  | _ => throwUnsupportedSyntax

syntax (name := cyclicMutualCmd)
  "cyclic_mutual"
    ("thm " ident cycThmBinder+ " : " term " by " Lean.Parser.Tactic.tacticSeq)+
  "end_mutual"
  : command

@[command_elab cyclicMutualCmd]
def elabCyclicMutual : Lean.Elab.Command.CommandElab := fun stx => do
  -- Pull the (name, binders, type, tacs) for each `thm` entry. The
  -- `+` repetition packs them in parallel argument arrays at fixed
  -- offsets in the syntax tree.
  let nameStxs   : Array Lean.Syntax := stx[1].getArgs.map (·[1])
  let binderStxs : Array Lean.Syntax := stx[1].getArgs.map (·[2])
  let typeStxs   : Array Lean.Syntax := stx[1].getArgs.map (·[4])
  let tacsStxs   : Array Lean.Syntax := stx[1].getArgs.map (·[6])
  let entryCount := nameStxs.size
  if entryCount < 2 then
    Lean.throwError "cyclic_mutual: needs at least two `thm` entries; \
      use `cyclic_thm` for a single theorem."
  -- Collect ThmContexts + reconstruct standard bracketed-binder syntax
  -- per entry.
  let mut thmCtxs : List ThmContext := []
  let mut entries :
      Array (Lean.Ident × Array (Lean.TSyntax `Lean.Parser.Term.bracketedBinder)
             × Lean.TSyntax `term × Lean.TSyntax `Lean.Parser.Tactic.tacticSeq) := #[]
  for i in [0:entryCount] do
    let nameStx : Lean.Ident := ⟨nameStxs[i]!⟩
    let typeStx : Lean.TSyntax `term := ⟨typeStxs[i]!⟩
    let tacsStx : Lean.TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨tacsStxs[i]!⟩
    let binderArr := binderStxs[i]!.getArgs
    let mut flatBinderNames : List Lean.Name := []
    let mut bracketedBinders :
        Array (Lean.TSyntax `Lean.Parser.Term.bracketedBinder) := #[]
    for b in binderArr do
      match b with
      | `(cycThmBinder| ($vs:ident* : $bt:term)) =>
        for v in vs do flatBinderNames := flatBinderNames ++ [v.getId]
        let bb ← `(Lean.Parser.Term.bracketedBinderF| ($vs* : $bt))
        bracketedBinders := bracketedBinders.push bb
      | _ => Lean.throwErrorAt b "cyclic_mutual: malformed binder"
    thmCtxs := thmCtxs ++
      [{ thmName := nameStx.getId, binders := flatBinderNames }]
    entries := entries.push (nameStx, bracketedBinders, typeStx, tacsStx)
  -- Reset state and register all ThmContexts so `cyclic R` can
  -- self-resolve via `getDeclName?`.
  resetCyclicState
  resetMutualState
  setMutualThmCtxs thmCtxs
  -- Pre-register every companion → target mapping by syntactically
  -- scanning each entry's tactic source for `cyclic <label>` calls.
  -- Without this, a back-edge in entry 0 that targets entry 1's
  -- companion would fail because entry 1's body hasn't elaborated
  -- yet — companions only get registered when `cyclic <label>`
  -- actually runs. Pre-registration is safe because the (label →
  -- ThmContext) mapping is fully determined by syntax.
  let rec findCyclicLabels (stx : Lean.Syntax) : List String :=
    match stx with
    | .node _ kind args =>
      let here : List String :=
        if kind == ``cyclicTac then
          match args[1]? with
          | some idStx =>
            match idStx with
            | .ident _ _ n _ => [n.toString]
            | _ => []
          | none => []
        else []
      args.foldl (init := here) fun acc c => acc ++ findCyclicLabels c
    | _ => []
  for i in [0:entryCount] do
    let (_, _, _, tacsStx) := entries[i]!
    let labels := findCyclicLabels tacsStx.raw
    let ctx := thmCtxs[i]!
    for lbl in labels do
      addMutualCompanion lbl ctx
  -- Synthesise the mutual block as a raw string and reparse via the
  -- command parser. The `cyclic R` tactic self-identifies its enclosing
  -- theorem via `getDeclName?` (looked up against `mutualThmCtxsRef`),
  -- so no per-entry preamble injection is needed. The only subtlety:
  -- `Syntax.reprint` strips the leading whitespace of the *first* line
  -- of `tacsStr` but preserves it on subsequent lines, so siblings
  -- end up at different columns and Lean's indented-tacticSeq parser
  -- rejects them. `normalizeIndent` re-aligns them to a uniform
  -- column under the `by` block.
  let countLeading : String → Nat := fun s => Id.run do
    let mut n : Nat := 0
    for c in s.toList do
      if c == ' ' then n := n + 1 else break
    return n
  let normalizeIndent : String → String → String := fun src indentBy =>
    let lines := src.splitOn "\n"
    let later := lines.drop 1
    let nonEmpty := later.filter (fun l => l.any (· != ' ') && !l.isEmpty)
    let baseIndent : Nat :=
      if nonEmpty.isEmpty then 0
      else nonEmpty.foldl (fun m l => Nat.min m (countLeading l)) 1000
    let processOne : String → String := fun l =>
      let l' := if countLeading l ≥ baseIndent then l.drop baseIndent else l
      if l'.isEmpty || l'.all (· == ' ') then "" else indentBy ++ l'
    String.intercalate "\n" (lines.map processOne)
  let mut entryTexts : Array String := #[]
  for i in [0:entryCount] do
    let (nameStx, bracketedBinders, typeStx, tacsStx) := entries[i]!
    let nameStr := nameStx.getId.toString
    let bindersStr := String.intercalate " "
      (bracketedBinders.toList.map fun b => (b.raw.reprint).getD "")
    let typeStr := (typeStx.raw.reprint).getD "<reprint-failed>"
    let tacsStrRaw := (tacsStx.raw.reprint).getD "<reprint-failed>"
    let tacsStr := normalizeIndent tacsStrRaw "  "
    entryTexts := entryTexts.push
      s!"def {nameStr} {bindersStr} : {typeStr} := by\n{tacsStr}"
  let mutStr := "mutual\n" ++ String.intercalate "\n" entryTexts.toList ++ "\nend"
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command mutStr with
  | .ok cmdStx => Lean.Elab.Command.elabCommand cmdStx
  | .error msg =>
    Lean.throwError s!"cyclic_mutual: failed to parse synthesised mutual \
      block:\n{msg}\n\nblock was:\n{mutStr}"
  -- Per-theorem event diagnostics. The single event log holds events
  -- from all entries interleaved by elaboration order; render the
  -- whole stream so the user can see the recorded structure.
  let st ← getCyclicState
  let compStr := String.intercalate ", " (st.companions.map (·.1))
  let mutCompStr ← do
    let m ← mutualCompanionTargetRef.get
    pure <| String.intercalate ", "
      (m.map fun (l, c) => s!"{l}→{c.thmName}")
  Lean.logInfoAt nameStxs[0]!
    m!"[cyclic_mutual] entries: {thmCtxs.map (·.thmName.toString)}\n\
       companions in scope: [{compStr}]\n\
       companion → target: [{mutCompStr}]\n\
       events recorded: {st.events.length}"
  -- Done — clean up.
  setCurrentThm none
  resetMutualState

end CyclicTactic
