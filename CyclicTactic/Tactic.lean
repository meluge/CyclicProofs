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
    cyclicStateRef.set {
      companions := [(labelStr, seq)]
      events := [.companion labelStr seq]
      goalHeadName := goalHeadName
    }
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
      let some (_, _companionSeq) := st.companions.find? (·.1 == labelStr)
        | throwError s!"back: no companion '{labelStr}' in scope. \
            Available: {st.companions.map (·.1)}"
      -- Parse σ as raw (var, Expr) pairs.
      let σExprs : List (String × Lean.Expr) ← match σStx? with
        | none     => pure []
        | some stx => parseSubstExprs stx
      -- Look up the enclosing theorem context.
      let some thmCtx ← getCurrentThm
        | throwError "back: not inside a `cyclic_thm` command. \
            Use `cyclic_thm` instead of `theorem` to enable back-edges."
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

end CyclicTactic
