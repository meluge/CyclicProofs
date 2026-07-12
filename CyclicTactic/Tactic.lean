import Lean
import CyclicTactic.ProofTree
import CyclicTactic.SizeChange
import CyclicTactic.Phase
import CyclicTactic.InductionOrder
import CyclicTactic.PaperAnnotation
import CyclicTactic.Theorem6
import CyclicTactic.WFEmit
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
    -- `btPred t n`) so the §6 emitter can use it as the
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
      -- Record the back-edge event FIRST, BEFORE issuing the recursive
      -- call. The user's raw recursive scaffold may NOT type-check (e.g.
      -- merge_length's `+1` arithmetic gap, where `exact merge_length …`
      -- fails because the post-`simp` goal differs by `+1`s the hand proof
      -- never closes). The scaffold exists ONLY to fire events for SCT +
      -- emission — the committed declaration comes from the §6/WF emitter,
      -- not the scaffold. Recording before the (possibly-throwing) `exact`
      -- guarantees the cycle stays visible so the dispatcher can choose WF.
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
      pushEvent (.back labelStr bSeq σData pos sourceText.trimAscii.toString)
      -- Issue the recursive call; if it doesn't type-check (scaffold-only
      -- shape) fall back to `sorry` so the enclosing tactic block / `·`
      -- bullet still completes and the command reaches its emission phase.
      let recCall := Lean.mkAppN (Lean.mkConst thmCtx.thmName) argExprs
      let recCallStx ← Lean.PrettyPrinter.delab recCall
      Lean.Elab.Tactic.evalTactic
        (← `(tactic| first | exact $recCallStx | sorry))
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
      -- Capture the body's source text for the §6 emitter. Used as
      -- the leaf's closeTactic when the arm has no back-edge, or as
      -- the prelude (with the back call's text replaced by `recurse`)
      -- when the arm has one. `Syntax.reprint` reconstructs the source.
      -- The reprint sometimes includes the leading `=>` separator
      -- because the parser combines it with the body; strip it.
      let bodyTextRaw : String := (bodyArea.reprint).getD ""
      let trimmed : String := bodyTextRaw.trimAscii.toString
      let bodyText : String :=
        if trimmed.startsWith "=>" then (trimmed.drop 2).trimAscii.toString
        else trimmed
      { ctor := ctor, binders := binders, range := range, bodyText := bodyText }
    pushEvent (.caseSplitStart varName seq armInfos)
    -- Delegate arm-body elaboration to Lean's standard cases.
    Lean.Elab.Tactic.evalTactic
      (← `(tactic| cases $var:ident with $arms:inductionAlt*))
    pushEvent .caseSplitEnd
  | _ => throwUnsupportedSyntax

/-! ### `cyc_by_cases <h> : <prop> with | pos => … | neg => …` (Phase 2)

`merge`-style recursion lives inside an `if x ≤ y` — a *Decidable*
split. The user's proof branches with `by_cases hle : x ≤ y` and puts a
`back R {…}` in each arm, descending on a DIFFERENT argument per arm
(xs when `x ≤ y`, ys otherwise). Lean's plain `by_cases` is opaque to
the event recorder, so those back-edges never fire as events and the
cycle is invisible (no SCG ⇒ no measure to synthesise).

`cyc_by_cases` makes the split visible: it records a `.dCaseSplitStart`
(building a `.dCaseSplit` ProofTree node) carrying the two arm source
ranges + body text, then runs Lean's `by_cases h : P` and elaborates
each arm so its inner `back R` fires normally, attributed to the arm by
source position. Because a decidable split refines NO root-sequent
variable, trace extraction descends into both arms with the path
substitution unchanged — surfacing each arm's own size-change graph
(xs-descent vs ys-descent), which the WF backend turns into a lex/sum
measure. The `| pos`/`| neg` arms map to `by_cases`'s goal order
[h : P, h : ¬P]. -/

syntax (name := cycByCasesTac)
  "cyc_by_cases " ident " : " term " with "
    (Lean.Parser.Tactic.inductionAlt)+ : tactic

@[tactic cycByCasesTac]
def evalCycByCases : Tactic := fun stx => do
  match stx with
  | `(tactic| cyc_by_cases $h:ident : $prop:term with $arms:inductionAlt*) =>
    let hName := h.getId.toString
    let goal ← getMainGoal
    let target ← goal.getType
    let seq : Sequent ← match ← getCurrentThm with
      | some ctx =>
        let args : List SubjectTerm := ctx.binders.map fun b => .var b.toString
        pure (Sequent.succ1 { pred := ctx.thmName.toString, args := args })
      | none =>
        Build.exprToSequent target
    let propStr : String := (prop.raw.reprint).getD "<prop>"
    if arms.size != 2 then
      throwError "cyc_by_cases: expected exactly two arms (positive `| pos => …` \
        then negative `| neg => …`); got {arms.size}"
    -- Extract each arm's body source range + text. The arm label (`pos`/
    -- `neg`) is only for readability — attribution is positional: first
    -- arm = `h : P`, second = `h : ¬P`, matching `by_cases` goal order.
    let armData : Array (SourceRange × String × Lean.TSyntax `Lean.Parser.Tactic.tacticSeq) :=
      arms.map fun arm =>
        let bodyArea := arm.raw[1]
        let range : SourceRange :=
          match bodyArea.getRange? with
          | some r => { startPos := r.start.byteIdx, endPos := r.stop.byteIdx }
          | none   => { startPos := 0, endPos := 0 }
        let bodyTextRaw : String := (bodyArea.reprint).getD ""
        let trimmed : String := bodyTextRaw.trimAscii.toString
        let bodyText : String :=
          if trimmed.startsWith "=>" then (trimmed.drop 2).trimAscii.toString
          else trimmed
        -- The arm body's tacticSeq is the last child of the body area.
        let bodySeq : Lean.TSyntax `Lean.Parser.Tactic.tacticSeq := ⟨bodyArea[bodyArea.getNumArgs - 1]⟩
        (range, bodyText, bodySeq)
    let (posRange, posBody, posSeq) := armData[0]!
    let (negRange, negBody, negSeq) := armData[1]!
    pushEvent (.dCaseSplitStart hName propStr seq posRange negRange posBody negBody)
    -- Run the decidable split, then elaborate each arm's body in its
    -- subgoal so the `back R {…}` calls inside fire as events. `by_cases`
    -- leaves goals in order [h : P, h : ¬P], matching pos-then-neg.
    Lean.Elab.Tactic.evalTactic (← `(tactic| by_cases $h:ident : $prop:term))
    -- Elaborate each arm in its own `·`-focused subgoal so the inner
    -- `back R {…}` fires as an event. Wrap in `(try …)`/`all_goals sorry`
    -- so a scaffold arm that doesn't fully close still lets the command
    -- finish and reach the post-elaboration emission phase.
    Lean.Elab.Tactic.evalTactic (← `(tactic| · (try ($posSeq:tacticSeq)); all_goals sorry))
    Lean.Elab.Tactic.evalTactic (← `(tactic| · (try ($negSeq:tacticSeq)); all_goals sorry))
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

/-- Dispatcher predicate: can the §6 STRUCTURAL emitter succeed?

The §6 emitter (`Theorem6.Emit.translate`) emits `induction <var>
generalizing …` and binds one IH per recursive subterm — it can only
express recursion that descends on a SINGLE fixed argument position
(Wehr's lex induction order specialised to one variable). That order is
exactly what `InductionOrder.findInductionOrder` constructs from the
bud-companion SCC graph: `some asg` iff every strongly-connected bud
component has a position preserved along every cycle and progressing on
at least one.

So structural emission can succeed iff `findInductionOrder` returns an
order whose deduplicated position set has size ≤ 1 (one variable carries
the whole induction). When it is `none`, or uses ≥ 2 distinct positions,
no single `induction` witnesses termination and we fall back to the WF
backend with a synthesised lex/sum measure.

merge-sort's `merge` fails this: the `x ≤ y` arm descends on `xs`
(position 0), the `x > y` arm on `ys` (position 1); no single position is
preserved-and-progressing across BOTH arms, so `findInductionOrder`
returns `none` ⇒ `canStructural = false` ⇒ WF. This predicate is the
dispatcher's load-bearing criterion. -/
def canStructural
    (tree : Proof.ProofTree)
    (labeled : List (String × SCGraph))
    (arity : Nat) : Bool :=
  match InductionOrder.findInductionOrder tree labeled arity with
  | none     => false
  | some asg => (InductionOrder.lexOrderFromAssignment asg).length ≤ 1

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
    -- cyclic events from the firing tactics). If the §6 emission
    -- subsequently elaborates cleanly, we ROLL BACK env to before the
    -- recursive elaboration and replace `<name>` with the canonical
    -- Theorem 6.1 form. If that fails, the recursive form stands as
    -- the fallback. Either way: one name, one declaration.
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
    -- Snapshot the message log BEFORE the recursive scaffold elaborates.
    -- The scaffold (the user's raw `back`-based proof) may itself fail to
    -- type-check — e.g. merge_length's `+1` arithmetic gap that the hand
    -- proof never closes. It exists only to FIRE EVENTS for SCT +
    -- emission, not as the user-facing decl. When canonical emission
    -- (structural or WF) succeeds we drop the scaffold's diagnostics so
    -- the build is clean; on fallback we keep them (the recursive form IS
    -- the committed decl then, so its errors are real).
    let msgsBeforeScaffold := (← getThe Lean.Elab.Command.State).messages
    -- Elaborate the scaffold with `Elab.async` forced OFF (set in the monad,
    -- NOT via a `set_option … in` syntax wrapper — that wrapper re-dispatches
    -- the command and runs the whole elaborator twice). A tactic-body `def` is
    -- otherwise elaborated on a background task, so its `declaration uses
    -- 'sorry'` warning (from the scaffold's `back … | sorry`) is posted to the
    -- message log AFTER `tryCommit` resets messages to `msgsBeforeScaffold` —
    -- leaking a spurious sorry warning onto the otherwise kernel-clean WF /
    -- structural decl. Synchronous elaboration lands the warning before the
    -- reset, so the "drop scaffold diagnostics on success" logic removes it.
    Lean.Elab.Command.withScope (fun sc => { sc with opts := sc.opts.setBool `Elab.async false }) do
      Lean.Elab.Command.elabCommand
        (← `(def $name:ident $bracketedBinders* : $type:term := by $tacs:tacticSeq))
    -- Phase B: build a ProofTree from recorded events.
    let st ← getCyclicState
    let events := st.events.reverse
    let tree := Build.eventsToTree events
    -- Phase C: run SCT validation (extractTraceSCGsLabeled →
    -- checkMultiSCT → findInductionOrder Wehr 3.2.4) on the tree.
    let labeled := Proof.extractTraceSCGsLabeled tree
    -- PHASE AUGMENTATION (GAP 2): patch the per-back-edge SCGs with a strict
    -- self-loop at any finite-domain (Bool/enum) "phase" position whose
    -- required descent order is consistent (see `Proof.phaseAugment`). This
    -- must happen BEFORE `checkMultiSCT`/`findInductionOrder`, since a
    -- phase-only two-step proof (e.g. `f_total`) otherwise fails the SCT gate
    -- and is filtered out before emission. On a corpus with no phase structure
    -- `phaseAugment` returns the graphs unchanged and `ranks = []`, so SCT,
    -- the induction order, and emission are all byte-identical to before — no
    -- regression. The kernel still re-checks the emitted measure, so the
    -- augmentation is sound by construction (an over-eager patch is rejected,
    -- never accepted as a wrong proof). `phaseRanks` flows to WFEmit below.
    let phaseTrans := Proof.extractPhaseTrans tree
    let pa := Proof.phaseAugment labeled phaseTrans
    let labeledRaw := labeled
    let labeled := labeled.zip pa.graphs |>.map (fun ((l, _), g) => (l, g))
    let phaseRanks := pa.ranks
    let graphs := pa.graphs
    let rootSeq := tree.sequent
    let arity : Nat :=
      let ns := rootSeq.antecedents.map (·.args.length) ++
                rootSeq.succedents.map (·.args.length)
      ns.foldl (· + ·) 0
    let sctOk := SCGraph.checkMultiSCT graphs
    -- Induction order / `canStructural` use the RAW (un-augmented) graphs: a
    -- phase self-loop must NOT make a proof look structurally-recursive and get
    -- routed to the §6 structural emitter (which can't render a phase rank).
    -- Phase augmentation only ever ADDS WF-emittable proofs, never reroutes.
    let order := InductionOrder.findInductionOrder tree labeledRaw arity
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
    -- Paper-faithful (Grotenhuis-Otten Def 5.1) verification: compute
    -- the Stack/Name/Reset annotation and check Theorem 5.2 on this
    -- specific tree. When some back-edge fails, surface the report so
    -- the user knows why the paper-faithful path didn't fire — typical
    -- causes are name/stack mismatches between sprout and bud, or no
    -- qualifying progressing name in `Reset(bud) ∩ preserved`.
    let paperBuds := CyclicTactic.PaperAnnotation.annotateTree tree
    let checks := paperBuds.map CyclicTactic.PaperAnnotation.checkTheorem52
    let paperMsg : String :=
      match CyclicTactic.PaperAnnotation.renderChecks checks with
      | none     => "paper-faithful (Thm 5.2): PASS ✓"
      | some msg => "paper-faithful (Thm 5.2): FAIL ✗\n" ++ msg
    -- §6 augmented per-node info (RelAnc / Ineq / Hyp / cov). Diagnostic
    -- only — the Theorem 6.1 emission itself is not yet wired in.
    let augMap := CyclicTactic.Theorem6.computeAug tree
    let augMsg := CyclicTactic.Theorem6.renderAug augMap
    Lean.logInfoAt name m!"[cyclic_thm {name.getId}] SCT: {sctMsg}\n{orderMsg}\n{paperMsg}\nback-edge SCGs:\n{graphsStr}\n\nProofTree:\n{Build.renderTree tree}\n\n§6 per-node info (RelAnc/Ineq/Hyp):\n{augMsg}"
    -- Snapshot env-with-recursive so we can restore the recursive
    -- form if canonical emission fails.
    let envWithRecursive ← Lean.getEnv
    -- Message log INCLUDING the scaffold's diagnostics — restored if
    -- canonical emission fails and the recursive form becomes the decl.
    let msgsAfterScaffold := (← getThe Lean.Elab.Command.State).messages
    -- Phase E: try canonical emission (structural §6 or WF). On success,
    -- roll back env to BEFORE the recursive elaboration and commit the
    -- emitted script as <name>. On failure, restore envWithRecursive so
    -- the recursive form stands as the user-facing declaration.
    if sctOk then
      -- Read binder types from the already-elaborated recursive def's
      -- signature. This handles dependent binders (`(h : P x)`)
      -- correctly — re-elabbing each binder syntax independently would
      -- fail since `x` isn't in scope outside the def's context.
      let varSorts ← Lean.Elab.Command.liftTermElabM <| do
        let env ← Lean.getEnv
        match env.find? name.getId with
        | some di =>
          Lean.Meta.forallTelescope di.type fun fvars _ => do
            let mut acc : List (String × EmitCommon.SortInfo) := []
            for fv in fvars do
              let decl ← fv.fvarId!.getDecl
              let si ← Build.buildSortInfo decl.type
              acc := acc ++ [(decl.userName.toString, si)]
            return acc
        | none =>
          -- Defensive fallback: the recursive def wasn't found in the
          -- env (shouldn't happen post-elabCommand). Fall back to the
          -- old per-binder elab, which fails for dependent types but
          -- works for the common non-dependent case.
          binderTypes.mapM fun (bname, btStx) => do
            let typeExpr ← Lean.Elab.Term.elabType btStx
            let si ← Build.buildSortInfo typeExpr
            return (bname.toString, si)
      let goalTypeStr := type.raw.reprint.getD "<unknown-goal>"
      -- Dispatcher (Phase 3): choose the STRUCTURAL §6 emitter when a
      -- single induction variable witnesses termination, else the WF
      -- backend with a synthesised lex/sum measure. The decision is
      -- computed from the §6/SCT data BEFORE attempting emission. Each
      -- branch logs a textually-DISTINCT marker (chosen / committed ✓ /
      -- FALLBACK) so a fresh compile proves which path produced <name> —
      -- a green build alone is NOT proof of WF emission.
      let useStructural := canStructural tree labeledRaw arity
      -- Shared committer: parse `script`, roll env back to `envBefore`,
      -- drop the scaffold's diagnostics, elaborate, and report whether a
      -- sorry-free value was committed (restoring the recursive form +
      -- its diagnostics on failure).
      -- The committed `def`/`theorem` is added under the CURRENT namespace
      -- (e.g. inside `namespace MergeSort`, `merge_length` becomes
      -- `MergeSort.merge_length`). Resolve the qualified name so the
      -- success-check below finds it — looking up the bare `name.getId`
      -- silently misses namespaced decls and wrongly triggers FALLBACK.
      let currNs := (← Lean.Elab.Command.getScope).currNamespace
      let qualName := currNs ++ name.getId
      let tryCommit : String → Lean.Elab.Command.CommandElabM Bool := fun script => do
        match Lean.Parser.runParserCategory envWithRecursive `command script with
        | .ok cmdStx =>
          Lean.setEnv envBefore
          modifyThe Lean.Elab.Command.State fun s => { s with messages := msgsBeforeScaffold }
          try Lean.Elab.Command.elabCommand cmdStx catch _ => pure ()
          let envAfter ← Lean.getEnv
          let hasGoodValue : Bool :=
            match envAfter.find? qualName <|> envAfter.find? name.getId with
            | some di =>
              match di.value? with
              | some v => !v.hasSorry
              | none   => true
            | none    => false
          if hasGoodValue then
            return true
          else
            Lean.setEnv envWithRecursive
            modifyThe Lean.Elab.Command.State fun s => { s with messages := msgsAfterScaffold }
            return false
        | .error msg =>
          Lean.logWarningAt name m!"[cyclic_thm {name.getId}] emitted script parse failed ({msg})."
          return false
      if useStructural then
        Lean.logInfoAt name m!"[cyclic_thm {name.getId}] dispatcher chose structural: single-variable induction order suffices."
        let script := CyclicTactic.Theorem6.Emit.translate
          (defaultSimpPred := st.goalHeadName)
          (goalType := goalTypeStr)
          (thmName := name.getId.toString)
          (varSorts := varSorts)
          tree
        Lean.logInfoAt name m!"[cyclic_thm {name.getId}] Theorem 6.1 emitted script:\n{script}"
        if ← tryCommit script then
          -- NB: re-state the chosen strategy HERE, not only before `tryCommit`
          -- — `tryCommit` resets the message log on success, which would
          -- otherwise drop the "dispatcher chose …" line. The per-decision
          -- rationale is the paper's evidence base, so it must survive a
          -- SUCCESSFUL emission, not just a fallback.
          Lean.logInfoAt name m!"[cyclic_thm {name.getId}] canonical form: Theorem 6.1 (structural) emission ✓ [dispatcher chose structural: single-variable induction order]"
        else
          Lean.logWarningAt name m!"[cyclic_thm {name.getId}] structural emission failed; keeping recursive form (FALLBACK)."
      else
        -- WF path: synthesise a lex/sum measure from the per-back-edge
        -- size-change graphs and emit `termination_by <measure> decreasing_by`
        -- with a measure-typed `decreasing_by` (see WFEmit.decreasingByFor).
        --
        -- Emission ladder (each rung strictly more permissive; the explicit
        -- synthesised measure stays the VISIBLE artifact when it works, so
        -- nothing hides the SCT→measure contribution):
        --   1. `synthMeasure` → emit `def … termination_by <measure>`.
        --   2. on failure, emit the SAME body with NO clause and let Lean's
        --      own structural/GuessLex inference find a measure (catches e.g.
        --      `merge_length`, which Lean infers unaided).
        --   3. on failure, keep the user's recursive form (existing fallback).
        -- `gs` (phase-augmented SCGs) and `phaseRanks` were computed up top
        -- (Phase C) so SCT, the induction order, and emission all agree.
        let gs := graphs
        -- Body-only script for rung 2 — shared by both the `some` and `none`
        -- measure cases.
        let inferScript := CyclicTactic.WFEmit.translateNoMeasure
          (defaultSimpPred := st.goalHeadName)
          (goalType := goalTypeStr)
          (thmName := name.getId.toString)
          (varSorts := varSorts)
          tree
        let tryInferThenFallback : String → Lean.Elab.Command.CommandElabM Unit :=
          fun reason => do
            if ← tryCommit inferScript then
              Lean.logInfoAt name m!"[cyclic_thm {name.getId}] canonical form: WF emission ✓ (Lean-inferred measure); dispatcher chose WF: {reason}"
            else
              Lean.logWarningAt name m!"[cyclic_thm {name.getId}] WF emission failed (synthesised measure AND Lean inference); keeping recursive form (FALLBACK)."
        match synthMeasure gs arity with
        | some measure =>
          let phaseNote := if phaseRanks.isEmpty then "" else s!" [phase-augmented: {phaseRanks.length} finite-domain position(s)]"
          Lean.logInfoAt name m!"[cyclic_thm {name.getId}] dispatcher chose WF: findInductionOrder has no single-variable order; measure = {measure}{phaseNote}"
          let script := CyclicTactic.WFEmit.translate
            (defaultSimpPred := st.goalHeadName)
            (goalType := goalTypeStr)
            (thmName := name.getId.toString)
            (varSorts := varSorts)
            (measure := measure)
            tree
            (phaseRanks := phaseRanks)
          Lean.logInfoAt name m!"[cyclic_thm {name.getId}] WF emitted script:\n{script}"
          if ← tryCommit script then
            -- Re-state the measure HERE: `tryCommit` resets the message log on
            -- success, dropping the "dispatcher chose WF …" line above. The
            -- synthesised measure is the paper's evidence base, so it must
            -- survive a successful emission. (`measure` prints as e.g.
            -- `lex (a0, a1)` or `sum 2`.)
            let phaseNote := if phaseRanks.isEmpty then "" else s!"; phase-augmented ({phaseRanks.length} finite-domain pos)"
            Lean.logInfoAt name m!"[cyclic_thm {name.getId}] canonical form: WF emission ✓ (termination_by); dispatcher chose WF: no single-variable induction order; measure = {measure}{phaseNote}"
          else
            tryInferThenFallback s!"synthesised measure {measure} did not discharge; tried Lean inference"
        | none =>
          tryInferThenFallback "no synthesisable lex/sum measure; tried Lean inference"
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
    | .dCaseSplitStart h p _ _ _ _ _ =>
      lines := lines ++ [s!"{pad}by_cases {h} : {p}"]
      indent := indent + 1
    | .dCaseArmSep =>
      -- Separator between the pos/neg arms of a recorded `by_cases`.
      lines := lines ++ [s!"{pad}·"]
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

/-- Demultiplex a chronologically-ordered event stream from a
    `cyclic_mutual` block into per-entry segments. Uses the
    companion → ThmContext table to attribute each `.companion lbl _`
    event to a specific theorem; the next `.companion` that targets a
    different theorem starts a new segment.

    Entries appear in the order their first companion is registered
    (which matches source order: entry 1's `cyclic R_1` fires before
    entry 2's `cyclic R_2`). Events preceding the first companion are
    dropped (defensive — shouldn't happen for well-formed input). -/
def demuxMutualEvents
    (events : List CyclicEvent)
    (companionTargets : List (String × ThmContext))
    : List (Lean.Name × List CyclicEvent) := Id.run do
  let mut result : List (Lean.Name × List CyclicEvent) := []
  let mut currentThm : Option Lean.Name := none
  let mut currentEvents : List CyclicEvent := []
  for e in events do
    match e with
    | .companion lbl _ =>
      let target? := companionTargets.find? (·.1 == lbl)
      match target? with
      | some (_, ctx) =>
        let sameThm := match currentThm with
          | some t => t == ctx.thmName
          | none   => false
        if sameThm then
          currentEvents := currentEvents ++ [e]
        else
          if let some prevThm := currentThm then
            result := result ++ [(prevThm, currentEvents)]
          currentThm := some ctx.thmName
          currentEvents := [e]
      | none =>
        if currentThm.isSome then
          currentEvents := currentEvents ++ [e]
    | _ =>
      if currentThm.isSome then
        currentEvents := currentEvents ++ [e]
  if let some prevThm := currentThm then
    result := result ++ [(prevThm, currentEvents)]
  return result

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
  -- Snapshot env *before* the recursive mutual elaborates, so we can
  -- roll back and re-elaborate as the §6-canonical form if it
  -- elaborates cleanly. Mirrors the single `cyclic_thm` flow.
  let envBefore ← Lean.getEnv
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command mutStr with
  | .ok cmdStx => Lean.Elab.Command.elabCommand cmdStx
  | .error msg =>
    Lean.throwError s!"cyclic_mutual: failed to parse synthesised mutual \
      block:\n{msg}\n\nblock was:\n{mutStr}"
  -- Env after recursive mutual: kept as fallback if §6 emission fails.
  let envWithRecursive ← Lean.getEnv
  -- Per-theorem event diagnostics. The single event log holds events
  -- from all entries interleaved by elaboration order; render the
  -- whole stream so the user can see the recorded structure.
  let st ← getCyclicState
  let compStr := String.intercalate ", " (st.companions.map (·.1))
  let companionTargets ← mutualCompanionTargetRef.get
  let mutCompStr := String.intercalate ", "
    (companionTargets.map fun (l, c) => s!"{l}→{c.thmName}")
  Lean.logInfoAt nameStxs[0]!
    m!"[cyclic_mutual] entries: {thmCtxs.map (·.thmName.toString)}\n\
       companions in scope: [{compStr}]\n\
       companion → target: [{mutCompStr}]\n\
       events recorded: {st.events.length}"
  -- Demux events by entry and surface the per-entry ProofTree as a
  -- diagnostic. §6 augmentation (computeAug / annotateTree) hangs on
  -- mutual trees when buds reference out-of-tree ancestors — the
  -- Lemma 5.9 unfolding fixpoint never converges for cross-theorem
  -- cycles. Mutual emission doesn't need aug data anyway, since all
  -- buds emit as `exact <sibling-thm-name> <σ-applied args>` (the
  -- sibling theorem is the IH provided by Lean's mutual termination
  -- check). See step-3 mutual emitter for the routing.
  let chronoEvents := st.events.reverse
  let perEntry := demuxMutualEvents chronoEvents companionTargets
  -- First pass: build per-entry diagnostic + collect entries for the
  -- §6 mutual emitter.
  let mut mutualEntries : List CyclicTactic.Theorem6.Emit.MutualEntry := []
  for (thmName, evs) in perEntry do
    let tree := Build.eventsToTree evs
    let nameIdx? := thmCtxs.zipIdx.find? (·.1.thmName == thmName)
    let (posStx, entryIdx) : Lean.Syntax × Nat := match nameIdx? with
      | some (_, i) => (nameStxs[i]!, i)
      | none        => (nameStxs[0]!, 0)
    Lean.logInfoAt posStx
      m!"[cyclic_mutual.{thmName}] events: {evs.length}\n\
         ProofTree:\n{Build.renderTree tree}"
    -- Build the MutualEntry for §6 emission. Binder names + raw type
    -- strings come from the syntax directly (no `elabType`, which
    -- fails on dependent types like `(h : Od n)` outside the right
    -- elaboration context). SortInfo is recovered by looking up the
    -- type's head identifier in the env — sufficient for `cases h
    -- with` since constructors don't depend on the type's indices.
    let (_, bracketedBinders, typeStx, _) := entries[entryIdx]!
    let goalTypeStr := typeStx.raw.reprint.getD "<unknown>"
    let mut bindersWithTypes : List (String × String) := []
    let mut varSorts : List (String × CyclicTactic.EmitCommon.SortInfo) := []
    for h : i in [:bracketedBinders.size] do
      let bb := bracketedBinders[i]
      match bb.raw with
      | `(Lean.Parser.Term.bracketedBinderF| ($vs:ident* : $bt:term)) =>
        let typeStr := bt.raw.reprint.getD "<?>"
        -- Resolve the type's head ident to an inductive name and
        -- build SortInfo from its constructors. Falls through to
        -- "no sort info" if the head isn't an inductive — the
        -- emitter handles that with a `sorry` fallback.
        let headIdent? : Option Lean.Name := Id.run do
          let mut cur := bt.raw
          while cur.getKind == ``Lean.Parser.Term.app do
            cur := cur[0]
          match cur with
          | .ident _ _ n _ => return some n
          | _              => return none
        let env ← Lean.getEnv
        let resolve : Lean.Name → Option Lean.ConstantInfo :=
          let rec go (n : Lean.Name) : Option Lean.ConstantInfo :=
            match env.find? n with
            | some ci => some ci
            | none => match n with
              | .str p _ => go p
              | _        => none
          go
        let si? : Option CyclicTactic.EmitCommon.SortInfo :=
          match headIdent?.bind resolve with
          | some (.inductInfo indVal) =>
            let ctorsCI : List CyclicTactic.EmitCommon.CtorInfo :=
              indVal.ctors.foldl (init := []) fun acc ctorName =>
                match env.find? ctorName with
                | some (.ctorInfo cv) =>
                  let shortName := ctorName.toString.splitOn "." |>.getLast!
                  acc ++ [{ shortName := shortName
                            fullName  := ctorName.toString
                            recArgs   := []
                            totalArgs := cv.numFields }]
                | _ => acc
            some { typeStr := typeStr, ctors := ctorsCI }
          | _ => none
        for v in vs do
          bindersWithTypes := bindersWithTypes ++ [(v.getId.toString, typeStr)]
          if let some si := si? then
            varSorts := varSorts ++ [(v.getId.toString, si)]
      | _ => pure ()
    let entry : CyclicTactic.Theorem6.Emit.MutualEntry :=
      { thmName  := thmName.toString
        binders  := bindersWithTypes
        goalType := goalTypeStr
        tree     := tree
        varSorts := varSorts }
    mutualEntries := mutualEntries ++ [entry]
  -- Build the §6 companion-map: label → (sibling-thm-name, binder-vars).
  -- Dedup labels (the table is double-populated by the syntactic
  -- pre-scan + the live `cyclic <label>` calls).
  let companionMap : List (String × String × List String) :=
    companionTargets.foldl (init := []) fun acc (lbl, ctx) =>
      if acc.any (·.1 == lbl) then acc
      else acc ++ [(lbl, ctx.thmName.toString, ctx.binders.map (·.toString))]
  let mutualScript := CyclicTactic.Theorem6.Emit.translateMutual
    (defaultSimpPred := st.goalHeadName)
    mutualEntries companionMap
  Lean.logInfoAt nameStxs[0]!
    m!"[cyclic_mutual] §6 emitted script:\n{mutualScript}"
  -- Phase E: try Theorem 6.1 canonical emission. Parse the §6 script
  -- and, if elaboration produces sorry-free declarations for every
  -- entry, roll back to `envBefore` and commit the §6 form as the
  -- canonical declarations. On failure, restore `envWithRecursive`.
  match Lean.Parser.runParserCategory envWithRecursive `command mutualScript with
  | .ok cmdStx =>
    Lean.setEnv envBefore
    let beforeMsgs := (← getThe Lean.Elab.Command.State).messages
    try Lean.Elab.Command.elabCommand cmdStx catch _ => pure ()
    let envAfter ← Lean.getEnv
    let allGood : Bool := thmCtxs.all fun ctx =>
      match envAfter.find? ctx.thmName with
      | some di =>
        match di.value? with
        | some v => !v.hasSorry
        | none   => true
      | none    => false
    if allGood then
      Lean.logInfoAt nameStxs[0]!
        m!"[cyclic_mutual] canonical form: Theorem 6.1 emission ✓"
    else
      Lean.setEnv envWithRecursive
      modifyThe Lean.Elab.Command.State fun s => { s with messages := beforeMsgs }
      Lean.logWarningAt nameStxs[0]!
        m!"[cyclic_mutual] Theorem 6.1 emission produced sorries; keeping recursive form."
  | .error msg =>
    Lean.logWarningAt nameStxs[0]!
      m!"[cyclic_mutual] Theorem 6.1 script parse failed ({msg}); keeping recursive form."
  -- Done — clean up.
  setCurrentThm none
  resetMutualState

end CyclicTactic
