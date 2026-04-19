import Lean
import Cyclic.ProofTree
import Cyclic.ThmCmd

/-!
# `by_cyclic` — tactic-style DSL for writing cyclic proofs

A surface syntax that lets you write cyclic proofs without explicitly
constructing `ProofTree` values. The DSL is parsed at elaboration time
into a `ProofTree`, then handed to the same backend pipeline as the
explicit form.

## Examples

```
cyclic_thm myL_all : myL by_cyclic
  cases xs with
    | []         => done
    | cons x xs' => back {xs := xs'}
```

```
cyclic_thm myB_all : myB by_cyclic
  R: cases x with
    | zero    => done
    | succ x' =>
      cases y with
        | zero    => back R {x := x', y := 1}
        | succ y' => back {y := y'}
```

## Step grammar

  * `done` — leaf
  * `back [<label>] [{var := term, …}]` — back-edge to ancestor
  * `cases <var> with | <pat> => <step> | … | <pat> => <step>`
  * `<label>: <step>` — attach a user label
-/

/-! ### Syntax categories (top-level: Lean syntax cats aren't namespaced) -/

declare_syntax_cat cyclic_pat
declare_syntax_cat cyclic_step

syntax (name := cycPatNum)  num                       : cyclic_pat
syntax (name := cycPatNil)  "[" "]"                   : cyclic_pat
syntax (name := cycPatCons) ident " :: " ident        : cyclic_pat
syntax (name := cycPatCtor) ident (ppSpace ident)*    : cyclic_pat

syntax cyclicSubstItem := ident " := " term
syntax cyclicSubst := "{" cyclicSubstItem,* "}"

syntax cyclicArm := "| " cyclic_pat " => " cyclic_step

syntax (name := cycDone)
  "done" (" by " Lean.Parser.Tactic.tacticSeq)? : cyclic_step
syntax (name := cycBack)
  "back" (ppSpace ident)? (ppSpace cyclicSubst)?
    (" by " Lean.Parser.Tactic.tacticSeq)? : cyclic_step
syntax (name := cycCases)
  "cases " ident " with " withPosition((colGe cyclicArm)+) : cyclic_step
syntax (name := cycLabel)
  ident ":" cyclic_step : cyclic_step

namespace Cyclic.Tactic

open Lean Elab Command Cyclic.Proof

/-! ### Conversion from syntax to `SubjectTerm` -/

/-- Turn a numeric literal into a `Nat.succ ⋯ Nat.zero` chain. -/
private def natToSubject (n : Nat) : SubjectTerm := Id.run do
  let mut t : SubjectTerm := .ctor "zero" []
  for _ in [0:n] do
    t := .ctor "succ" [t]
  return t

partial def patToSubject (stx : TSyntax `cyclic_pat) : CommandElabM SubjectTerm := do
  match stx with
  | `(cyclic_pat| $n:num) =>
    return natToSubject n.getNat
  | `(cyclic_pat| []) =>
    return .ctor "nil" []
  | `(cyclic_pat| $a:ident :: $b:ident) =>
    return .ctor "cons" [.var a.getId.toString, .var b.getId.toString]
  | `(cyclic_pat| $c:ident $args:ident*) =>
    let argVars := args.toList.map fun i => SubjectTerm.var i.getId.toString
    return .ctor c.getId.toString argVars
  | _ => throwError "unrecognized cyclic pattern: {stx}"

/-- Turn a Lean term used in a substitution RHS into a `SubjectTerm`. -/
partial def termToSubject (stx : Syntax) : CommandElabM SubjectTerm := do
  match stx with
  | `($n:num) =>
    return natToSubject n.getNat
  | `(($t:term)) =>
    termToSubject t.raw
  | `(Nat.zero) =>
    return .ctor "zero" []
  | `(Nat.succ $t:term) =>
    return .ctor "succ" [← termToSubject t.raw]
  | `([]) =>
    return .ctor "nil" []
  | `($a:term :: $b:term) =>
    return .ctor "cons" [← termToSubject a.raw, ← termToSubject b.raw]
  | `($i:ident) =>
    return .var i.getId.toString
  | _ =>
    -- Fallback for `f x y …` — head must be a single identifier.
    if stx.getKind == ``Lean.Parser.Term.app then
      let args := stx.getArgs
      if args.size ≥ 2 then
        let f := args[0]!
        let xs := args[1]!.getArgs
        match f with
        | `($i:ident) =>
          let argSubjs ← xs.toList.mapM (fun a => termToSubject a)
          return .ctor i.getId.toString argSubjs
        | _ => throwError "unsupported subst rhs: {stx}"
    throwError "unsupported subst rhs: {stx}"

/-! ### Building the `ProofTree` -/

def mkSequent (predName : Name) (args : List SubjectTerm) : Sequent :=
  let formula : Formula := { pred := predName.toString, args := args }
  .succ1 formula

/-- A *non-iterating* substitution. `SubjectTerm.subst` iterates on the
    looked-up replacement, which is intended for composing chained
    substitutions but breaks on user σs like `{y := Nat.succ y}` where
    the RHS mentions the variable being replaced. For a single-shot
    apply at a back-edge, we want exactly one rewrite per variable
    occurrence — no cycle risk. -/
partial def substOnce (σ : List (String × SubjectTerm)) : SubjectTerm → SubjectTerm
  | .var n =>
    match σ.lookup n with
    | none   => .var n
    | some t => t
  | .ctor n args => .ctor n (args.map (substOnce σ))

private def fresh (pfx : String) : StateRefT Nat CommandElabM String := do
  let n ← get
  set (n + 1)
  return s!"{pfx}{n}"

/-- An entry in the ancestor stack: the case-split's auto-or-user label
    paired with the predicate's argument list at the moment that case-split
    was entered. The latter is what a back-edge's `σ` is applied to. -/
abbrev AncEntry := String × List SubjectTerm

partial def walkStep
    (predName : Name)
    (currentArgs : List SubjectTerm)
    (ancStack : List AncEntry)         -- innermost first
    (forcedLabel : Option String)
    (stx : TSyntax `cyclic_step)
    : StateRefT Nat CommandElabM Cyclic.Proof.ProofTree := do
  let getLabel (pfx : String) : StateRefT Nat CommandElabM String :=
    match forcedLabel with
    | some l => pure l
    | none   => fresh pfx
  match stx with
  | `(cyclic_step| $userLbl:ident : $sub:cyclic_step) =>
    walkStep predName currentArgs ancStack (some userLbl.getId.toString) sub
  | `(cyclic_step| done $[by $tac]?) =>
    let lbl ← getLabel "_L"
    let tacStr := tac.bind (·.raw.reprint)
    return .leaf lbl (mkSequent predName currentArgs) "done" tacStr
  | `(cyclic_step| back $[$ancId]? $[$subst]? $[by $tac]?) =>
    -- Resolve the target ancestor: explicit label, or nearest enclosing.
    let entry : AncEntry ← match ancId with
      | some i =>
        let lblStr := i.getId.toString
        match ancStack.find? (fun e => e.1 == lblStr) with
        | some e => pure e
        | none =>
          throwError s!"back: no ancestor labelled '{lblStr}' in scope"
      | none =>
        match ancStack with
        | e :: _ => pure e
        | [] =>
          throwError "back: no enclosing case-split to default to; supply an explicit ancestor label"
    let ancLabel := entry.1
    let ancArgs := entry.2
    let σ : Subst ← match subst with
      | none   => pure []
      | some s =>
        match s with
        | `(cyclicSubst| { $items:cyclicSubstItem,* }) =>
          items.getElems.toList.mapM fun (item : TSyntax `cyclicSubstItem) => do
            match item with
            | `(cyclicSubstItem| $v:ident := $t:term) =>
              return ((v.getId.toString : String), ← termToSubject t.raw)
            | _ => throwError "malformed substitution item"
        | _ => throwError "expected substitution braces"
    -- The back-edge's sequent is the ancestor's sequent with σ applied —
    -- i.e. the IH instantiated at the user-supplied σ. Non-iterating
    -- because user σs may legitimately have RHSs that mention the same
    -- variable (e.g. `{y := Nat.succ y}` in a `y`-rebinding back-edge).
    let bArgs := ancArgs.map (substOnce σ)
    let backLbl ← getLabel "_B"
    let tacStr := tac.bind (·.raw.reprint)
    let backNode : Cyclic.Proof.ProofTree :=
      .back backLbl (mkSequent predName bArgs) ancLabel σ tacStr
    -- When the user didn't supply `by tac`, wrap the back-edge in an
    -- `.node "unfold"` so the translator emits `simp [<pred>]` before
    -- the `exact ih …`. With a custom close tactic, the user takes full
    -- control — emit the bare `.back` so we don't double-emit simp.
    match tacStr with
    | some _ => return backNode
    | none =>
      let nodeLbl ← fresh "_U"
      return .node nodeLbl (mkSequent predName currentArgs) "unfold" [backNode]
  | `(cyclic_step| cases $varId:ident with $arms:cyclicArm*) =>
    let lbl ← getLabel "_R"
    let varName := varId.getId.toString
    let myEntry : AncEntry := (lbl, currentArgs)
    let armList ← arms.toList.mapM fun (arm : TSyntax `cyclicArm) => do
      match arm with
      | `(cyclicArm| | $pat:cyclic_pat => $body:cyclic_step) => do
        let patSubj ← patToSubject pat
        let σPat : Subst := [(varName, patSubj)]
        let argsAfterCase := currentArgs.map (SubjectTerm.subst σPat)
        let subTree ← walkStep predName argsAfterCase (myEntry :: ancStack) none body
        return (patSubj, subTree)
      | _ => throwError "malformed arm"
    return .caseSplit lbl (mkSequent predName currentArgs) varName armList
  | _ =>
    throwError "unrecognized cyclic step: {stx}"

/-! ### Predicate binder-name introspection -/

def getPredArgNames (predName : Name) : Lean.MetaM (List String) := do
  let env ← getEnv
  let some predInfo := env.find? predName
    | throwError "predicate not found: {predName}"
  Lean.Meta.forallTelescope predInfo.type fun args _ => do
    args.toList.mapM fun a => do
      let decl ← a.fvarId!.getDecl
      return decl.userName.toString

end Cyclic.Tactic

/-! ### Surface forms 2 & 3 — `by_cyclic` DSL

  * Predicate form: `cyclic_thm name : pred args by_cyclic …` — user
    references a separately-defined Prop predicate.
  * Inline-goal form: `cyclic_thm name (binders) : <goal> by_cyclic …` —
    user writes the theorem statement inline, like a normal Lean
    theorem. The `by_cyclic` clause supplies the cyclic structure;
    SCT is validated against the synthetic goal-as-predicate.
-/

/-- A binder for the inline-goal form: `(name : type)`. -/
syntax cyclicBinder := "(" ident " : " term ")"

syntax (name := cyclicThmBy)
  "cyclic_thm " ident " : " ident (ppSpace ident)* " by_cyclic " cyclic_step : command

syntax (name := cyclicThmGoal)
  "cyclic_thm " ident (ppSpace cyclicBinder)+ " : " term " by_cyclic " cyclic_step : command

elab_rules : command
  | `(cyclic_thm $name:ident : $pred:ident $args:ident* by_cyclic $step:cyclic_step) => do
    -- The user-supplied arg idents become the initial `cases` targets and
    -- the variable names threaded through the proof tree. They must match
    -- the predicate's argument positions in declaration order.
    let argNames : List String := args.toList.map (·.getId.toString)
    let initArgs : List Cyclic.Proof.SubjectTerm :=
      argNames.map (Cyclic.Proof.SubjectTerm.var ·)
    let (proofTree, _) ←
      (Cyclic.Tactic.walkStep pred.getId initArgs [] none step).run 0
    Cyclic.Thm.runCyclicThm name pred proofTree

elab_rules : command
  | `(cyclic_thm $name:ident $binders:cyclicBinder* : $goal:term by_cyclic $step:cyclic_step) => do
    -- Pull (varName, varType) pairs from the binders.
    let mut argNames : List String := []
    let mut argTypeSyns : List (Lean.TSyntax `term) := []
    for b in binders do
      match b with
      | `(cyclicBinder| ($v:ident : $t:term)) =>
        argNames := argNames ++ [v.getId.toString]
        argTypeSyns := argTypeSyns ++ [t]
      | _ => throwError "malformed cyclic binder"
    -- Build a SortInfo for each binder type via existing introspection.
    let sorts ← Lean.Elab.Command.liftTermElabM do
      argTypeSyns.mapM fun (typeStx : Lean.TSyntax `term) => do
        let typeExpr ← Lean.Elab.Term.elabType typeStx
        Cyclic.Thm.buildSortInfo typeExpr
    let varSorts : List (String × Cyclic.Unravel.SortInfo) := argNames.zip sorts
    -- Walk the cyclic structure into a ProofTree. Use the theorem's own
    -- name as the synthetic predicate name (only used for SCT bookkeeping
    -- — the emitted theorem uses the user's goal expression directly).
    let initArgs : List Cyclic.Proof.SubjectTerm :=
      argNames.map (Cyclic.Proof.SubjectTerm.var ·)
    let synthPredName := name.getId
    let (proofTree, _) ←
      (Cyclic.Tactic.walkStep synthPredName initArgs [] none step).run 0
    -- The goal expression: take the user's source verbatim.
    let goalStr := goal.raw.reprint.getD "<goal>"
    -- No default predicate to unfold — leaves/back-edges that don't
    -- supply `by tac` get bare `simp`, which the user can override.
    Cyclic.Thm.runCyclicThmCore name varSorts goalStr none proofTree
