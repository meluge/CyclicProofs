import Lean
import Cyclic.ProofTree
import Cyclic.Unravel
import Cyclic.SizeChange
import Cyclic.Measure
import Cyclic.Annotation
import Cyclic.Reorganize

/-!
# The `cyclic_thm` command

Turns a validated `ProofTree` into a real Lean theorem at elaboration time.

## Two surface forms

```
cyclic_thm myQ_all : myQ := qProof          -- explicit ProofTree value
cyclic_thm myQ_all : myQ by_cyclic …        -- tactic-style DSL (see Cyclic.Tactic)
```

Both forms feed into the same backend pipeline below.

## Pipeline

  1. (External) Obtain a `ProofTree` value — either by elaborating a
     user-provided term, or by walking the DSL syntax.
  2. Run `extractTraceSCGs` + `checkMultiSCT`. Fail at the theorem name's
     position if SCT rejects.
  3. Synthesize a termination `Measure` for diagnostics.
  4. Introspect the predicate's signature: walk its Pi-binders to get
     each argument's binder name and inductive type, then build
     `Cyclic.Unravel.SortInfo` for each type from the environment.
  5. Call `Cyclic.Unravel.translate` to produce a `theorem … := by …`
     script as a `String`.
  6. Parse and `elabCommand`. Lean's kernel then checks the theorem,
     which is what makes this approach sound regardless of `translate`'s
     internal correctness.
-/

open Lean Elab Command Meta

namespace Cyclic.Thm

/-! ### Unsafe `evalExpr` wrapper for `ProofTree` values -/

unsafe def evalProofTreeExprImpl (e : Expr) : MetaM Cyclic.Proof.ProofTree :=
  evalExpr Cyclic.Proof.ProofTree (mkConst ``Cyclic.Proof.ProofTree) e

@[implemented_by evalProofTreeExprImpl]
def evalProofTreeExpr (_e : Expr) : MetaM Cyclic.Proof.ProofTree :=
  pure default

/-! ### Predicate-type introspection -/

/-- Build `CtorInfo` for a single constructor of inductive `indName`,
    after substituting the inductive's parameters from `typeArgs`. -/
def buildCtorInfo (indName : Name) (typeArgs : Array Expr) (ctorName : Name)
    : MetaM (Option Cyclic.Unravel.CtorInfo) := do
  let env ← getEnv
  let some ctorInfo := env.find? ctorName | return none
  let ctorTypeApplied : Expr := Id.run do
    let mut t := ctorInfo.type
    let mut tas := typeArgs.toList
    while t.isForall && !tas.isEmpty do
      t := t.bindingBody!.instantiate1 tas.head!
      tas := tas.tail
    return t
  forallTelescope ctorTypeApplied fun fargs _ => do
    let mut recArgs : List Nat := []
    for h : i in [0:fargs.size] do
      let fa := fargs[i]
      let aType ← inferType fa
      if let .const n _ := aType.getAppFn then
        if n == indName then
          recArgs := recArgs ++ [i]
    let shortName := ctorName.toString.splitOn "." |>.getLast!
    return some {
      shortName  := shortName
      fullName   := ctorName.toString
      recArgs    := recArgs
      totalArgs  := fargs.size
    }

/-- Build `SortInfo` for a Lean type expression like `Nat` or `List Nat`. -/
def buildSortInfo (typeExpr : Expr) : MetaM Cyclic.Unravel.SortInfo := do
  let typeExpr ← whnf typeExpr
  let head := typeExpr.getAppFn
  let typeArgs := typeExpr.getAppArgs
  let env ← getEnv
  match head with
  | .const indName _ =>
    match env.find? indName with
    | some (.inductInfo indVal) =>
      let typeStr := (← Meta.ppExpr typeExpr).pretty
      let mut ctors : List Cyclic.Unravel.CtorInfo := []
      for cn in indVal.ctors do
        if let some ci ← buildCtorInfo indName typeArgs cn then
          ctors := ctors ++ [ci]
      return { typeStr := typeStr, ctors := ctors }
    | _ =>
      throwError "expected an inductive type, got: {typeExpr}"
  | _ =>
    throwError "expected an inductive type head, got: {typeExpr}"

/-- For `pred : T₁ → … → Tₙ → Prop`, return one entry per argument:
    the binder's `userName` and the corresponding `SortInfo`. -/
def buildPredicateSig (predName : Name)
    : MetaM (List (String × Cyclic.Unravel.SortInfo)) := do
  let env ← getEnv
  let some predInfo := env.find? predName
    | throwError "predicate not found: {predName}"
  forallTelescope predInfo.type fun args _ => do
    let mut sig : List (String × Cyclic.Unravel.SortInfo) := []
    for arg in args do
      let aType ← inferType arg
      let aName := (← arg.fvarId!.getDecl).userName.toString
      let si ← buildSortInfo aType
      sig := sig ++ [(aName, si)]
    return sig

/-! ### Shared backend: turn a `ProofTree` into an elaborated theorem -/

/-- Once a `ProofTree` value, the per-root-var sort info, the goal type
    string, and the default-simp predicate are in hand, run the SCT
    check + measure synth + script emission + kernel elaboration.

    Used by all three surface forms:

      * `cyclic_thm name : pred := <term>`     (predicate, explicit tree)
      * `cyclic_thm name : pred args by_cyclic …`  (predicate, DSL)
      * `cyclic_thm name (binders) : <goal> by_cyclic …`  (inline goal, DSL)
-/
def runCyclicThmCore
    (nameStx : Lean.TSyntax `ident)
    (varSorts : List (String × Cyclic.Unravel.SortInfo))
    (goalType : String)
    (defaultSimpPred : Option String)
    (proofTree : Cyclic.Proof.ProofTree)
    : CommandElabM Unit := do
  -- Step 1: SCT check.
  let graphs := Cyclic.Proof.extractTraceSCGs proofTree
  let labeledGraphs := Cyclic.Proof.extractTraceSCGsLabeled proofTree
  unless SCGraph.checkMultiSCT graphs do
    let lines := graphs.map fun g => "  " ++ toString g
    throwErrorAt nameStx
      ("cyclic_thm '" ++ toString nameStx.getId
        ++ "': multi-SCT check FAILED.\nExtracted graphs:\n"
        ++ String.intercalate "\n" lines
        ++ "\nNo SCT-based measure exists for this derivation.")
  -- Step 2: synthesize a measure. This now drives emission, not just
  -- diagnostics — `translateWF` plumbs it into a `termination_by` clause
  -- so the cyclic proof's soundness travels with the emitted def.
  let rootArity : Nat :=
    let ns := proofTree.sequent.antecedents.map (·.args.length) ++
              proofTree.sequent.succedents.map (·.args.length)
    ns.foldl (· + ·) 0
  let measureOpt := synthMeasure graphs rootArity
  let measureStr :=
    match measureOpt with
    | some m => toString m
    | none   => "(none — SCT closure passes but no lex/sum measure)"
  -- Step 2b: paper-style reset annotation — assigns each back-edge a
  -- progressing name from the closure-idempotent witness, and a global
  -- induction order. `progMap` feeds the per-back-edge comments the
  -- emitter prepends to each recursive call.
  let annotOpt : Option Cyclic.Annotation.ProofAnnot :=
    match Cyclic.Annotation.annotate labeledGraphs rootArity (some proofTree) with
    | .ok a => some a
    | .error _ => none
  let annotStr : String :=
    match annotOpt with
    | some a  => Cyclic.Annotation.render a
    | none    => "(annotation unavailable)"
  -- Closure witnesses: raw strict-self-loop positions per idempotent.
  -- Still surfaced alongside the annotation because it makes the SCT
  -- analysis legible even when annotation-level attribution fails.
  let witnessStr := witnessesToString graphs rootArity
  -- Step 3: dispatcher — structural emission (nested `induction`) when
  -- the annotation's induction order lex-validates every back-edge's
  -- input graph; otherwise fall back to WF emission with a synthesised
  -- measure. Structural is the paper-faithful path (Wehr §6, Sprenger-
  -- Dam, Grotenhuis-Otten Theorem 6.1: "preserves the structure of π")
  -- and produces output that reads like an ordinary Lean inductive
  -- proof; WF is the catch-all (Lee 2009 measure-synthesis tradition)
  -- for sum/swap-style cases where descent shows up only in the SCT
  -- closure, not the per-call graph.
  let canStructOriginal : Bool :=
    match annotOpt with
    | some a => Cyclic.Annotation.ProofAnnot.canStructural a labeledGraphs proofTree varSorts
    | none   => false
  -- If structural feasibility fails on the original tree, try
  -- reorganising it (Grotenhuis-Otten Prop 5.8 / Wehr Ch. 7): permute
  -- the case-split nesting to match the annotation's induction order,
  -- then retarget each back-edge based on its descending variable
  -- (looked up via the annotation's per-back-edge progPos). Re-extract
  -- trace SCGs from the reorganised + retargeted tree and re-check
  -- feasibility. If it passes, emit structurally on it; else WF.
  --
  -- Why retarget separately: a back-edge that descends on `x` and
  -- originally targeted the outer `cases y` (because the user happened
  -- to write y outer) must, after the swap, target the new outer
  -- `cases x`, not the new inner `cases y`. A simple label remap can't
  -- compute this; we need descending-variable awareness.
  let (proofTree', labeledGraphs', useStructural, reorganised) :
      Cyclic.Proof.ProofTree × List (String × SCGraph) × Bool × Bool :=
    if canStructOriginal then
      (proofTree, labeledGraphs, true, false)
    else
      match annotOpt with
      | none   => (proofTree, labeledGraphs, false, false)
      | some a =>
        let varOrder := a.varOrder varSorts
        -- Step 1: reorder case-split nesting.
        let reorgTree := Cyclic.Reorganize.reorder varOrder proofTree
        -- Step 2: build descMap (back-edge label → descending variable
        -- name) from the original annotation, then retarget each back-
        -- edge's `anc` to the case-split on its descending variable in
        -- the reorganised scope.
        let descMap : List (String × String) :=
          a.backEdges.filterMap fun be =>
            (varSorts[be.progPos]?).map fun (vName, _) => (be.label, vName)
        let retargeted := Cyclic.Reorganize.retargetBacks descMap [] reorgTree
        let reorgGraphs := Cyclic.Proof.extractTraceSCGsLabeled retargeted
        let reorgOk := Cyclic.Annotation.ProofAnnot.canStructural a reorgGraphs retargeted varSorts
        if reorgOk then (retargeted, reorgGraphs, true, true)
        else (proofTree, labeledGraphs, false, false)
  -- Recompute the prog map from the (possibly reorganised) labeled graphs.
  let progMap' : List (String × Nat) :=
    match annotOpt with
    | some a =>
      match Cyclic.Annotation.annotate labeledGraphs' rootArity (some proofTree') with
      | .ok a' => a'.backEdges.map fun be => (be.label, be.progPos)
      | .error _ => a.backEdges.map fun be => (be.label, be.progPos)
    | none => []
  let thmName := toString nameStx.getId
  let script :=
    if useStructural then
      Cyclic.Unravel.translate defaultSimpPred goalType thmName
        varSorts proofTree'
    else
      Cyclic.Unravel.translateWF defaultSimpPred goalType thmName
        varSorts measureOpt progMap' proofTree'
  let pathStr :=
    if useStructural then
      if reorganised then "structural (nested `induction`, after reorganisation)"
      else "structural (nested `induction`)"
    else "WF (`termination_by`)"
  let env ← getEnv
  match Lean.Parser.runParserCategory env `command script with
  | .error msg =>
    throwErrorAt nameStx
      ("cyclic_thm: failed to parse emitted script:\n" ++ msg
        ++ "\nScript:\n" ++ script)
  | .ok cmdStx =>
    elabCommand cmdStx
    logInfoAt nameStx
      ("[cyclic_thm " ++ thmName ++ "] multi-SCT PASS; measure = "
        ++ measureStr ++ "; emission = " ++ pathStr
        ++ "\nannotation:\n" ++ annotStr
        ++ "\nclosure witnesses:\n" ++ witnessStr
        ++ "\nemitted:\n" ++ script)

/-- Convenience for the predicate form: introspects the predicate
    signature from the environment, then dispatches to `runCyclicThmCore`. -/
def runCyclicThm (name pred : Lean.TSyntax `ident) (proofTree : Cyclic.Proof.ProofTree)
    : CommandElabM Unit := do
  let sig ← liftTermElabM do buildPredicateSig pred.getId
  let sorts := sig.map (·.2)
  let rootVars := Cyclic.Unravel.sequentVars proofTree.sequent
  let varSorts : List (String × Cyclic.Unravel.SortInfo) := rootVars.zip sorts
  let leanPred := toString pred.getId
  let argList := String.intercalate " " rootVars
  let goalType := leanPred ++ " " ++ argList
  runCyclicThmCore name varSorts goalType (some leanPred) proofTree

end Cyclic.Thm

/-! ### Surface form 1: explicit `ProofTree` value -/

syntax (name := cyclicThm)
  "cyclic_thm " ident " : " ident " := " term : command

elab_rules : command
  | `(cyclic_thm $name:ident : $pred:ident := $tree:term) => do
    let proofTree ← liftTermElabM do
      let expectedType := mkConst ``Cyclic.Proof.ProofTree
      let expr ← Term.elabTermAndSynthesize tree (some expectedType)
      let expr ← instantiateMVars expr
      Cyclic.Thm.evalProofTreeExpr expr
    Cyclic.Thm.runCyclicThm name pred proofTree
