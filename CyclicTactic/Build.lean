import Lean
import CyclicTactic.ProofTree
import CyclicTactic.Unravel

/-!
# Building a `ProofTree` from tactic-recorded events

Convert the linear event stream produced by the tactic frontend
(`CyclicTactic.Tactic`) into a `CyclicTactic.Proof.ProofTree` value —
the data-DSL's first-class cyclic-proof type that feeds SCT validation
+ structural emission.

Three main pieces:

  * Event data types (`CyclicEvent`, `CyclicState`, etc.) — placed
    here (rather than in `Tactic.lean`) so the converter and the tree
    builder can work on them without an import cycle.
  * `Expr → SubjectTerm` and `Expr → Sequent` converters (best-effort,
    handle Nat ctors / fvars / app heads / Nat literals / OfNat
    wrappers; opaque fallback for anything else).
  * `eventsToTree` — walks the event stream into a `ProofTree`, using
    source-position attribution to assign back-edges to arms.
  * `buildSortInfo` — introspects a binder type into the `SortInfo`
    Unravel needs to emit `induction` blocks.
-/

namespace CyclicTactic

open Lean
open CyclicTactic.Proof

/-! ### Cyclic state types (shared between Tactic and Build) -/

/-- A source-position range (byte offsets in the source file). Used by
    the tree builder to attribute back-edges to the correct case-split
    arm without manually elaborating arm bodies. -/
structure SourceRange where
  startPos : Nat
  endPos : Nat
  deriving Inhabited, Repr

def SourceRange.contains (r : SourceRange) (p : Nat) : Bool :=
  r.startPos ≤ p && p ≤ r.endPos

/-- One arm of a case-split, as recorded by `cyc_cases`: constructor
    name + binder names + source range + arm body source text. -/
structure ArmInfo where
  ctor : Lean.Name
  binders : List Lean.Name
  range : SourceRange
  /-- Source text of the arm's body (after `=>`), used as a leaf's
      closeTactic or as a back-arm prelude (with the back call's text
      replaced by `recurse`). -/
  bodyText : String := ""
  deriving Inhabited

/-- An event recorded into the cyclic state during interactive
    elaboration. Position-based attribution: `caseSplitStart` carries
    arm position ranges; `back` carries its own source position +
    source text. -/
inductive CyclicEvent where
  | companion (label : String) (sequent : Sequent)
  | caseSplitStart (var : String) (sequent : Sequent) (arms : List ArmInfo)
  | caseSplitEnd
  /-- A back-edge: ancestor label, captured sequent, σ, source
      position (for arm attribution), and source text (for emission —
      gets replaced by `recurse` inside the arm prelude). -/
  | back (ancestor : String) (sequent : Sequent) (σ : Subst)
         (pos : Nat) (sourceText : String)
  deriving Inhabited

structure CyclicState where
  companions : List (String × Sequent) := []
  events : List CyclicEvent := []
  /-- Head constant of the user's goal type (e.g. `"btPred"` for
      `btPred t n`). Passed to `Unravel.translate` as
      `defaultSimpPred` so the emitted script uses `simp [btPred]`
      to unfold the predicate at leaves and at branch preludes. -/
  goalHeadName : Option String := none
  deriving Inhabited

initialize cyclicStateRef : IO.Ref CyclicState ← IO.mkRef {}

def resetCyclicState : IO Unit := cyclicStateRef.set {}
def getCyclicState : IO CyclicState := cyclicStateRef.get
def modifyCyclicState (f : CyclicState → CyclicState) : IO Unit :=
  cyclicStateRef.modify f
def pushEvent (e : CyclicEvent) : IO Unit :=
  modifyCyclicState fun st => { st with events := e :: st.events }

namespace Build

/-! ### `Expr → SubjectTerm` (best-effort)

Filters arguments by binder-info (keeps only EXPLICIT args) so
typeclass instances + implicit type args don't bleed into the term.
Handles Nat literals (`.lit (.natVal n)`) by building a `succ ∘ … ∘
zero` chain, and peels `OfNat.ofNat` wrappers so a goal arg like
`(1 : Nat)` produces a clean `succ(zero)` chain rather than
`ofNat(succ(zero))`. -/

partial def exprToSubject (e : Expr) : MetaM SubjectTerm := do
  -- Resolve any pending mvars + peel `.mdata` wrappers so the match
  -- below sees the canonical Expr form.
  let e ← Lean.instantiateMVars e
  let e := e.consumeMData
  match e with
  | .fvar fvarId =>
    let decl ← fvarId.getDecl
    return .var decl.userName.toString
  | .const name _ =>
    let short := name.toString.splitOn "." |>.getLast!
    return .ctor short []
  | .app .. =>
    let head := e.getAppFn
    let args := e.getAppArgs
    -- Peel `OfNat.ofNat`-style numeric-literal wrappers so a goal arg
    -- like `1 : Nat` produces a clean `succ(zero)` chain rather than
    -- `ofNat(succ(zero))`. The literal value sits at args[1].
    if let .const ``OfNat.ofNat _ := head then
      if h : args.size ≥ 2 then
        return ← exprToSubject args[1]
    let headName : String ← match head with
      | .const n _ => pure (n.toString.splitOn "." |>.getLast!)
      | .fvar f    => do
        let decl ← f.getDecl
        pure decl.userName.toString
      | _          => pure "_app"
    -- Use the function's binder info to keep only EXPLICIT args.
    let info ← Lean.Meta.getFunInfo head
    let mut argTerms : List SubjectTerm := []
    for h : i in [:args.size] do
      let a := args[i]
      let isExplicit : Bool :=
        match info.paramInfo[i]? with
        | some p => p.binderInfo.isExplicit
        | none   => true
      if isExplicit then
        argTerms := argTerms ++ [← exprToSubject a]
    return .ctor headName argTerms
  | .lit (.natVal n) =>
    -- Render Nat literals as a `succ ∘ … ∘ zero` chain so SCT can see
    -- structural relations and Unravel's `termToLean` renders them
    -- back as numerals.
    let mut t : SubjectTerm := .ctor "zero" []
    for _ in [:n] do
      t := .ctor "succ" [t]
    return t
  | .lit (.strVal s) =>
    return .var s!"\"{s}\""
  | _ =>
    let pp ← Lean.Meta.ppExpr e
    return .var s!"<{pp.pretty}>"

/-! ### `Expr → Sequent` (best-effort) -/

def exprToSequent (e : Expr) : MetaM Sequent := do
  let e ← Lean.instantiateMVars e
  let e := e.consumeMData
  let head := e.getAppFn
  let args := e.getAppArgs
  let predName : String := match head with
    | .const n _ => n.toString
    | _          => "<opaque>"
  let info ← Lean.Meta.getFunInfo head
  let mut argTerms : List SubjectTerm := []
  for h : i in [:args.size] do
    let a := args[i]
    let isExplicit : Bool :=
      match info.paramInfo[i]? with
      | some p => p.binderInfo.isExplicit
      | none   => true
    if isExplicit then
      argTerms := argTerms ++ [← exprToSubject a]
  return Sequent.succ1 { pred := predName, args := argTerms }

/-! ### Event-stream → ProofTree with position-based attribution

Algorithm: `caseSplitStart` carries arm position ranges. Events
following it (until matching `caseSplitEnd`) include back-edges with
their own source positions. For each back, we find the arm whose range
contains its position. Nested case-splits work recursively. -/

/-- One inner event of a case-split scope: either a back-edge (with
    position + source text) or a nested case-split block. -/
private inductive InnerEvent where
  | back (ancestor : String) (sequent : Sequent) (σ : Subst)
         (pos : Nat) (sourceText : String)
  | nestedCase (var : String) (sequent : Sequent)
                (arms : List ArmInfo) (inner : List InnerEvent)
  deriving Inhabited

/-- Consume events from the start of a case-split scope, grouping
    into `InnerEvent`s. Returns the inner events and remaining events. -/
private partial def consumeScope
    (events : List CyclicEvent) : List InnerEvent × List CyclicEvent := Id.run do
  let mut inner : List InnerEvent := []
  let mut rest := events
  while true do
    match rest with
    | []                            => return (inner, [])
    | .caseSplitEnd :: tail         => return (inner, tail)
    | .back anc bSeq σ p src :: tail =>
      inner := inner ++ [.back anc bSeq σ p src]
      rest := tail
    | .caseSplitStart v s arms :: tail =>
      let (subInner, afterSub) := consumeScope tail
      inner := inner ++ [.nestedCase v s arms subInner]
      rest := afterSub
    | _ :: tail                     => rest := tail
  return (inner, rest)

/-- Assemble the body of a case-split: for each arm, find inner events
    that fall within its source range. Per arm:
      * No matching events → `.leaf` (closeTac = arm body text)
      * One back → `.back` (closeTac = arm body with back text → "recurse")
      * One nested case-split → `.caseSplit`
      * Multiple backs → `.node "branch"` (multi-rec via refine ⟨…⟩) -/
private partial def assembleArms
    (rootSeq : Sequent) (arms : List ArmInfo) (inner : List InnerEvent)
    : List (SubjectTerm × ProofTree) :=
  arms.zipIdx.map fun (arm, armIdx) =>
    let ctorShort := arm.ctor.toString.splitOn "." |>.getLast!
    let binderArgs : List SubjectTerm :=
      arm.binders.map fun b => .var b.toString
    let pat : SubjectTerm := .ctor ctorShort binderArgs
    let matching := inner.filter fun e =>
      match e with
      | .back _ _ _ p _          => arm.range.contains p
      | .nestedCase _ _ nArms _  =>
        match nArms with
        | []     => false
        | a :: _ => arm.range.contains a.range.startPos
    let armBody : ProofTree := match matching with
      | []                              =>
        let closeTac := if arm.bodyText.isEmpty then none else some arm.bodyText
        .leaf s!"_L_{arm.ctor}_{armIdx}" rootSeq "external" closeTac
      | [.back anc bSeq σ _ srcText]    =>
        let closeTac : Option String :=
          if arm.bodyText.isEmpty then none
          else if srcText.isEmpty then some (arm.bodyText ++ "\nrecurse")
          else some (arm.bodyText.replace srcText "recurse")
        .back s!"_B_{arm.ctor}_{armIdx}" bSeq anc σ closeTac
      | [.nestedCase v s nArms nInner]  =>
        .caseSplit s!"_R_{arm.ctor}_{armIdx}" s v (assembleArms s nArms nInner)
      | events                          =>
        -- Multiple events — typical: `node l r => refine ⟨?_, …⟩;
        -- · back R {…}; · back R {…}`. Build `.node "branch"`.
        let allBacks := events.all fun e =>
          match e with | .back .. => true | _ => false
        if allBacks then
          let children : List ProofTree := events.zipIdx.map fun (event, evIdx) =>
            match event with
            | .back anc bSeq σ _ _ =>
              .back s!"_BR_{arm.ctor}_{armIdx}_{evIdx}" bSeq anc σ none
            | _ =>
              .leaf s!"_BR_fallback_{evIdx}" rootSeq "branch slot fallback" none
          .node s!"_branch_{arm.ctor}_{armIdx}" rootSeq "branch" children
        else
          .leaf s!"_L_{arm.ctor}_multi_{armIdx}" rootSeq "mixed-event arm not yet supported" none
    (pat, armBody)

/-- Build a complete `ProofTree` from the event stream. -/
partial def eventsToTree (events : List CyclicEvent) : ProofTree :=
  match events with
  | [] => .leaf "_empty" {} "no events" none
  | .companion lbl rootSeq :: rest => buildBody lbl rootSeq rest
  | _ => .leaf "_no_companion" {} "missing companion event" none
where
  buildBody (companionLbl : String) (rootSeq : Sequent)
      (events : List CyclicEvent) : ProofTree :=
    match events with
    | [] => .leaf "_companion_only" rootSeq "no body" none
    | .caseSplitStart var _ arms :: rest =>
      let (inner, _post) := consumeScope rest
      let armBodies := assembleArms rootSeq arms inner
      .caseSplit companionLbl rootSeq var armBodies
    | .back anc bSeq σ _ _ :: _ =>
      .back companionLbl bSeq anc σ none
    | _ =>
      .leaf "_unrecognised" rootSeq "unrecognised event sequence" none

/-! ### Tree pretty-printing for diagnostics -/

partial def treeToString : ProofTree → Nat → String
  | t, depth =>
    let pad := String.ofList (List.replicate (depth * 2) ' ')
    match t with
    | .leaf lbl seq j _ =>
      s!"{pad}leaf [{lbl}] {seq} ({j})"
    | .identity lbl seq =>
      s!"{pad}identity [{lbl}] {seq}"
    | .node lbl seq r cs =>
      let header := s!"{pad}node [{lbl}] {seq} (rule={r})"
      let body := cs.map (fun c => treeToString c (depth + 1))
      String.intercalate "\n" (header :: body)
    | .caseSplit lbl seq v cs =>
      let header := s!"{pad}cases [{lbl}] {seq} on '{v}'"
      let arms := cs.map fun (pat, sub) =>
        let armHead := s!"{pad}  | {pat}"
        let armBody := treeToString sub (depth + 2)
        armHead ++ "\n" ++ armBody
      String.intercalate "\n" (header :: arms)
    | .back lbl seq anc σ _ =>
      let σstr := if σ.isEmpty then "" else
        " {" ++ String.intercalate ", "
          (σ.map fun (v, t) => s!"{v} := {t}") ++ "}"
      s!"{pad}back [{lbl}] {seq} → {anc}{σstr}"
    | .haveStep lbl seq n _ _ cont =>
      let header := s!"{pad}have [{lbl}] {seq} (intro {n})"
      header ++ "\n" ++ treeToString cont (depth + 1)
    | .existsStep lbl seq w cont =>
      let header := s!"{pad}exists [{lbl}] {seq} (witness={w})"
      header ++ "\n" ++ treeToString cont (depth + 1)

def renderTree (t : ProofTree) : String := treeToString t 0

/-! ### SortInfo construction

To call `Unravel.translate`, each binder needs a `SortInfo` describing
its inductive type + constructors. We introspect the type expression
via Lean.Environment to build it. Ported from `Cyclic.ThmCmd`. -/

/-- Build `CtorInfo` for one constructor of inductive `indName`. -/
def buildCtorInfo (indName : Lean.Name) (typeArgs : Array Lean.Expr)
    (ctorName : Lean.Name)
    : MetaM (Option Unravel.CtorInfo) := do
  let env ← getEnv
  let some ctorConst := env.find? ctorName | return none
  let ctorTypeApplied : Lean.Expr := Id.run do
    let mut t := ctorConst.type
    let mut tas := typeArgs.toList
    while t.isForall && !tas.isEmpty do
      t := t.bindingBody!.instantiate1 tas.head!
      tas := tas.tail
    return t
  Lean.Meta.forallTelescope ctorTypeApplied fun fargs _ => do
    let mut recArgs : List Nat := []
    for h : i in [:fargs.size] do
      let fa := fargs[i]
      let aType ← Lean.Meta.inferType fa
      if let .const n _ := aType.getAppFn then
        if n == indName then recArgs := recArgs ++ [i]
    let shortName := ctorName.toString.splitOn "." |>.getLast!
    return some {
      shortName  := shortName
      fullName   := ctorName.toString
      recArgs    := recArgs
      totalArgs  := fargs.size
    }

/-- Build `SortInfo` for a Lean type expression like `Nat` or `List Nat`. -/
def buildSortInfo (typeExpr : Lean.Expr) : MetaM Unravel.SortInfo := do
  let typeExpr ← Lean.Meta.whnf typeExpr
  let head := typeExpr.getAppFn
  let typeArgs := typeExpr.getAppArgs
  let env ← getEnv
  match head with
  | .const indName _ =>
    match env.find? indName with
    | some (.inductInfo indVal) =>
      let typeStr := (← Lean.Meta.ppExpr typeExpr).pretty
      let mut ctors : List Unravel.CtorInfo := []
      for cn in indVal.ctors do
        if let some ci ← buildCtorInfo indName typeArgs cn then
          ctors := ctors ++ [ci]
      return { typeStr := typeStr, ctors := ctors }
    | _ => throwError "expected an inductive type, got: {typeExpr}"
  | _ => throwError "expected an inductive type head, got: {typeExpr}"

end Build
end CyclicTactic
