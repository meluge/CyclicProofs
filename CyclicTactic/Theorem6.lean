import CyclicTactic.PaperAnnotation
import CyclicTactic.ProofTree
import CyclicTactic.EmitCommon

/-!
# Theorem 6.1 emission

Implements the per-node data structures defined in Grotenhuis-Otten
§6 (definitions on page 10): `cov(b)`, `RelAnc(n_k)`, `Ineq(n_k)`,
`Hyp(n_k)`, and the `σ` substitution from Lemma 6.4. On top of these,
`Emit.translate` walks an annotated `ProofTree` and emits a
paper-faithful Lean tactic script (Lemma 6.3 rules + Lemma 6.4 IH
construction).

This module is the canonical emitter for `cyclic_thm`. Shared
script-rendering utilities (`SortInfo`, `CtorInfo`, `termToLean`,
`patToInductionCase`, …) live in [`CyclicTactic.EmitCommon`].

## Vocabulary

The paper distinguishes between *names* (abstract `a_0, a_1, …`,
already implemented in `PaperAnnotation`) and *variables* (the actual
proof-tree slot values, `x_{k,j}` for slot `j` at node `n_k`). A
`var(n_k, a)` is the variable that carries name `a` at node `n_k`.

For our flat-arity setting, "variable" reduces to "slot index": at
each non-back node, the slots are determined by the canonical root
sequent under the path substitution. We represent variable references
with a sum type `RelAncRef` because `RelAnc(n_k)` mixes:
  * named ancestors (`var(n_k, a)`),
  * slot variables (`x_{k,j}`),
  * the cover variable at buds (`x_cov(b)` = `var(b, cov(b))`).

For naming purposes — emitting Lean code — we collapse these to a
human-readable form via the path substitution and root args.
-/

namespace CyclicTactic.Theorem6

open CyclicTactic.PaperAnnotation
open CyclicTactic.Proof

/-! ### Variable references in `RelAnc(n_k)` -/

/-- A reference to a `RelAnc(n_k)` element. The paper treats these
    uniformly as variables; we keep the source-of-introduction
    explicit for emission so we can recover human-readable names. -/
inductive RelAncRef where
  /-- `var(n_k, a)` — the variable named by `a` in `Name(n_k)`. -/
  | named (a : Name)
  /-- `x_{k,j}` — the variable currently occupying slot `j` at this
      node. -/
  | slot (j : Nat)
  /-- `x_cov(b)` — the cover variable at a bud. Expressed as a name
      because cov(b) was a name in `Name(parent)` before the reset. -/
  | cov (a : Name)
  deriving Repr, BEq

namespace RelAncRef

/-- Pretty-print a reference, e.g. for diagnostics. -/
def pp : RelAncRef → String
  | .named a => "var(" ++ Name.pp a ++ ")"
  | .slot j  => "x" ++ toString j
  | .cov a   => "x_cov(" ++ Name.pp a ++ ")"

instance : ToString RelAncRef := ⟨pp⟩

end RelAncRef

/-! ### Inequalities in `Ineq(n_k)`

`Ineq(n_k)` collects:
  * `y > z` for `y, z ∈ RelAnc(n_k)` with `y` a strict ancestor of `z`
    (i.e., `y` occurs strictly before `z` in some `Stack(n_k)_j`);
  * `y ≥ z` for `y ∈ RelAnc(n_k)` an ancestor of `x_{k,j}`, where
    `z = x_{k,j}`.

The order of the list is irrelevant under the exchange rule, so we
emit it in a canonical order (strict first, then nonstrict; lex by
LHS name).
-/

inductive IneqEntry where
  | strict    (y z : RelAncRef)
  | nonstrict (y z : RelAncRef)
  deriving Repr, BEq

namespace IneqEntry

def pp : IneqEntry → String
  | .strict y z    => RelAncRef.pp y ++ " > " ++ RelAncRef.pp z
  | .nonstrict y z => RelAncRef.pp y ++ " ≥ " ++ RelAncRef.pp z

instance : ToString IneqEntry := ⟨pp⟩

end IneqEntry

/-! ### Induction hypotheses in `Hyp(n_k)`

The paper's `hyp_b := ∀x'. (x_{prog(b)} > x'_{prog(b)}) → Ineq[x'/x] →
OldHyp_b[x'/x] → judg(n_k)(x'_k)` carries a lot of structure. For
diagnostics we record the key data — the bud, prog name + slot, and
the OldHyp dependency list — and render the formula on demand. -/

structure HypInfo where
  /-- The bud this `hyp_b` is for. -/
  bud : String
  /-- `prog(b)` — the progressing name. -/
  progName : Name
  /-- The slot of `x_{prog(b)}` at the sprout. (For diagnostics only;
      Hyp's quantification ranges over the sprout's RelAnc, not over
      slots directly.) -/
  progSlotAtSprout : Nat
  /-- The list of buds whose `hyp_{b'}` was in `Hyp` at the time `hyp_b`
      was introduced — i.e., `OldHyp_b` per the paper's algorithm.
      Older-first (per "ordered from old to young"). -/
  oldHypBuds : List String
  deriving Repr

namespace HypInfo

def pp (h : HypInfo) : String :=
  let oldStr :=
    if h.oldHypBuds.isEmpty then "∅"
    else "{" ++ String.intercalate ", " h.oldHypBuds ++ "}"
  s!"hyp_{h.bud}: prog={Name.pp h.progName}@slot{h.progSlotAtSprout}; OldHyp={oldStr}"

instance : ToString HypInfo := ⟨pp⟩

end HypInfo

/-! ### Per-node augmented data -/

/-- The `judgind(n_k)` view: the augmented sequent at this node. -/
structure NodeAug where
  /-- The Stack/Name/Reset annotation (from PaperAnnotation). -/
  annot : NodeAnnot
  /-- `RelAnc(n_k) ⊆ Var(n_k)` — relevant ancestors. For non-bud
      nodes: `{var(n_k, a) | a ∈ Name(n_k)}`. For buds: above plus
      `var(b, cov(b))`. -/
  relAnc : List RelAncRef
  /-- `Ineq(n_k)` — derived from the stack ancestor relation plus the
      slot-ancestor relation. -/
  ineqs : List IneqEntry
  /-- `Hyp(n_k)` — accumulated IHs in scope at this node. -/
  hyps : List HypInfo
  /-- Set when this node is a bud; the bud's label, progressing name,
      cover, and progressing slot index. -/
  bud? : Option (String × Name × Name × Nat)
  deriving Repr

/-! ### Computing RelAnc, Ineq

`RelAnc` and `Ineq` are local: they depend only on the current node's
`NodeAnnot`. For buds, we additionally include `cov(b)`. -/

/-- Compute the strict-ancestor relation on names: `a` is a strict
    ancestor of `a'` iff `a` occurs strictly before `a'` in some
    `Stack(n_k)_j`. -/
def strictAncestor (annot : NodeAnnot) (a a' : Name) : Bool :=
  annot.stacks.any fun s =>
    -- `a` occurs strictly before `a'` iff both are in `s` and `a`'s
    -- index < `a'`'s index.
    match s.idxOf? a, s.idxOf? a' with
    | some i, some i' => i < i'
    | _, _            => false

/-- A name `a` is an ancestor of slot `j` (i.e., of `x_{k,j}`) iff
    `a` occurs anywhere in `Stack(n_k)_j`. -/
def ancestorOfSlot (annot : NodeAnnot) (a : Name) (j : Nat) : Bool :=
  match annot.stacks[j]? with
  | none   => false
  | some s => s.elem a

/-- `RelAnc(n_k)` for a non-bud node: `{var(n_k, a) | a ∈ Name(n_k)}`. -/
def relAncOf (annot : NodeAnnot) : List RelAncRef :=
  annot.names.map RelAncRef.named

/-- `RelAnc(n_k)` for a bud: above plus `var(b, cov(b))`. -/
def relAncOfBud (annot : NodeAnnot) (cov : Name) : List RelAncRef :=
  RelAncRef.cov cov :: relAncOf annot

/-- Compute `Ineq(n_k)`. The slot-ancestor entries point each slot's
    relevant-ancestor names to `x_{k,j}` (a slot-ref). -/
def ineqsOf (annot : NodeAnnot) (relAnc : List RelAncRef) : List IneqEntry :=
  -- Strict entries: y > z for distinct names in stacks.
  let strictEntries : List IneqEntry :=
    annot.names.flatMap fun a =>
      annot.names.filterMap fun a' =>
        if strictAncestor annot a a' && relAnc.elem (.named a)
            && relAnc.elem (.named a') then
          some (.strict (.named a) (.named a'))
        else none
  -- Slot-ancestor entries: y ≥ x_{k,j} for ancestor y of slot j.
  let arity := annot.stacks.length
  let slotEntries : List IneqEntry :=
    annot.names.flatMap fun a =>
      (List.range arity).filterMap fun j =>
        if ancestorOfSlot annot a j && relAnc.elem (.named a) then
          some (.nonstrict (.named a) (.slot j))
        else none
  strictEntries ++ slotEntries

/-! ### Computing Hyp

`Hyp(n_k)` is path-dependent: it accumulates IHs as we descend through
sprouts. We compute it during a top-down walk that mirrors the
annotation walk in `annotateTreeAux`.

For our setting, we identify *sprouts* as the nodes that are referenced
by some back-edge's `ancestor` field. The walk:
  * starts with `Hyp = []`;
  * at each sprout (= node whose label appears as the `ancestor` of
    some bud below), introduces a `hyp_b` for each bud `b` whose
    sprout this node is.
  * at each non-sprout node, propagates `Hyp` unchanged from the
    parent.

The "remove buds not reachable from `n_k`" step (Def 6.1's Hyp
algorithm) is implicit: we only add `hyp_b` *at the sprout of b*, so
descendants of that sprout naturally see it; siblings don't.
-/

/-- All `(bud, ancestor)` pairs in the proof tree. Used to identify
    which nodes act as sprouts. -/
def collectBuds (t : ProofTree) : List (String × String) := t.backEdges

/-- Is `label` a sprout (the ancestor of any back-edge)? -/
def isSprout (label : String) (buds : List (String × String)) : Bool :=
  buds.any (fun (_, anc) => anc == label)

/-- The buds whose sprout is this node. -/
def budsAtSprout (label : String) (buds : List (String × String))
    : List String :=
  buds.filterMap (fun (b, anc) => if anc == label then some b else none)

/-! ### Building per-node `NodeAug`

Walks the tree like `annotateTreeAux` but additionally tracks
`Hyp(n_k)` along the path. Returns one `NodeAug` per node visited,
keyed by the node's label. (Labels are unique by construction in our
event-stream-built trees.) -/

/-- Per-node augmented info, keyed by node label. Order matches DFS
    visit order. -/
abbrev NodeAugMap := List (String × NodeAug)

/-- Look up the bud's information from a per-bud annotation: prog
    name, prog slot at *bud* (we map back to sprout slot via the
    bud's stacks lookup). -/
def progDataFor (b : BudAnnot) : Option (Name × Name × Nat) := do
  let progName ← b.progName?
  let cov ← b.budAnnot.cov? progName
  let progSlot ← b.progSlot?
  return (progName, cov, progSlot)

/-- Compute `NodeAug` for every node along the walk. The walk threads
    `Hyp` and the budAnnot lookup map. -/
partial def computeAugAux
    (rootArgs : List SubjectTerm)
    (cur : NodeAnnot)
    (σp : Subst)
    (hyps : List HypInfo)
    (buds : List (String × String))
    (budAnnots : List BudAnnot)
    : ProofTree → NodeAugMap
  | .leaf lbl _ _ _ =>
    [(lbl, { annot := cur, relAnc := relAncOf cur,
             ineqs := ineqsOf cur (relAncOf cur), hyps := hyps,
             bud? := none })]
  | .identity lbl _ =>
    [(lbl, { annot := cur, relAnc := relAncOf cur,
             ineqs := ineqsOf cur (relAncOf cur), hyps := hyps,
             bud? := none })]
  | .node lbl _ _ children =>
    let hyps' := hypsAtSprout lbl hyps buds budAnnots
    let aug : NodeAug :=
      { annot := cur, relAnc := relAncOf cur,
        ineqs := ineqsOf cur (relAncOf cur), hyps := hyps',
        bud? := none }
    let here : NodeAugMap := [(lbl, aug)]
    let descendants := children.flatMap fun child =>
      let σc := σp
      let parentSlots := rootArgs.map (SubjectTerm.subst σc)
      let childSlots := effectiveSlots rootArgs σc child
      let g := edgeSCG parentSlots childSlots
      let cur' := step cur g
      computeAugAux rootArgs cur' σc hyps' buds budAnnots child
    here ++ descendants
  | .caseSplit lbl _ var arms =>
    let hyps' := hypsAtSprout lbl hyps buds budAnnots
    let aug : NodeAug :=
      { annot := cur, relAnc := relAncOf cur,
        ineqs := ineqsOf cur (relAncOf cur), hyps := hyps',
        bud? := none }
    let here : NodeAugMap := [(lbl, aug)]
    let descendants := arms.flatMap fun (pat, sub) =>
      let σc := (var, pat) :: σp
      let parentSlots := rootArgs.map (SubjectTerm.subst σc)
      let childSlots := effectiveSlots rootArgs σc sub
      let g := edgeSCG parentSlots childSlots
      let cur' := step cur g
      computeAugAux rootArgs cur' σc hyps' buds budAnnots sub
    here ++ descendants
  | .haveStep lbl _ _ _ _ cont =>
    let hyps' := hypsAtSprout lbl hyps buds budAnnots
    let aug : NodeAug :=
      { annot := cur, relAnc := relAncOf cur,
        ineqs := ineqsOf cur (relAncOf cur), hyps := hyps',
        bud? := none }
    let σc := σp
    let parentSlots := rootArgs.map (SubjectTerm.subst σc)
    let childSlots := effectiveSlots rootArgs σc cont
    let g := edgeSCG parentSlots childSlots
    let cur' := step cur g
    (lbl, aug) :: computeAugAux rootArgs cur' σc hyps' buds budAnnots cont
  | .existsStep lbl _ _ cont =>
    let hyps' := hypsAtSprout lbl hyps buds budAnnots
    let aug : NodeAug :=
      { annot := cur, relAnc := relAncOf cur,
        ineqs := ineqsOf cur (relAncOf cur), hyps := hyps',
        bud? := none }
    let σc := σp
    let parentSlots := rootArgs.map (SubjectTerm.subst σc)
    let childSlots := effectiveSlots rootArgs σc cont
    let g := edgeSCG parentSlots childSlots
    let cur' := step cur g
    (lbl, aug) :: computeAugAux rootArgs cur' σc hyps' buds budAnnots cont
  | .back lbl _ _ _ _ =>
    let budAnnot? := budAnnots.find? (·.bud == lbl)
    let bud? : Option (String × Name × Name × Nat) := budAnnot?.bind fun b =>
      progDataFor b |>.map fun (p, c, s) => (lbl, p, c, s)
    let relAnc := match bud? with
      | some (_, _, c, _) => relAncOfBud cur c
      | none              => relAncOf cur
    [(lbl, { annot := cur, relAnc := relAnc,
             ineqs := ineqsOf cur relAnc, hyps := hyps, bud? := bud? })]
where
  /-- At a sprout: extend `hyps` with one `hyp_b` per bud whose sprout
      is this node, ordered older-first. Per Def 6.1's algorithm, each
      `hyp_b` snapshots `Hyp(n_k)` *at the moment of its introduction*
      as `OldHyp_b` — so for hyps introduced later in the same sprout
      pass, `OldHyp` includes the earlier ones.

      We use input order as the age proxy. (Multi-companion proofs
      with truly distinct ages would need the Lemma 5.9 ordering;
      single-companion proofs have all same-sprout buds at equal age,
      where any deterministic order is acceptable per Def 6.1's
      footnote.) -/
  hypsAtSprout (label : String) (hyps : List HypInfo)
      (buds : List (String × String)) (budAnnots : List BudAnnot)
      : List HypInfo :=
    let mySprout := budsAtSprout label buds
    mySprout.foldl (init := hyps) fun running budLbl =>
      match budAnnots.find? (·.bud == budLbl) |>.bind fun b => do
              let progName ← b.progName?
              let progSlot ← b.progSlot?
              return (progName, progSlot) with
      | none => running
      | some (progName, progSlot) =>
        running ++ [{ bud := budLbl, progName := progName,
                      progSlotAtSprout := progSlot,
                      oldHypBuds := running.map (·.bud) }]

/-- Top-level: compute per-node augmented info for the whole tree. -/
def computeAug (t : ProofTree) : NodeAugMap :=
  let rootArgs := Sequent.flatArgs t.sequent
  let cur0 := NodeAnnot.root rootArgs.length
  let buds := collectBuds t
  let budAnnots := annotateTree t
  computeAugAux rootArgs cur0 [] [] buds budAnnots t

/-! ### Diagnostic rendering -/

/-- Render a per-node augmented info entry as a multi-line block. -/
def renderNodeAug (lbl : String) (aug : NodeAug) : String :=
  let relAncStr :=
    if aug.relAnc.isEmpty then "∅"
    else "{" ++ String.intercalate ", " (aug.relAnc.map RelAncRef.pp) ++ "}"
  let ineqStr :=
    if aug.ineqs.isEmpty then "∅"
    else String.intercalate ", " (aug.ineqs.map IneqEntry.pp)
  let hypStr :=
    if aug.hyps.isEmpty then "∅"
    else String.intercalate "; " (aug.hyps.map HypInfo.pp)
  let budStr := match aug.bud? with
    | none              => ""
    | some (b, p, c, s) =>
      "\n  bud: " ++ b ++ "; prog=" ++ Name.pp p ++ " (slot " ++ toString s ++ ")"
        ++ "; cov=" ++ Name.pp c
  "node " ++ lbl ++ ":\n  RelAnc: " ++ relAncStr
    ++ "\n  Ineq:   " ++ ineqStr
    ++ "\n  Hyp:    " ++ hypStr ++ budStr

/-- Render the full per-node augmentation as a multi-line block. -/
def renderAug (m : NodeAugMap) : String :=
  if m.isEmpty then "(no nodes)"
  else String.intercalate "\n\n" (m.map fun (lbl, aug) => renderNodeAug lbl aug)

/-! ### Paper-faithful emission (Lemma 6.2-6.4 + Theorem 6.1)

Emits a Lean tactic script driven by the §6 data structures. The
decisions about *where to introduce inductions* and *what to
substitute at IH calls* come directly from the augmented annotation:

  * **Sprout-driven inductions** (Theorem 6.1's `>-ind'_x_prog` step):
    a node is a sprout iff its `aug.hyps` extends the parent's
    `aug.hyps`. For each new hyp introduced here, emit one
    `induction <var-of-prog> generalizing <rest-of-RelAnc-vars> with`.

  * **Rule applications** (Lemma 6.3): each non-sprout internal node
    emits the corresponding C-rule (`cases` for caseSplit, `refine`
    for branch nodes, `have` / `refine` for cut/exists steps).

  * **IH applications at buds** (Lemma 6.4): the σ from the lemma
    maps `x_{s,j} ↦ x_{t,j}` (sprout slot j → bud slot j),
    `x_prog ↦ x_cov`, identity otherwise. In our flat-arity setting
    with companion = root, this reduces to the bud's literal slot
    values for `rest` and `ih_<recursive-subterm>` for the IH name.
-/

namespace Emit

open CyclicTactic.EmitCommon  -- pad, reindent, defaultSimp, termToLean,
                              -- SortInfo, CtorInfo, patToInductionCase

/-- Look up which root-var occupies a given slot. In our flat-arity
    model, `rootArgs[slot]` is the var (or constant) that "named" that
    slot at the root. -/
def varAtSlot (rootArgs : List SubjectTerm) (slot : Nat) : Option String :=
  match rootArgs[slot]? with
  | some (.var v) => some v
  | _             => none

/-- Name the IH bound by Lean's `induction var with` for the arm
    `pat`. For a single-recursive constructor (e.g. `Nat.succ n'`) the
    IH is `ih_<recVar>`. For multi-recursive (e.g. `BTr.node l r`)
    Lean introduces multiple IHs (`ih_l`, `ih_r`); the bud's `σ_back`
    selects which by naming the recursive subterm.

    `σ_back`'s mapping for the prog slot tells us which recursive
    subterm we're recursing on — that subterm's var name is the IH's
    suffix. -/
def ihNameForBud (σ_back : Subst) (progSlot : Nat)
    (rootArgs : List SubjectTerm) : Option String := do
  let progVar ← varAtSlot rootArgs progSlot
  match σ_back.lookup progVar with
  | some (.var recVar) => return "ih_" ++ recVar
  | _                  => none

/-- The σ-applied rest-of-args for an IH call. Per Lemma 6.4, σ maps
    sprout slot vars to bud slot vars. For Lean's `induction var
    generalizing rest with`, the IH takes `rest`-many arguments — we
    supply the σ-substituted values for each, which equals the bud's
    literal slot value at that position. -/
def ihRestArgs (sorts : List SortInfo) (progSlot : Nat)
    (budSlots : List SubjectTerm) : List String :=
  budSlots.zipIdx.filterMap fun (slotVal, j) =>
    if j == progSlot then none  -- prog slot's value comes from the case-pat
    else some (termToLean sorts slotVal)

/-- Header for a `cases` arm — constructor + bound arg vars, no IH
    names. Mirrors `patToInductionCase` but drops the trailing IH
    binders since `cases` doesn't bind any. -/
def patToCasesHeader (sortInfo : SortInfo) (pat : SubjectTerm) : Option String :=
  match pat with
  | .ctor cname patArgs =>
    match sortInfo.ctors.find? (·.shortName == cname) with
    | none => none
    | some ci =>
      let argVars := patArgs.filterMap fun
        | .var n => some n
        | _      => none
      if argVars.length != patArgs.length || argVars.length != ci.totalArgs then none
      else
        let argsStr :=
          if argVars.isEmpty then ""
          else " " ++ String.intercalate " " argVars
        some (ci.shortName ++ argsStr)
  | _ => none

/-! ### The emit walker

State threaded through the recursion:
  * `parentHyps` — names of hyps in scope from the parent's
    `aug.hyps` (used to detect sprout introductions).
  * `pathBudIH` — for each enclosing sprout, a map from arm-pat to
    the IH name Lean bound there. Buds use this to choose `ih_<var>`.

For Phase 1 we restrict to single-companion proofs (companion = root),
so every bud's sprout is the root and we just need to track the
root's induction var(s).
-/

/-- Slot-info bundle: per-slot (var name + sort info), plus `rootArgs`
    for ancestor lookups. -/
structure EmitCtx where
  rootArgs : List SubjectTerm
  varSorts : List (String × SortInfo)
  defaultSimpPred : Option String
  augMap : NodeAugMap

partial def emitTree (ctx : EmitCtx) (depth : Nat) (parentHyps : List String)
    : ProofTree → String
  | .leaf _ _ _ closeTac =>
    let body := closeTac.getD (defaultSimp ctx.defaultSimpPred)
    pad depth ++ reindent depth body
  | .identity _ _ =>
    pad depth ++ "assumption"
  | .node lbl _ rule children =>
    let aug? := ctx.augMap.lookup lbl
    let myHyps := (aug?.map (·.hyps.map (·.bud))).getD []
    let newHyps := myHyps.filter (fun h => !parentHyps.elem h)
    -- A `.node "branch"` introduces a multi-rec branch (refine ⟨…⟩).
    -- New hyps shouldn't typically appear here in our tree shape;
    -- the sprout is usually the enclosing caseSplit.
    let _ := newHyps
    if rule == "branch" then
      -- Multi-rec branch: a `.node "branch"` typically wraps multiple
      -- back-edges (one per recursive subterm of the enclosing
      -- caseSplit's pattern). Emission shape: `simp [pred]; refine ⟨?_,
      -- ?_⟩; · child0; · child1`. Each child is rendered via the same
      -- emitTree machinery so .back children get correct `ih_<var>
      -- <args>` calls per Lemma 6.4.
      let prelude := defaultSimp ctx.defaultSimpPred
      let qmarks := String.intercalate ", " (children.map (fun _ => "?_"))
      let bodies := children.map fun child =>
        let inner := emitTree ctx (depth + 1) parentHyps child
        pad depth ++ "·\n" ++ inner
      pad depth ++ prelude ++ "\n"
        ++ pad depth ++ "refine ⟨" ++ qmarks ++ "⟩\n"
        ++ String.intercalate "\n" bodies
    else
      -- Generic single-child node (unfold/etc).
      pad depth ++ defaultSimp ctx.defaultSimpPred ++ "\n"
        ++ String.intercalate "\n"
            (children.map (emitTree ctx depth parentHyps))
  | .caseSplit lbl _ var arms =>
    let aug? := ctx.augMap.lookup lbl
    let myHyps := (aug?.map (·.hyps.map (·.bud))).getD []
    let newHyps := myHyps.filter (fun h => !parentHyps.elem h)
    -- Determine if this caseSplit is also a sprout (introduces hyps).
    -- If so, emit `induction var generalizing rest with` per Theorem 6.1.
    -- Otherwise, emit `cases var with` per Lemma 6.3's rule application.
    let isSproutHere := !newHyps.isEmpty
    let sortInfo? := ctx.varSorts.lookup var
    -- `induction` arms bind IHs (`succ n' ih_n'`); `cases` arms don't
    -- (`succ n'`). Pick the header builder per emission mode.
    let armsBody : List String := arms.filterMap fun (pat, sub) =>
      match sortInfo? with
      | none => some (pad depth ++ "| _ => sorry /- no sort info for '"
                       ++ var ++ "' -/")
      | some sortInfo =>
        let header? : Option String :=
          if isSproutHere then
            (patToInductionCase sortInfo pat).map (·.1)
          else
            patToCasesHeader sortInfo pat
        match header? with
        | none => none
        | some header =>
          let body := emitTree ctx (depth + 1) myHyps sub
          some (pad depth ++ "| " ++ header ++ " =>\n" ++ body)
    if isSproutHere then
      -- Generalizing list: all root vars except `var` itself, in
      -- declaration order. Drives the IH's quantification per Lemma 6.4.
      let genVars := ctx.varSorts.map (·.1) |>.filter (· != var)
      let genClause :=
        if genVars.isEmpty then ""
        else " generalizing " ++ String.intercalate " " genVars
      pad depth ++ "induction " ++ var ++ genClause ++ " with\n"
        ++ String.intercalate "\n" armsBody
    else
      pad depth ++ "cases " ++ var ++ " with\n"
        ++ String.intercalate "\n" armsBody
  | .back lbl bSeq _ σ_back closeTac =>
    -- Look up the bud's prog slot from the augmented map. This was
    -- recorded during `computeAug` and reflects the final converged
    -- annotation (post-Lemma-5.9 unfolding when needed).
    let aug? := ctx.augMap.lookup lbl
    let progSlot : Nat :=
      match aug?.bind (·.bud?) with
      | some (_, _, _, s) => s
      | none              => 0  -- defensive: shouldn't happen for well-formed buds
    let sorts := ctx.varSorts.map (·.2)
    let ihName := match ihNameForBud σ_back progSlot ctx.rootArgs with
      | some s => s
      | none   => "ih_?"
    let budSlots := bSeq.succedents.flatMap (·.args)
    let restArgs := ihRestArgs sorts progSlot budSlots
    let restStr := if restArgs.isEmpty then "" else " " ++ String.intercalate " " restArgs
    let exactStmt := "exact " ++ ihName ++ restStr
    match closeTac with
    | none     => pad depth ++ exactStmt
    | some tac =>
      let withIH := tac.replace "recurse" exactStmt
      pad depth ++ reindent depth withIH
  | .haveStep _ _ haveName haveTypeStr haveProofStr cont =>
    pad depth ++ "have " ++ haveName ++ " : " ++ haveTypeStr ++ " := by\n"
      ++ pad (depth + 1) ++ reindent (depth + 1) haveProofStr ++ "\n"
      ++ emitTree ctx depth parentHyps cont
  | .existsStep _ _ witnessStr cont =>
    pad depth ++ "refine ⟨" ++ witnessStr ++ ", ?_⟩\n"
      ++ emitTree ctx depth parentHyps cont

/-- Top-level paper-faithful emission. Builds the theorem header from
    the supplied metadata and emits the body via `emitTree`.

    `goalType` is the user-visible goal type as a string (the caller
    builds it from the `cyclic_thm` syntax). `varSorts` lists the root
    variables in positional order with their sort info. -/
def translate (defaultSimpPred : Option String) (goalType thmName : String)
    (varSorts : List (String × SortInfo)) (t : ProofTree) : String :=
  let augMap := computeAug t
  let rootArgs := Sequent.flatArgs t.sequent
  let ctx : EmitCtx :=
    { rootArgs := rootArgs
      varSorts := varSorts
      defaultSimpPred := defaultSimpPred
      augMap := augMap }
  let bindings := varSorts.map fun (v, si) => "(" ++ v ++ " : " ++ si.typeStr ++ ")"
  let header := "theorem " ++ thmName ++ " " ++ String.intercalate " " bindings
                  ++ " : " ++ goalType ++ " := by"
  header ++ "\n" ++ emitTree ctx 1 [] t

/-! ### Mutual-block emission

For `cyclic_mutual` blocks, every bud is cross-theorem: its `ancestor`
label is a sibling entry's companion, not a node in the same tree.
The §6 within-tree machinery (sprouts, IH binding, `induction`) doesn't
apply — instead each bud emits as `exact <sibling-thm-name> <σ-args>`,
relying on Lean's mutual termination check to validate that the call
is structurally smaller.

`computeAug` is *not* called per-entry because cross-theorem buds make
`annotateTree`'s Lemma 5.9 unfolding fail to converge (the fixpoint
iteration doesn't terminate when the bud's ancestor isn't in the
tree's ancestor stack). Skipping aug is safe here because the mutual
case doesn't need sprout-driven `induction`; the inductive content
lives in Lean's mutual recursion check.

Entries are emitted as `def` (not `theorem`) because cross-theorem
calls *are* recursive at the Lean level; `theorem` would reject. -/

/-- One entry in a `cyclic_mutual` block. Carries the data the emitter
    needs to produce its `def` body. -/
structure MutualEntry where
  thmName : String
  /-- The entry's flat binders (var-name × pretty-printed type). -/
  binders : List (String × String)
  /-- The user's goal type, as printed source. -/
  goalType : String
  /-- The per-entry proof tree from event demux. -/
  tree : ProofTree
  /-- Sort info per binder, for rendering bud args via `termToLean`. -/
  varSorts : List (String × SortInfo)
  deriving Inhabited

/-- Mutual emit context. Carries the cross-companion table so `.back`
    nodes can route to the right sibling. -/
structure MutualEmitCtx where
  varSorts : List (String × SortInfo)
  defaultSimpPred : Option String
  /-- `label → (sibling-thm-name, sibling-binder-vars)`. A bud whose
      `.back` ancestor matches a key here emits as
      `exact <thm-name> <σ-args>`. -/
  companionMap : List (String × String × List String)

/-- Walk a per-entry tree, emitting a Lean tactic script. Mirrors
    `emitTree` but routes `.back` to cross-theorem `exact` calls
    instead of in-tree IH applications. All case-splits emit as
    `cases` (no sprout detection — there's no within-tree induction
    to drive). -/
partial def emitMutualTree (ctx : MutualEmitCtx) (depth : Nat)
    : ProofTree → String
  | .leaf _ _ _ closeTac =>
    let body := closeTac.getD (defaultSimp ctx.defaultSimpPred)
    pad depth ++ reindent depth body
  | .identity _ _ =>
    pad depth ++ "assumption"
  | .node _ _ rule children =>
    if rule == "branch" then
      let prelude := defaultSimp ctx.defaultSimpPred
      let qmarks := String.intercalate ", " (children.map (fun _ => "?_"))
      let bodies := children.map fun child =>
        let inner := emitMutualTree ctx (depth + 1) child
        pad depth ++ "·\n" ++ inner
      pad depth ++ prelude ++ "\n"
        ++ pad depth ++ "refine ⟨" ++ qmarks ++ "⟩\n"
        ++ String.intercalate "\n" bodies
    else
      pad depth ++ defaultSimp ctx.defaultSimpPred ++ "\n"
        ++ String.intercalate "\n"
            (children.map (emitMutualTree ctx depth))
  | .caseSplit _ _ var arms =>
    let sortInfo? := ctx.varSorts.lookup var
    let armsBody : List String := arms.filterMap fun (pat, sub) =>
      match sortInfo? with
      | none => some (pad depth ++ "| _ => sorry /- no sort info for '"
                       ++ var ++ "' -/")
      | some sortInfo =>
        match patToCasesHeader sortInfo pat with
        | none => none
        | some header =>
          let body := emitMutualTree ctx (depth + 1) sub
          some (pad depth ++ "| " ++ header ++ " =>\n" ++ body)
    pad depth ++ "cases " ++ var ++ " with\n"
      ++ String.intercalate "\n" armsBody
  | .back _ bSeq anc _ closeTac =>
    -- Cross-theorem bud: look up the ancestor label in companionMap.
    -- The sibling-binder-vars list tells us how many args the call
    -- needs and which slots; we read them positionally from bSeq.
    match ctx.companionMap.find? (·.1 == anc) with
    | none =>
      pad depth ++ "sorry /- cyclic_mutual: no companion '" ++ anc ++ "' -/"
    | some (_, siblingName, _) =>
      let sorts := ctx.varSorts.map (·.2)
      let argTerms := bSeq.succedents.flatMap (·.args)
      let argsStr := argTerms.map (termToLean sorts)
      let exactStmt :=
        "exact " ++ siblingName ++ " " ++ String.intercalate " " argsStr
      match closeTac with
      | none     => pad depth ++ exactStmt
      | some tac =>
        let withCall := tac.replace "recurse" exactStmt
        pad depth ++ reindent depth withCall
  | .haveStep _ _ haveName haveTypeStr haveProofStr cont =>
    pad depth ++ "have " ++ haveName ++ " : " ++ haveTypeStr ++ " := by\n"
      ++ pad (depth + 1) ++ reindent (depth + 1) haveProofStr ++ "\n"
      ++ emitMutualTree ctx depth cont
  | .existsStep _ _ witnessStr cont =>
    pad depth ++ "refine ⟨" ++ witnessStr ++ ", ?_⟩\n"
      ++ emitMutualTree ctx depth cont

/-- Top-level mutual-block emission. Produces a `mutual\n…\nend`
    block where each entry is rendered as a `def` with a body emitted
    by `emitMutualTree`. -/
def translateMutual (defaultSimpPred : Option String)
    (entries : List MutualEntry)
    (companionMap : List (String × String × List String)) : String :=
  let entryDefs := entries.map fun e =>
    let ctx : MutualEmitCtx :=
      { varSorts := e.varSorts
        defaultSimpPred := defaultSimpPred
        companionMap := companionMap }
    let bindings := e.binders.map fun (v, ty) => "(" ++ v ++ " : " ++ ty ++ ")"
    let header := "def " ++ e.thmName ++ " " ++ String.intercalate " " bindings
                    ++ " : " ++ e.goalType ++ " := by"
    header ++ "\n" ++ emitMutualTree ctx 1 e.tree
  "mutual\n" ++ String.intercalate "\n" entryDefs ++ "\nend"

end Emit

end CyclicTactic.Theorem6
