import CyclicTactic.PaperAnnotation
import CyclicTactic.ProofTree

/-!
# Theorem 6.1 emission scaffolding

Implements the per-node data structures defined in Grotenhuis-Otten
§6 (definitions on page 10): `cov(b)`, `RelAnc(n_k)`, `Ineq(n_k)`,
`Hyp(n_k)`, and the `σ` substitution from Lemma 6.4. These are
prerequisites for a paper-faithful structural-induction emission
(Theorem 6.1) — a sibling to the ad-hoc string-mashing in
[`CyclicTactic.Unravel`](Unravel.lean).

This module currently provides the data structures and a diagnostic
renderer; the actual emission (Lemma 6.2-6.4 driven) will be added
on top in a follow-up.

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
  /-- Set when this node is a bud; the bud's progressing name and
      its cover. -/
  bud? : Option (String × Name × Name)
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
    let bud? : Option (String × Name × Name) := budAnnot?.bind fun b =>
      progDataFor b |>.map fun (p, c, _) => (lbl, p, c)
    let relAnc := match bud? with
      | some (_, _, c) => relAncOfBud cur c
      | none           => relAncOf cur
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
    | none           => ""
    | some (b, p, c) =>
      "\n  bud: " ++ b ++ "; prog=" ++ Name.pp p ++ "; cov=" ++ Name.pp c
  "node " ++ lbl ++ ":\n  RelAnc: " ++ relAncStr
    ++ "\n  Ineq:   " ++ ineqStr
    ++ "\n  Hyp:    " ++ hypStr ++ budStr

/-- Render the full per-node augmentation as a multi-line block. -/
def renderAug (m : NodeAugMap) : String :=
  if m.isEmpty then "(no nodes)"
  else String.intercalate "\n\n" (m.map fun (lbl, aug) => renderNodeAug lbl aug)

end CyclicTactic.Theorem6
