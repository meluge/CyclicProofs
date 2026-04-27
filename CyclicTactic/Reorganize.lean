import CyclicTactic.ProofTree

/-!
# Proof-tree reorganisation

Inspired by Grotenhuis-Otten Proposition 5.8 ("we may permute the
order of induction") and Wehr 2025 PhD thesis Ch. 7 (CHA< unravelling,
which similarly restructures sprout/bud nesting). The actual algorithm
below is original: a bubble-sort over adjacent case-splits driven by the
desired induction order, plus a separate back-edge retargeting pass keyed
by descending variable. Neither paper specifies a concrete algorithm at
this level — they assert the transformation exists; we implement one.

Swap adjacent case-splits in a cyclic proof to match a desired induction
order on variables. When a user writes case-splits in an order that
doesn't match the order the annotation's greedy-lex synthesis requires,
this pass restructures the tree so the structural emitter can proceed.

## Scope

This is a *minimal* viable version of the paper's reorganisation. It
handles:

  * Uniformly structured case-splits: every arm of the outer case-split
    is a case-split on the same inner variable, with the same set of
    inner patterns.
  * Single-recursive inductive types (Nat, List, etc.). Multi-recursive
    constructors (e.g. `BinTree.node l r` that binds two IHs) are not
    handled — the swap transformation would need to duplicate IH routing
    and is out of scope here.
  * Arbitrary-depth trees via bubble-sort: repeatedly swap adjacent
    levels until the desired variable is at the top, then recurse into
    each arm.

When the tree doesn't fit these assumptions (non-uniform branches, a
leaf where a case-split was expected, etc.) the pass returns the tree
unchanged; the dispatcher then falls through to WF emission.

## Algorithm: the swap

Given outer `caseSplit lbl_o v_o [(pat_o_k, caseSplit lbl_i_k v_i arms_i_k)]`
where every `arms_i_k` has the same patterns `[pat_i_1, ..., pat_i_m]`,
produce `caseSplit lbl_o' v_i [(pat_i_j, caseSplit lbl_i_j' v_o [(pat_o_k, body_kj)])]`.

## Back-edge label rewiring

The transformation breaks the identity of case-split labels. We rewire
back-edge `ancestor` labels in two passes:

  1. **Uniform remap** (global): every old inner label `lbl_i_k` becomes
     the single new outer label `lbl_o'` (the inner case-splits collapse
     into one outer one on the inner variable).
  2. **Position-dependent remap** (scoped): the old outer label `lbl_o`
     becomes the appropriate new inner label `lbl_i_j'` — which one
     depends on which `pat_i_j` subtree the back-edge sits in.

The position-dependent remap is realised by walking the new outer's
arms; inside each arm's subtree, we apply a per-arm remap that maps
`lbl_o → lbl_i_j'`.

## Sequent recomputation

New case-split sequents are computed by substituting the relevant
variable in the original outer's sequent. Body sequents are unchanged
(they already reflect both substitutions).
-/

namespace CyclicTactic.Reorganize

open CyclicTactic.Proof

/-! ### Fresh label generation -/

abbrev FreshM := StateM Nat

def fresh (pfx : String) : FreshM String := do
  let n ← get
  set (n + 1)
  return "_" ++ pfx ++ toString n ++ "_RG"

/-! ### Label remapping in a proof tree -/

/-- Walk the tree and apply `remap` to every back-edge's ancestor label.
    All other structure is preserved. -/
partial def remapBacks (remap : String → String) : ProofTree → ProofTree
  | .leaf l s j t        => .leaf l s j t
  | .identity l s        => .identity l s
  | .node l s r cs       => .node l s r (cs.map (remapBacks remap))
  | .caseSplit l s v cs  => .caseSplit l s v (cs.map fun (p, t) => (p, remapBacks remap t))
  | .back l s anc σ t    => .back l s (remap anc) σ t
  | .haveStep l s n ty pf cont => .haveStep l s n ty pf (remapBacks remap cont)
  | .existsStep l s w cont    => .existsStep l s w (remapBacks remap cont)

/-! ### Helpers -/

def topVar : ProofTree → Option String
  | .caseSplit _ _ v _ => some v
  | _                  => none

def patEq (a b : SubjectTerm) : Bool := SubjectTerm.structEq a b

/-- Substitute a variable inside a sequent. -/
def seqSubst (σ : Subst) (s : Sequent) : Sequent :=
  { antecedents := s.antecedents.map (Formula.subst σ)
    succedents  := s.succedents.map (Formula.subst σ) }

/-! ### The swap transformation

Original. The swap can handle two shapes for an outer arm's body,
captured by `InnerStructure`:

  * `.single` — the arm's body is a *direct* case-split on the inner
    variable. This is the common shape for single-recursive constructors
    (e.g. `Nat.succ x'`, `List.cons x xs'`).
  * `.branch` — the arm's body is a *multi-recursive* `branch` step
    (`.node "branch" children`) whose every child is itself a case-split
    on the same inner variable. This handles the case where the outer
    constructor binds multiple recursive args (e.g. `BinTree.node l r`)
    AND each branch slot independently case-splits on the inner var.

The swap output preserves these structures: per inner pat, we build a
new inner case-split whose body at each outer pat is either a direct
body (from `.single`) or a `.node "branch" …` re-built from the
original branch's children at the matching inner pat (from `.branch`).

Outer arms whose body is *neither* — e.g. a leaf, a back-edge, or a
branch whose children aren't case-splits on the inner var — are not
supported; reorganisation falls through to WF emission for trees with
those shapes.
-/

/-- The structure of an outer arm's body, classified for the swap. -/
inductive InnerStructure
  /-- Body is a direct case-split: `caseSplit lbl_i _ v_i arms_i`. -/
  | single (lbl_i : String) (arms_i : List (SubjectTerm × ProofTree))
  /-- Body is `.node "branch"` whose every child is a case-split on the
      shared inner var. `slots` lists, per branch child, its own caseSplit
      label and arms. -/
  | branch (lbl_b : String) (slots : List (String × List (SubjectTerm × ProofTree)))

/-- Get the InnerStructure's inner-variable patterns (whichever shape). -/
def InnerStructure.innerPats : InnerStructure → List SubjectTerm
  | .single _ arms => arms.map (·.1)
  | .branch _ slots => match slots with
                      | []          => []
                      | (_, a) :: _ => a.map (·.1)

/-- For the simpler shape — every arm's first thing is a case-split on
    `v_i`. Returns the corresponding inner case-splits, or none. -/
def determineInnerVar : ProofTree → Option String
  | .caseSplit _ _ v _ => some v
  | .node _ _ "branch" children =>
    match children with
    | first :: _ => determineInnerVar first
    | []         => none
  | _ => none

/-- Extract the inner structure of one outer arm with respect to a fixed
    inner variable. -/
def extractInnerStructure (v_i : String) : ProofTree → Option InnerStructure
  | .caseSplit lbl _ v arms =>
    if v == v_i then some (.single lbl arms) else none
  | .node lbl _ "branch" children =>
    let rec go : List ProofTree → Option (List (String × List (SubjectTerm × ProofTree)))
      | [] => some []
      | child :: rest =>
        match child with
        | .caseSplit lbl_c _ v arms_c =>
          if v != v_i then none
          else (go rest).map (fun acc => (lbl_c, arms_c) :: acc)
        | _ => none
    (go children).map (fun slots => .branch lbl slots)
  | _ => none

/-- Check that two pat lists are structurally equal in length and content. -/
def patsMatch (xs ys : List SubjectTerm) : Bool :=
  xs.length == ys.length
    && (xs.zip ys).all (fun (x, y) => patEq x y)

/-- Extract per-outer-arm `InnerStructure`. Verifies all arms agree on
    `v_i` and on the set of inner pats (uniform). -/
def extractUniform
    (arms_o : List (SubjectTerm × ProofTree))
    : Option (String × List SubjectTerm
              × List (SubjectTerm × InnerStructure)) :=
  match arms_o with
  | [] => none
  | (_, sub_first) :: _ =>
    match determineInnerVar sub_first with
    | none => none
    | some v_i =>
      let extracted_arms? : Option (List (SubjectTerm × InnerStructure)) :=
        let rec go : List (SubjectTerm × ProofTree)
                    → Option (List (SubjectTerm × InnerStructure))
          | []                   => some []
          | (pat_o, sub) :: rest =>
            match extractInnerStructure v_i sub with
            | none      => none
            | some inner => (go rest).map (fun acc => (pat_o, inner) :: acc)
        go arms_o
      match extracted_arms? with
      | none => none
      | some extracted_arms =>
        -- All InnerStructures must agree on inner pats (uniform).
        let inner_pats := match extracted_arms with
                          | (_, s) :: _ => s.innerPats
                          | []          => []
        if extracted_arms.all (fun (_, s) => patsMatch s.innerPats inner_pats)
        then some (v_i, inner_pats, extracted_arms)
        else none

/-- Try to swap the top two case-splits of `t`. Returns `none` if the
    structure isn't uniform.

    Bodies are moved verbatim — back-edge `anc` labels are *not* rewired
    here; that's done by `retargetBacks` afterward, which rewires based
    on the back-edge's descending variable rather than its old label.
    A naive label-remap is unsound: a back-edge descending on `x` that
    originally targeted the outer cases-on-y must, after the swap,
    target the cases-on-x ancestor (now the outer level), not the
    cases-on-y (now nested). The descending-variable retargeting handles
    this; a simple label remap can't. -/
def swapAdjacent (t : ProofTree) : FreshM (Option ProofTree) := do
  match t with
  | .caseSplit _ seq_o v_o arms_o =>
    match extractUniform arms_o with
    | none => return none
    | some (v_i, inner_pats, extracted) =>
      let lbl_o_new ← fresh "Ro"
      -- Build one new outer arm per inner pat.
      let rec buildArms : List SubjectTerm → FreshM (List (SubjectTerm × ProofTree))
        | []             => return []
        | pat_i :: rest  => do
          let lbl_i_new ← fresh "Ri"
          -- For each outer pat, extract the body at this inner pat. The
          -- shape depends on the arm's InnerStructure: `.single` →
          -- direct body lookup; `.branch` → re-build a `.node "branch"`
          -- whose children are extracted from each original branch slot
          -- at this same `pat_i`.
          let inner_arms : List (SubjectTerm × ProofTree) := extracted.map
            fun (pat_o, inner) =>
              let body := match inner with
                | .single _ arms_i =>
                  match arms_i.find? (fun (p, _) => patEq p pat_i) with
                  | some (_, b) => b
                  | none        => .leaf "_MISSING_RG" default "uniformity violated" none
                | .branch lbl_b slots =>
                  let new_children : List ProofTree := slots.map fun (_, arms_c) =>
                    match arms_c.find? (fun (p, _) => patEq p pat_i) with
                    | some (_, b) => b
                    | none        => .leaf "_MISSING_RG" default "uniformity violated" none
                  -- Re-use the original branch's label and a fresh
                  -- per-position sequent (path subst applies pat_o + pat_i).
                  let seq_b_new := seqSubst [(v_o, pat_o), (v_i, pat_i)] seq_o
                  .node lbl_b seq_b_new "branch" new_children
              (pat_o, body)
          let seq_i_new := seqSubst [(v_i, pat_i)] seq_o
          let inner : ProofTree := .caseSplit lbl_i_new seq_i_new v_o inner_arms
          let restArms ← buildArms rest
          return (pat_i, inner) :: restArms
      let newOuterArms ← buildArms inner_pats
      return some (.caseSplit lbl_o_new seq_o v_i newOuterArms)
  | _ => return none

/-! ### Bubble a variable up to the top -/

/-- Bring `v` to the top of `t` by recursively bubbling up in each arm
    then swapping the top two levels. Returns `none` if the tree doesn't
    fit the uniform pattern at some level. -/
partial def bubbleUp (v : String) (t : ProofTree) : FreshM (Option ProofTree) := do
  match topVar t with
  | none => return none
  | some v_top =>
    if v_top == v then return some t
    else
      match t with
      | .caseSplit lbl_o seq_o v_o arms_o =>
        -- Bubble v up in every arm first.
        let rec liftArms : List (SubjectTerm × ProofTree)
                          → FreshM (Option (List (SubjectTerm × ProofTree)))
          | []                   => return some []
          | (pat, sub) :: rest   => do
            match ← bubbleUp v sub with
            | none      => return none
            | some sub' =>
              match ← liftArms rest with
              | none       => return none
              | some rest' => return some ((pat, sub') :: rest')
        match ← liftArms arms_o with
        | none         => return none
        | some newArms => swapAdjacent (.caseSplit lbl_o seq_o v_o newArms)
      | _ => return none

/-! ### Top-level reorder -/

/-- Reorganise `t` so its top-level case-splits match `desiredOrder`
    (outermost first). Recursively bubbles each variable in order to the
    top, then descends into each arm with the remainder of the order.
    Returns the tree unchanged if reorganisation isn't possible. -/
partial def reorderM (desiredOrder : List String) (t : ProofTree) : FreshM ProofTree := do
  match desiredOrder with
  | []        => return t
  | v :: rest =>
    match ← bubbleUp v t with
    | none    => return t
    | some t' =>
      match t' with
      | .caseSplit lbl seq v' arms =>
        if v' != v then return t
        else
          let newArms ← armsReordered rest arms
          return .caseSplit lbl seq v' newArms
      | _ => return t
where
  armsReordered (rest : List String) :
      List (SubjectTerm × ProofTree) → FreshM (List (SubjectTerm × ProofTree))
    | []                      => return []
    | (pat, sub) :: remaining => do
      let sub' ← reorderM rest sub
      let tail ← armsReordered rest remaining
      return (pat, sub') :: tail

/-- Reorganise `t` with a fresh counter, returning the reorganised tree. -/
def reorder (desiredOrder : List String) (t : ProofTree) : ProofTree :=
  (reorderM desiredOrder t).run' 0

/-! ### Back-edge retargeting

Original — neither Grotenhuis-Otten Prop 5.8 nor Wehr Ch. 7 specifies how
to rewire back-edges after permuting case-splits, since their formalism
identifies bud-companion pairs by sequent rather than by surface label.
Our cyclic-proof tree carries explicit `ancestor` labels on each back-
edge, so we need an explicit pass.

After reorganisation moves bodies into new positions, each back-edge's
`anc` field needs updating: the case-split it logically targets (the
one on its *descending variable*) is now at a new position with a new
label. A simple label-based remap can't compute this — it only knows
where the *old* label moved, not which new ancestor matches the
back-edge's intent.

`retargetBacks` walks the reorganised tree, maintaining a stack of
`(var, currentLabel)` pairs (innermost first). For each back-edge,
look up its descending variable in the supplied `descMap` (back-edge
label → descending variable, computed from the annotation's per-back-
edge `progPos`), then resolve to the current label of the case-split
on that variable.
-/

partial def retargetBacks (descMap : List (String × String)) :
    List (String × String) → ProofTree → ProofTree
  | _, .leaf l s j t          => .leaf l s j t
  | _, .identity l s          => .identity l s
  | vToL, .node l s r cs      => .node l s r (cs.map (retargetBacks descMap vToL))
  | vToL, .caseSplit l s v cs =>
    let vToL' := (v, l) :: vToL  -- innermost first
    .caseSplit l s v (cs.map fun (p, t) => (p, retargetBacks descMap vToL' t))
  | vToL, .back lbl s anc σ t =>
    let newAnc :=
      match descMap.lookup lbl with
      | some descVar => (vToL.lookup descVar).getD anc
      | none         => anc
    .back lbl s newAnc σ t
  | vToL, .haveStep l s n ty pf cont =>
    .haveStep l s n ty pf (retargetBacks descMap vToL cont)
  | vToL, .existsStep l s w cont =>
    .existsStep l s w (retargetBacks descMap vToL cont)

end CyclicTactic.Reorganize
