import CyclicTactic.SizeChange
import CyclicTactic.ProofTree

/-!
# Paper-faithful Stack/Name/Reset annotation

Direct implementation of Grotenhuis-Otten "Unravelling Abstract Cyclic
Proofs into Proofs by Induction" (arXiv 2602.12054), Definition 5.1.
The earlier `CyclicTactic.Annotation` module collapsed this construction
to its trivial flat-arity case and used `WellFounded.fix`-style measure
synthesis as a proxy; this module computes the actual `Stack(n)_j`,
`Name(n)`, `var(n, a)` and `Reset(n)` annotations defined by the paper.

## Vocabulary

- `Name`         — the abstract names from the paper's set `Name = {a₀, a₁, …}`.
- `Stack`        — a non-repeating list of names (paper's `Name*`).
- `NodeAnnot`    — the annotation at a single node: `(stacks, names, varOf, reset)`.

## Algorithm step (Def 5.1, n_{i+1} case)

Given `n_i`'s annotation and the size-change graph `G_i` describing the
edge `n_i → n_{i+1}`:

1. **New names** — allocate a fresh name per slot of `n_{i+1}`.
2. **New variables** — old names map to old variables; new names map to
   the freshly-introduced variables.
3. **New stacks** — for each slot `j'` of `n_{i+1}`, look at every slot
   `j` of `n_i` connected by `G_i`: a strict edge contributes the
   candidate `Stack(n_i)_j ++ [a'_{j'}]`; a nonstrict edge contributes
   `Stack(n_i)_j`. Pick the *oldest* candidate (the one whose set of
   names contains the oldest element in the symmetric difference). If
   no candidate, start a new stack `[a'_{j'}]`.
4. **Reset** — while some name `a` is *uniformly covered* by a strictly
   younger `a'` (i.e., wherever `a` appears, so does `a'`), trim every
   stack to its prefix up to and including `a`, drop names that no
   longer appear in any stack, and add `a` to `Reset(n_{i+1})`.
   Process youngest-first.

The implementation here operates on abstract `(NodeAnnot, SCGraph)`
inputs so it is testable in isolation; the proof-tree driver is in a
separate function below.
-/

namespace CyclicTactic.PaperAnnotation

/-! ### Names

Names are `Nat`s for cheap freshness/comparison. The paper writes them
as `a₀, a₁, …`; we render them that way in diagnostics. The "age" order
of names is just numeric `<`. -/
abbrev Name := Nat

abbrev Stack := List Name

/-- Pretty-print one name as `aₖ`. -/
def Name.pp (n : Name) : String := "a" ++ toString n

/-- Pretty-print a stack as `[a0, a3]`. -/
def Stack.pp (s : Stack) : String :=
  "[" ++ String.intercalate ", " (s.map Name.pp) ++ "]"

/-- Per-node annotation. The `varOf` map records the slot that carried
    each name when it was introduced, so we can recover the paper's
    `var(n_i, a)` (the actual proof-tree variable) at any node from the
    name alone. -/
structure NodeAnnot where
  /-- One stack per slot of the current node, in slot order. -/
  stacks : List Stack
  /-- All names currently in scope, ordered oldest-first (lower `Nat` is
      older). The paper requires `Name(n_i)` to be non-repeating; we
      maintain that invariant. -/
  names  : List Name
  /-- Map name → original slot index where the name was introduced.
      Together with the chain of substitutions on the path, this lets
      callers recover which Lean-level variable carries the name. -/
  varOf  : List (Name × Nat)
  /-- Reset events at this node, paired with the covering names. The
      first element of each pair is what `Reset(n_i)` contains in the
      paper (the older, surviving name). The second is the *cover* —
      the younger name that uniformly covered the older one immediately
      before the reset, which Def 6.1 names `cov(n_k)`. The cover gets
      gc'd by the reset operation but is still meaningful for emission
      (it identifies a strict ancestor of the progressing variable). -/
  resetCover : List (Name × Name)
  deriving Repr, Inhabited

namespace NodeAnnot

/-- The names reset at this node — `Reset(n_i)` in the paper. Derived
    by projecting `resetCover` to its first component. -/
def reset (a : NodeAnnot) : List Name := a.resetCover.map (·.1)

/-- The cover for a reset name, if it was reset at this node. `cov(n_k)`
    in Def 6.1 — the younger name that uniformly covered the reset
    (older) name immediately before the reset operation. -/
def cov? (a : NodeAnnot) (n : Name) : Option Name := a.resetCover.lookup n

/-- Pretty-print a `NodeAnnot` as a multi-line block. -/
def pp (a : NodeAnnot) : String :=
  let stacksStr :=
    String.intercalate "\n  " (a.stacks.zipIdx.map fun (s, i) =>
      "slot " ++ toString i ++ ": " ++ Stack.pp s)
  let namesStr := "[" ++ String.intercalate ", " (a.names.map Name.pp) ++ "]"
  let resetStr :=
    if a.resetCover.isEmpty then "∅"
    else "{" ++ String.intercalate ", "
              (a.resetCover.map fun (r, c) => Name.pp r ++ "↤" ++ Name.pp c) ++ "}"
  "stacks:\n  " ++ stacksStr
    ++ "\nnames: " ++ namesStr
    ++ "\nreset: " ++ resetStr

instance : ToString NodeAnnot := ⟨pp⟩

/-- Initial annotation at the root, given root arity `k`. Each slot gets
    its own singleton stack `[a_j]`. -/
def root (arity : Nat) : NodeAnnot :=
  let names : List Name := (List.range arity)
  { stacks := names.map ([·])
    names  := names
    varOf  := names.map fun a => (a, a)
    resetCover := [] }

end NodeAnnot

/-! ### The algorithm step

Given `parent : NodeAnnot` and the SCG `G_i : SCGraph` of the parent →
child edge, plus the *child arity* (which equals `G_i.codom`), compute
`child : NodeAnnot` per Def 5.1 (n_{i+1} case).

Naming convention inside this section:
- `j`   — a parent slot index (0 ≤ j < parent arity = G_i.dom).
- `j'`  — a child slot index  (0 ≤ j' < child arity = G_i.codom).
- `a`, `a'` — names. -/

/-- Allocate `k` fresh names: the smallest `k` numerals not currently
    in `existing`. This matches Def 5.1's "let `a'_0, a'_1, …` be the
    first names that are not in `Name(n_i)`": names get *reused* once
    they leave scope (via reset+gc), which is what makes annotations
    recur across iterations of the cyclic representation (Lemma 5.4
    bounds the alphabet at `2^m + m`, finite). -/
partial def freshNames (k : Nat) (existing : List Name) : List Name :=
  let rec loop (need : Nat) (cur : Nat) (acc : List Name) : List Name :=
    if need = 0 then acc.reverse
    else if existing.elem cur then loop need (cur + 1) acc
    else loop (need - 1) (cur + 1) (cur :: acc)
  loop k 0 []

/-- "Older" comparison on stacks (Def 5.1, "new stacks" step):

      A stack `s` is *older* than a stack `s'` if `s` contains the
      oldest name in their set-symmetric difference `S △ S'`.

    With `Name = Nat` and "older = smaller", this is: pick the smallest
    element of `S △ S'`; whichever of `s, s'` contains it is older. If
    `S = S'`, neither is strictly older — we treat them as equal here
    (the candidate-pick will deterministically choose the first one). -/
def stackOlderThan (s s' : Stack) : Bool :=
  -- Find smallest name in symmetric difference.
  let setS  := s
  let setS' := s'
  let symDiff := (setS.filter (fun a => !setS'.elem a))
                ++ (setS'.filter (fun a => !setS.elem a))
  match symDiff.foldl (init := none) (fun acc a =>
          match acc with
          | none   => some a
          | some b => if a < b then some a else some b) with
  | none   => false  -- equal sets: not strictly older
  | some a => s.elem a

/-- Pick the oldest stack from a non-empty list of candidates. Ties
    broken by list order (stable). -/
def pickOldest : List Stack → Option Stack
  | [] => none
  | c :: cs =>
    some <| cs.foldl (init := c) fun best cand =>
      if stackOlderThan cand best then cand else best

/-- For child slot `j'`, collect candidate stacks induced by `G_i`.

    Edge `j → j'` in `G_i`:
      * `.strict`    → candidate `Stack(parent)_j ++ [aFresh_{j'}]`.
      * `.nonstrict` → candidate `Stack(parent)_j`. -/
def candidatesForChildSlot
    (parent : NodeAnnot) (g : SCGraph) (j' : Nat) (aFresh_j' : Name)
    : List Stack :=
  g.edges.filterMap fun e =>
    if e.tgt != j' then none
    else
      match parent.stacks[e.src]? with
      | none   => none
      | some s =>
        match e.label with
        | .strict    => some (s ++ [aFresh_j'])
        | .nonstrict => some s

/-! ### Reset detection

A name `a` is *uniformly covered* by `a'` at the current node when:
  1. `a` is strictly older than `a'` in `Name(n_{i+1})` (i.e. `a < a'`
     in our `Nat` encoding, AND `a` appears strictly earlier in the
     ordered name list — which is automatic if names are kept in
     ascending order, but we don't rely on that and check directly).
  2. For every slot `j'`, if `a` appears in `Stack(n_{i+1})_{j'}`, so
     does `a'`.

The reset step processes uniformly-covered names youngest-first. -/

/-- True iff `a` is uniformly covered by `a'` given the current stacks.
    Assumes both names are present in the surrounding `names` list. -/
def uniformlyCovered (a a' : Name) (stacks : List Stack) : Bool :=
  if a == a' then false
  else
    stacks.all fun s => !s.elem a || s.elem a'

/-- Among the names present in `names`, find a uniformly-covered (a, a')
    pair where `a` is strictly older than `a'`. Returns the *youngest*
    such `a` (so the reset-loop processes youngest-first per Def 5.1).

    "Strictly older" given our `Nat` names = `a < a'`, modulo the
    `names` ordering: a name not in `names` is ineligible. -/
def findUniformCover (names : List Name) (stacks : List Stack)
    : Option (Name × Name) :=
  -- Scan candidates a in reverse-age order (youngest first).
  let revNames := names.reverse
  revNames.foldl (init := none) fun acc a =>
    match acc with
    | some _ => acc
    | none   =>
      -- Look for any a' strictly younger than a that uniformly covers a.
      let coverers := names.filter fun a' => a < a' && uniformlyCovered a a' stacks
      match coverers with
      | []        => none
      | a' :: _   => some (a, a')

/-- Trim a stack to its prefix up to and including `a`, if `a` appears
    in the stack. If `a` doesn't appear, leave the stack unchanged. -/
def restrictStackTo (a : Name) (s : Stack) : Stack :=
  if s.elem a then
    -- Take prefix while element ≠ a, then append a.
    s.takeWhile (· != a) ++ [a]
  else s

/-- Apply one reset of name `a` to all stacks. -/
def applyReset (a : Name) (stacks : List Stack) : List Stack :=
  stacks.map (restrictStackTo a)

/-- Drop names from `names` that no longer appear in any stack. Preserves
    order. -/
def gcNames (names : List Name) (stacks : List Stack) : List Name :=
  names.filter fun a => stacks.any (·.elem a)

/-- Run the reset loop to fixpoint, returning `(newStacks, newNames,
    resetCover)`. Processes uniformly-covered names youngest-first;
    each reset may unlock further covers, hence the loop. The third
    output records, per reset event, the `(reset name, covering name)`
    pair — the cover is the younger name from `findUniformCover` that
    triggered the reset of the older one (Def 6.1's `cov`). -/
partial def resetLoop (names : List Name) (stacks : List Stack)
    : List Stack × List Name × List (Name × Name) :=
  go names stacks []
where
  go (names : List Name) (stacks : List Stack) (acc : List (Name × Name))
      : List Stack × List Name × List (Name × Name) :=
    match findUniformCover names stacks with
    | none          => (stacks, names, acc)
    | some (a, a')  =>
      let stacks' := applyReset a stacks
      let names'  := gcNames names stacks'
      go names' stacks' (acc ++ [(a, a')])

/-- One step of Def 5.1: compute child annotation from parent + edge SCG. -/
def step (parent : NodeAnnot) (g : SCGraph) : NodeAnnot :=
  let childArity := g.codom
  let aFresh : List Name := freshNames childArity parent.names
  -- Step 1+2: new names + new var assignments.
  let newNames : List Name := parent.names ++ aFresh
  let newVarOf : List (Name × Nat) :=
    parent.varOf ++ (aFresh.zipIdx.map fun (a, j') => (a, j'))
  -- Step 3: new stacks per child slot.
  let stacks0 : List Stack :=
    (List.range childArity).map fun j' =>
      let aFresh_j' := aFresh[j']!
      let cands := candidatesForChildSlot parent g j' aFresh_j'
      match pickOldest cands with
      | some s => s
      | none   => [aFresh_j']  -- start a new stack
  -- After choosing stacks, gc names that ended up unused (no slot picked
  -- a candidate that mentions them). This precedes the reset step so the
  -- "uniform cover" check considers only names that actually live in
  -- some stack.
  let gcNames0 := gcNames newNames stacks0
  -- Step 4: reset to fixpoint.
  let (stacks', names', resetCover) := resetLoop gcNames0 stacks0
  { stacks := stacks'
    names  := names'
    varOf  := newVarOf.filter (fun (a, _) => names'.elem a)
    resetCover := resetCover }

/-! ### Self-tests on synthetic SCGs

These exercise the algorithm on the paper's running examples. We hand-
construct the per-edge SCGs because the proof-tree driver is in the
next module section. -/

/-- Render an annotation step `parent --G--> child` as a diagnostic. -/
def renderStep (parent : NodeAnnot) (g : SCGraph) : String :=
  let child := step parent g
  "parent:\n" ++ parent.pp ++ "\nedge SCG: " ++ toString g ++ "\nchild:\n" ++ child.pp

-- Example A — single-arg recursion (zeroAdd shape, descent on slot 0).
-- Root has arity 1 = `[a0]`. Edge SCG: `0 -> 0 strict`.
-- Expected: child.stacks = [[a0, a1]], names = [a0, a1], reset = [].
#eval (do
  let root := NodeAnnot.root 1
  let g : SCGraph := ⟨1, 1, [⟨0, 0, .strict⟩]⟩
  IO.println (renderStep root g)
  : IO Unit)

-- Example B — Ackermann shape, two slots, edge with strict on 0 and
-- nonstrict on 1.
-- Root arity 2 = stacks [[a0], [a1]], names [a0, a1].
-- Edge: 0->0 strict, 1->1 nonstrict.
-- Expected child stacks: slot 0 -> [a0, a2] (strict appends fresh a2);
--                       slot 1 -> [a1] (nonstrict keeps stack).
-- After reset: a3 (the fresh name allocated for slot 1) is unused.
-- Names: [a0, a1, a2].
#eval (do
  let root := NodeAnnot.root 2
  let g : SCGraph := ⟨2, 2, [⟨0, 0, .strict⟩, ⟨1, 1, .nonstrict⟩]⟩
  IO.println (renderStep root g)
  : IO Unit)

-- Example C — descent then *uniform cover* triggers reset. Two
-- consecutive strict edges on slot 0, single-slot proof.
--   Root          : stacks=[[a0]], names=[a0]
--   After step 1  : stacks=[[a0, a1]], names=[a0, a1]
--   After step 2  : new fresh a2; candidate=[a0, a1, a2]; before reset
--                   a0 is uniformly covered by a1 AND by a2; but the
--                   reset is on uniformly-covered *youngest-first*. The
--                   "young" candidate is a1: covered by a2. After reset
--                   on a1: stack becomes [a0, a1] (prefix up to a1).
--                   Then a0 is covered by a1 (vacuously satisfied
--                   anywhere). Reset on a0: [a0]. Names: [a0]. Reset: [a1, a0].
-- (This matches the paper's intent that resets keep stacks bounded.)
#eval (do
  let root := NodeAnnot.root 1
  let g : SCGraph := ⟨1, 1, [⟨0, 0, .strict⟩]⟩
  let n1 := step root g
  IO.println "after step 1:"
  IO.println n1.pp
  let n2 := step n1 g
  IO.println "\nafter step 2:"
  IO.println n2.pp
  : IO Unit)

/-! ### Tree driver

Walks a `ProofTree`, computing the per-node `NodeAnnot` and the
per-back-edge `prog` choice. The per-edge SCG is induced by the path
substitution at each step:

  * `.caseSplit … var arms`: at arm `(pat, sub)`, the step substitution
    is `[(var, pat)]`.
  * `.node`, `.haveStep`, `.existsStep`: identity step (no new
    substitution).
  * `.back`: terminal — produces a bud annotation comparison against
    the recorded sprout (companion's annotation).

The slot-to-slot edge labels are derived from comparing the root sequent
args under the parent's path-substitution to the same args under the
child's path-substitution. Strict iff the child's value is a strict
subterm of the parent's; nonstrict iff structurally equal; otherwise no
edge.

This generalises `CyclicTactic.Proof.buildTraceGraph` (which produces
the cumulative SCG over a whole companion → bud path) to one step at a
time. -/

open CyclicTactic.Proof

/-- Flatten a sequent into the list of subject terms occupying each
    slot, in the same flat order used by `buildTraceGraph` (antecedent
    args first, then succedent args). -/
def Sequent.flatArgs (s : Sequent) : List SubjectTerm :=
  s.antecedents.flatMap (·.args) ++ s.succedents.flatMap (·.args)

/-- Effective slot values at a node. Non-back nodes use the canonical
    root args under the path substitution to that node. Back-edges use
    the bud's recorded literal sequent — its slots already reflect the
    user's `σ_back` substitution (e.g., `{n := n'}`), which is one
    constructor below the path's narrowing (`(n, succ n')`).

    This asymmetry is what lets the SCG compare parent's path-narrowed
    `succ n'` against bud's literal `n'` and detect strict descent. -/
def effectiveSlots (rootArgs : List SubjectTerm) (σp : Subst)
    : ProofTree → List SubjectTerm
  | .back _ bSeq _ _ _ => Sequent.flatArgs bSeq
  | _                  => rootArgs.map (SubjectTerm.subst σp)

/-- Per-edge SCG between two adjacent proof-tree nodes, computed by
    comparing each node's effective slot values structurally:
      * `i → j` strict     iff bud-side slot `j` is a strict subterm of
        parent-side slot `i`;
      * `i → j` nonstrict  iff they are structurally equal;
      * no edge otherwise.

    Caller supplies the parent's effective slots (under its `σp`) and
    the child's effective slots (under `σc` for non-back children, or
    the bud's literal sequent for back-edges). -/
def edgeSCG (parentSlots childSlots : List SubjectTerm) : SCGraph :=
  let n := parentSlots.length
  let m := childSlots.length
  let edges := (List.range n).flatMap fun j =>
    (List.range m).filterMap fun j' =>
      match parentSlots[j]?, childSlots[j']? with
      | some pj, some cj' =>
        if SubjectTerm.structEq cj' pj then some ⟨j, j', .nonstrict⟩
        else if SubjectTerm.strictSubterm cj' pj then some ⟨j, j', .strict⟩
        else none
      | _, _ => none
  ⟨n, m, edges⟩

/-! ### Per-back-edge attribution

Walking the tree, we keep:

  * the running annotation `cur : NodeAnnot`,
  * the running path substitution `σp : Subst` (root → here),
  * a stack of (label, NodeAnnot, σ at that node) for each enclosing
    node — used to look up the companion (sprout) when we hit a back-edge.

At each `.back lbl _ anc σback _`, we look up the companion's recorded
annotation, compute the bud's annotation (which is just `cur`), and
choose `prog(bud) ∈ Reset(cur)` per Theorem 5.2: a reset name that
occurs in `Name(n_i)` for every node along the tree path from sprout
to bud (which we can check by intersecting the names lists at each
recorded ancestor).

For our setting, "occurs in Name(n_i) for every s ≤ i ≤ t" reduces to
"appears in every recorded ancestor's name list, plus in cur.names".
-/

/-- One back-edge's paper-faithful annotation. -/
structure BudAnnot where
  bud        : String
  companion  : String
  /-- The bud's `NodeAnnot` (i.e. `cur` at the back-edge). -/
  budAnnot   : NodeAnnot
  /-- The companion's `NodeAnnot` recorded at the sprout node. -/
  spoutAnnot : NodeAnnot
  /-- Names that appear in `Name(n_i)` for every `i` along the cycle
      sprout → … → bud. -/
  preservedNames : List Name
  /-- The chosen progressing name (intersection of `Reset(bud)` and
      `preservedNames`); `none` if no candidate qualifies (a sign that
      the user's tree doesn't satisfy Theorem 5.2 directly — would
      require unfolding per Prop 5.8). -/
  progName? : Option Name
  /-- Slot index that `progName?` corresponds to via `varOf`. -/
  progSlot? : Option Nat
  deriving Repr, Inhabited

/-! ### Theorem 5.2 verification

The annotation algorithm computes one annotation per node; whether that
annotation satisfies Grotenhuis-Otten Theorem 5.2 on the user's
*specific* tree is a separate question. The theorem asserts that
**every C-proof has** a cyclic representation satisfying the
properties — but finding such a representation on an arbitrary user
tree may require *unfolding* (Proposition 5.8 / Lemma 5.9), which we
don't yet implement.

This section provides a post-pass that checks the conditions on the
tree we have. When it reports failures, the caller knows the
paper-faithful path won't fire for this proof and falls back; the
report tells the user *why* (mismatched names, mismatched stacks, or
no qualifying progressing name).

Theorem 5.2 conditions per back-edge (sprout → bud, both `n_s` and `n_t`):
  (1) `Name(n_t) = Name(n_s)` (as ordered lists).
  (2) `Stack(n_t)_j = Stack(n_s)_j` for every slot `j`.
  (3) `prog(n_t) ∈ Reset(n_t)` and occurs in `Name(n_i)` for every
      `s ≤ i ≤ t`.
-/

inductive Theorem52Failure where
  /-- (1) bud's Name list differs from sprout's. -/
  | nameSetMismatch (budNames sproutNames : List Name)
  /-- (2) bud's stack at slot j differs from sprout's. -/
  | stackMismatch   (slot : Nat) (budStack sproutStack : Stack)
  /-- (3) `Reset(bud) ∩ preservedNames` is empty. -/
  | noProgName      (resetSet preserved : List Name)
  deriving Repr

/-- Per-back-edge verification result. `failures` empty ⇒ Theorem 5.2
    is satisfied for this back-edge. -/
structure Theorem52Check where
  bud       : String
  companion : String
  failures  : List Theorem52Failure
  deriving Repr

/-- Run the conditions of Theorem 5.2 against one back-edge's
    annotation. -/
def checkTheorem52 (b : BudAnnot) : Theorem52Check :=
  let nameMismatch :=
    if b.budAnnot.names == b.spoutAnnot.names then []
    else [Theorem52Failure.nameSetMismatch b.budAnnot.names b.spoutAnnot.names]
  let stackMismatches :=
    -- Compare slot-by-slot, using `List.zip` over equal-length stacks
    -- lists. If the lengths differ that's already covered by the name
    -- mismatch; here we just zip and report disagreeing slots.
    (b.budAnnot.stacks.zip b.spoutAnnot.stacks).zipIdx.filterMap
      fun ((bs, ss), j) =>
        if bs == ss then none
        else some (Theorem52Failure.stackMismatch j bs ss)
  let progMissing :=
    match b.progName? with
    | some _ => []
    | none   =>
      [Theorem52Failure.noProgName b.budAnnot.reset b.preservedNames]
  { bud       := b.bud
    companion := b.companion
    failures  := nameMismatch ++ stackMismatches ++ progMissing }

/-- Render one failure as a single-line diagnostic. -/
def renderFailure : Theorem52Failure → String
  | .nameSetMismatch bn sn =>
    "Name(bud) = [" ++ String.intercalate ", " (bn.map Name.pp)
      ++ "] but Name(sprout) = [" ++ String.intercalate ", " (sn.map Name.pp)
      ++ "]"
  | .stackMismatch j bs ss =>
    "Stack(bud)_" ++ toString j ++ " = " ++ Stack.pp bs
      ++ " but Stack(sprout)_" ++ toString j ++ " = " ++ Stack.pp ss
  | .noProgName rs preserved =>
    "no qualifying progressing name: Reset(bud) = "
      ++ "{" ++ String.intercalate ", " (rs.map Name.pp) ++ "}"
      ++ ", preserved cycle names = "
      ++ "{" ++ String.intercalate ", " (preserved.map Name.pp) ++ "}"

/-- Render a check as a multi-line block; empty string if no failures. -/
def renderCheck (c : Theorem52Check) : String :=
  if c.failures.isEmpty then ""
  else
    "back-edge " ++ c.bud ++ " → " ++ c.companion ++ ": Theorem 5.2 failed\n"
      ++ String.intercalate "\n" (c.failures.map fun f => "  " ++ renderFailure f)

/-- Render the full set of checks; `none` if all back-edges pass. -/
def renderChecks (cs : List Theorem52Check) : Option String :=
  let failing := cs.filter (·.failures.isEmpty == false)
  if failing.isEmpty then none
  else some (String.intercalate "\n" (failing.map renderCheck))

/-- Stable key for an enclosing-node frame: the node's label plus a
    snapshot of `Name(n_i)` at that node (used to compute the
    `preservedNames` intersection). -/
structure AncestorFrame where
  label  : String
  annot  : NodeAnnot
  σ      : Subst
  deriving Repr, Inhabited

/-- Walk the tree. The edge SCG between *this node* and a child uses
    the *child's* `σ` on both sides:
      * parent-side slots = `rootArgs.subst σc`
      * child-side slots  = `effectiveSlots rootArgs σc child`
        (which equals `rootArgs.subst σc` for non-back nodes, or the
        bud's literal `flatArgs` for back-edges).

    The asymmetry — using `σc` on both sides rather than `σp` on the
    parent — mirrors `buildTraceGraph`'s convention: the path
    substitution narrows the parent's view to match the child's, so the
    back-edge's literal `n'` can be matched against the path-narrowed
    `succ n'` to detect strict descent. For non-substituting edges
    (`σc = σp`) this collapses to identity-flavored SCGs.

    Args:
      * `rootArgs`   — canonical root flatArgs.
      * `cur`        — annotation at this node.
      * `σp`         — path subst from root to here.
      * `cycleNames` — names alive at every ancestor up through here.
      * `ancestors`  — recorded ancestor frames. -/
partial def annotateTreeAux
    (rootArgs : List SubjectTerm)
    (cur : NodeAnnot)
    (σp : Subst)
    (cycleNames : List Name)
    (ancestors : List AncestorFrame)
    : ProofTree → List BudAnnot
  | .leaf _ _ _ _    => []
  | .identity _ _    => []
  | .node lbl _ _ children =>
    let frame : AncestorFrame := ⟨lbl, cur, σp⟩
    let ancestors' := frame :: ancestors
    children.flatMap fun child =>
      let σc := σp
      let parentSlots := rootArgs.map (SubjectTerm.subst σc)
      let childSlots := effectiveSlots rootArgs σc child
      let g := edgeSCG parentSlots childSlots
      let cur' := step cur g
      let cycleNames' := cycleNames.filter (cur'.names.elem ·)
      annotateTreeAux rootArgs cur' σc cycleNames' ancestors' child
  | .caseSplit lbl _ var arms =>
    let frame : AncestorFrame := ⟨lbl, cur, σp⟩
    let ancestors' := frame :: ancestors
    arms.flatMap fun (pat, sub) =>
      let σc := (var, pat) :: σp
      let parentSlots := rootArgs.map (SubjectTerm.subst σc)
      let childSlots := effectiveSlots rootArgs σc sub
      let g := edgeSCG parentSlots childSlots
      let cur' := step cur g
      let cycleNames' := cycleNames.filter (cur'.names.elem ·)
      annotateTreeAux rootArgs cur' σc cycleNames' ancestors' sub
  | .dCaseSplit lbl _ _ _ pos neg =>
    -- Decidable split: no root-var substitution, identity edge into each
    -- arm (slots unchanged). Mirrors `.node`'s identity step but with two
    -- children.
    let frame : AncestorFrame := ⟨lbl, cur, σp⟩
    let ancestors' := frame :: ancestors
    [pos, neg].flatMap fun child =>
      let σc := σp
      let parentSlots := rootArgs.map (SubjectTerm.subst σc)
      let childSlots := effectiveSlots rootArgs σc child
      let g := edgeSCG parentSlots childSlots
      let cur' := step cur g
      let cycleNames' := cycleNames.filter (cur'.names.elem ·)
      annotateTreeAux rootArgs cur' σc cycleNames' ancestors' child
  | .haveStep lbl _ _ _ _ cont =>
    let frame : AncestorFrame := ⟨lbl, cur, σp⟩
    let ancestors' := frame :: ancestors
    let σc := σp
    let parentSlots := rootArgs.map (SubjectTerm.subst σc)
    let childSlots := effectiveSlots rootArgs σc cont
    let g := edgeSCG parentSlots childSlots
    let cur' := step cur g
    let cycleNames' := cycleNames.filter (cur'.names.elem ·)
    annotateTreeAux rootArgs cur' σc cycleNames' ancestors' cont
  | .existsStep lbl _ _ cont =>
    let frame : AncestorFrame := ⟨lbl, cur, σp⟩
    let ancestors' := frame :: ancestors
    let σc := σp
    let parentSlots := rootArgs.map (SubjectTerm.subst σc)
    let childSlots := effectiveSlots rootArgs σc cont
    let g := edgeSCG parentSlots childSlots
    let cur' := step cur g
    let cycleNames' := cycleNames.filter (cur'.names.elem ·)
    annotateTreeAux rootArgs cur' σc cycleNames' ancestors' cont
  | .back lbl _ anc _ _ =>
    match ancestors.find? (·.label == anc) with
    | none =>
      [{ bud := lbl
         companion := anc
         budAnnot := cur
         spoutAnnot := cur
         preservedNames := []
         progName? := none
         progSlot? := none }]
    | some frame =>
      let preserved := frame.annot.names.filter (cycleNames.elem ·)
      let progN? := cur.reset.find? (preserved.elem ·)
      let progS? : Option Nat :=
        progN?.bind fun a =>
          cur.stacks.zipIdx.findSome? fun (s, j) => if s.elem a then some j else none
      [{ bud := lbl
         companion := anc
         budAnnot := cur
         spoutAnnot := frame.annot
         preservedNames := preserved
         progName? := progN?
         progSlot? := progS? }]

/-- Walk the tree once with a given starting annotation. -/
def annotateTreeFromCur (t : ProofTree) (cur0 : NodeAnnot) : List BudAnnot :=
  let rootArgs := Sequent.flatArgs t.sequent
  let frame0 : AncestorFrame := ⟨t.label, cur0, []⟩
  annotateTreeAux rootArgs cur0 [] cur0.names [frame0] t

/-! ### Lemma 5.9 unfolding

When the user's tree doesn't directly satisfy Theorem 5.2 for some
bud, the paper's resolution is to unfold the cyclic representation
until the bud's annotation recurs. By Lemma 5.4 the alphabet is
finite (`2^m + m` names), so by König's lemma some `(node, annot)`
pair must repeat — that's where we close.

Concretely, for each failing bud `b`:
  1. Re-walk the tree with `cur0 := lastIter.budAnnot` (carrying the
     bud's annotation into the next iteration as the starting cur).
  2. Find the same back-edge label `b.bud` in the new walk.
  3. If that bud's `(stacks, names)` key matches any prior iteration's
     key, declare convergence and emit the BudAnnot with sprout = the
     matching prior annotation; cross-iteration `preservedNames` is
     the intersection of all prior iters' name lists.
  4. Otherwise iterate up to `fuel` times.

The smallest-available-name allocator (`freshNames`) is what makes
this terminate: names get reused after gc, so distinct iterations
produce identical `(stacks, names)` tuples once we hit the cycle.
-/

/-- An annotation key for fixpoint matching: just `(stacks, names)`. -/
abbrev AnnotKey := List Stack × List Name

def annotKey (a : NodeAnnot) : AnnotKey := (a.stacks, a.names)

/-- Try to find a fixpoint annotation for `originalBud` by iteratively
    unfolding the cyclic representation. Returns the converged
    `BudAnnot` if convergence is reached within `fuel` iterations, or
    `none` otherwise. -/
partial def unfoldFixpoint
    (origTree : ProofTree) (originalBud : BudAnnot) (fuel : Nat)
    : Option BudAnnot :=
  let initKey := annotKey originalBud.budAnnot
  let initPreserved := originalBud.budAnnot.names
  loop fuel originalBud.budAnnot initPreserved [(initKey, originalBud.budAnnot)]
where
  loop (fuel : Nat) (curStart : NodeAnnot) (crossPreserved : List Name)
       (history : List (AnnotKey × NodeAnnot)) : Option BudAnnot :=
    match fuel with
    | 0 => none
    | f + 1 =>
      let iterBuds := annotateTreeFromCur origTree curStart
      match iterBuds.find? (·.bud == originalBud.bud) with
      | none   => none
      | some b =>
        let bKey := annotKey b.budAnnot
        match history.find? (fun (k, _) => k == bKey) with
        | some (_, priorAnnot) =>
          -- Convergence: this bud's key recurs at `priorAnnot`. The
          -- cycle goes from `priorAnnot` through subsequent iterations
          -- to here; cross-iteration preserved names is the running
          -- intersection accumulated in `crossPreserved`.
          let pres := crossPreserved.filter (b.budAnnot.names.elem ·)
          let progN? := b.budAnnot.reset.find? (pres.elem ·)
          let progS? : Option Nat :=
            progN?.bind fun a =>
              b.budAnnot.stacks.zipIdx.findSome? fun (s, j) =>
                if s.elem a then some j else none
          some { bud := originalBud.bud
                 companion := originalBud.companion
                 budAnnot := b.budAnnot
                 spoutAnnot := priorAnnot
                 preservedNames := pres
                 progName? := progN?
                 progSlot? := progS? }
        | none =>
          let newPreserved := crossPreserved.filter (b.budAnnot.names.elem ·)
          let history' := history ++ [(bKey, b.budAnnot)]
          loop f b.budAnnot newPreserved history'

/-- Top-level driver. Runs the initial walk, then for each bud whose
    annotation fails Theorem 5.2 conditions (1)–(2) on the user's tree,
    attempts Lemma 5.9 unfolding to find a fixpoint that satisfies them.

    `unfoldFuel` bounds the number of unfolding iterations per failing
    bud. `2^arity * arity` is conservative; in practice 2-3 iterations
    suffice for the proofs we've seen. -/
def annotateTree (t : ProofTree) (unfoldFuel : Nat := 16) : List BudAnnot :=
  let rootArgs := Sequent.flatArgs t.sequent
  let cur0 := NodeAnnot.root rootArgs.length
  let initBuds := annotateTreeFromCur t cur0
  initBuds.map fun b =>
    -- If Theorem 5.2 holds directly, use as is.
    if (checkTheorem52 b).failures.isEmpty then b
    else
      match unfoldFixpoint t b unfoldFuel with
      | some converged => converged
      | none           => b  -- couldn't converge; surface original failure

/-! ### End-to-end self-test

Hand-build the `zeroAdd` proof tree:
  R: caseSplit on n
   | zero        → leaf (rfl)
   | succ n'     → back R {n := n'}
sequent for the root: `⊢ Eq(0+n, n)` — flat arity = 2 (the two args of `=`).
After case-split into the `succ n'` arm, the bud's sequent is `⊢ Eq(0+n', n')`.

Expected:
  * 1 back-edge.
  * `progName?` is set to a name that, via varOf, points to slot 1 (the
    slot holding `n`).
  * `preservedNames` includes the root's a0 and a1 (both alive
    throughout the cycle, since the cycle is one-step).
-/

def zeroAddTree : ProofTree :=
  let rootSeq : Sequent :=
    .succ1 ⟨"=", [.ctor "+" [.ctor "0" [], .var "n"], .var "n"]⟩
  let succArmSeq : Sequent :=
    .succ1 ⟨"=", [.ctor "+" [.ctor "0" [], .var "n'"], .var "n'"]⟩
  let bSeq : Sequent := succArmSeq
  .caseSplit "R" rootSeq "n"
    [(.ctor "Nat.zero" [], .leaf "Lzero" rootSeq "rfl" none),
     (.ctor "Nat.succ" [.var "n'"],
        .back "B" bSeq "R" [("n", .var "n'")] none)]

#eval (do
  let buds := annotateTree zeroAddTree
  for b in buds do
    IO.println s!"bud {b.bud} → {b.companion}"
    IO.println s!"  bud annot:\n{b.budAnnot.pp}"
    IO.println s!"  sprout annot:\n{b.spoutAnnot.pp}"
    IO.println s!"  preserved: {b.preservedNames.map Name.pp}"
    IO.println s!"  progName?: {b.progName?.map Name.pp}"
    IO.println s!"  progSlot?: {b.progSlot?}"
  : IO Unit)

/-- Render bud annotations as a multi-line diagnostic. -/
def renderBuds (buds : List BudAnnot) : String :=
  if buds.isEmpty then "(no back-edges)"
  else String.intercalate "\n\n" <| buds.map fun b =>
    let progStr := match b.progName?, b.progSlot? with
      | some a, some j => s!"prog = {Name.pp a} (slot {j})"
      | some a, none   => s!"prog = {Name.pp a} (slot ?)"
      | none, _        => "prog = (none — Thm 5.2 unsatisfied on this tree)"
    let preservedStr :=
      "{" ++ String.intercalate ", " (b.preservedNames.map Name.pp) ++ "}"
    let resetStr :=
      "{" ++ String.intercalate ", " (b.budAnnot.reset.map Name.pp) ++ "}"
    s!"back-edge {b.bud} → {b.companion}:\n  {progStr}\n  preserved cycle names: {preservedStr}\n  Reset(bud) = {resetStr}"

end CyclicTactic.PaperAnnotation
