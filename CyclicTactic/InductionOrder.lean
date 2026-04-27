import CyclicTactic.SizeChange
import CyclicTactic.Measure
import CyclicTactic.ProofTree

/-!
# Wehr Theorem 3.2.4: SCC-based induction-order construction

Implements the induction-order finding algorithm from Wehr 2025 PhD
thesis "Cyclic Proof Theory", Theorem 3.2.4 (book p. 33). For our
flat-arity, single-predicate setting, this is a direct specialisation.

## What an induction order is (Def 3.2.1, p. 32)

Given a cyclic preproof (C, λ) in cycle normal form with bud set
dom(β), an induction order is a pre-order ⪯ ⊆ dom(β) × dom(β) with
an associated mapping `x : dom(β) → Var` such that:

  * every strongly connected component C[η] has a ⪯-maximal element,
  * if s ⪯ t then γ(s) **preserves** x_t (i.e. x_t is a free variable
    along every node in γ(s)),
  * the cycle γ(s) **progresses** x_s (i.e. a Caseₓ rule is applied
    along γ(s) on x_s).

Theorem 3.2.4 says every CHA-proof in cycle normal form has one, and
gives a constructive procedure.

## The algorithm (Wehr p. 33, proof of Thm 3.2.4)

1. `S₀ := {η ⊆ dom(β) | η is a dom(β)-maximal SCC of the bud-companion
   graph B}`.
2. To obtain `S_{i+1}`:
     * pick η_i ∈ S_i,
     * find a bud s ∈ η_i and a variable x such that x is preserved
       along γ(t) for every t ∈ η_i and γ(s) progresses x,
     * set x_s := x,
     * `S_{i+1} := (S_i \ η_i) ∪ {η' ⊆ (η_i \ {s}) | η' is a
       (η_i \ {s})-maximal SCC}`.
3. Terminate when `S_{|dom(β)|} = ∅`.
4. Pre-order: `s ⪯ t` iff (let i be the step at which t was removed)
   `s ∈ η_i`. Earlier-removed buds are ⪯-maximal.

## Specialisation to our setting

In our flat single-predicate model:

  * Variables = root-sequent positions (`Nat`).
  * "x preserved along γ(t)" = t's trace SCG has a self-loop (any
    descent) at position x.
  * "γ(s) progresses x" = s's trace SCG has a strict self-loop at
    position x.
  * Bud-companion graph: edge `s → t` iff t's companion's label appears
    on the proof-tree path from s's companion down to s.

The output is a list of `(bud-label, position)` pairs in removal order.
For Lean emission we deduplicate the positions to get the lex induction
order outer-to-inner.

## Why this is paper-faithful (vs. our previous brute-force)

The previous order-finding (`CyclicTactic.Measure.synthLexOrder` and
`synthLexGreedy`) enumerated all permutations / used a closure-witness
greedy. The closure-witness greedy is *related* to Wehr's algorithm but
operates on closure idempotents rather than on the bud-companion graph
of the actual proof. Wehr's algorithm is the principled construction
the paper proves correct (Thm 3.2.4): it works in coNP (Prop 3.2.5)
and gives per-bud variable assignments directly.
-/

namespace CyclicTactic.InductionOrder

open CyclicTactic.Proof

/-! ### Bud contexts: collect each back-edge's companion + path-to-root -/

/-- One entry per back-edge in the proof tree.

    * `bud` — the back-edge's own label (= a bud in Wehr's sense).
    * `companion` — the back-edge's `ancestor` label (= β(bud)).
    * `pathLabels` — labels of all enclosing case-splits / nodes /
      have-steps / exists-steps from the bud upward to the root,
      innermost first. Used to determine which other buds' companions
      lie on this bud's local cycle γ(bud) = path from companion down
      to bud. -/
structure BudCtx where
  bud       : String
  companion : String
  pathLabels : List String
  deriving Repr, Inhabited

/-- Walk the tree, recording each back-edge's enclosing-label path. -/
partial def collectBudContexts (tree : ProofTree) : List BudCtx :=
  go [] tree
where
  go (path : List String) : ProofTree → List BudCtx
    | .leaf _ _ _ _              => []
    | .identity _ _              => []
    | .node lbl _ _ children     =>
      let path' := lbl :: path
      children.flatMap (go path')
    | .caseSplit lbl _ _ cases   =>
      let path' := lbl :: path
      cases.flatMap (fun (_, sub) => go path' sub)
    | .back lbl _ anc _ _        =>
      [{ bud := lbl, companion := anc, pathLabels := path }]
    | .haveStep lbl _ _ _ _ cont =>
      let path' := lbl :: path
      go path' cont
    | .existsStep lbl _ _ cont   =>
      let path' := lbl :: path
      go path' cont

/-! ### Bud-companion graph

For bud s, the local cycle γ(s) is the sub-path of pathLabels from
β(s) (companion) down to s. In our pathLabels representation
(innermost first), this is `companion :: takeUntil(pathLabels,
companion)` — the part of pathLabels strictly above the companion
isn't part of the cycle.

Edge `s → t` iff `β(t) ∈ γ(s)`. -/

/-- Labels on s's local cycle γ(s): the companion plus everything
    between the companion and s in the tree.

    Since `pathLabels` is innermost-first, take entries up to and
    including the companion's first occurrence (innermost-first scan
    finds companion as an ancestor). -/
def localCycleLabels (ctx : BudCtx) : List String :=
  let beforeCompanion := ctx.pathLabels.takeWhile (· != ctx.companion)
  ctx.companion :: beforeCompanion

/-- Build edges of the bud-companion graph: (s, t) iff β(t) ∈ γ(s). -/
def buildBCEdges (contexts : List BudCtx) : List (String × String) :=
  contexts.flatMap fun s =>
    let cycle := localCycleLabels s
    contexts.filterMap fun t =>
      if cycle.elem t.companion then some (s.bud, t.bud) else none

/-! ### Kosaraju's SCC algorithm

Two-pass DFS: forward DFS to compute post-order, then reverse-graph
DFS in reverse post-order. Each tree of the second DFS is one SCC.
-/

partial def dfsForward
    (adj : String → List String)
    : List String → String → List String × List String
  | visited, node =>
    if visited.elem node then ([], visited)
    else
      let visited' := node :: visited
      let neighbors := adj node
      let (po, vFinal) := neighbors.foldl (init := ([], visited')) fun (po, v) n =>
        let (po', v') := dfsForward adj v n
        (po ++ po', v')
      (po ++ [node], vFinal)

/-- Kosaraju's algorithm. Returns a list of SCCs (each SCC is a list of
    node labels). -/
def computeSCCs (nodes : List String) (edges : List (String × String))
    : List (List String) :=
  let outAdj := fun n => edges.filterMap fun (s, t) => if s == n then some t else none
  let inAdj  := fun n => edges.filterMap fun (s, t) => if t == n then some s else none
  -- Pass 1: forward DFS, accumulate post-order.
  let (postOrder, _) := nodes.foldl (init := ([], [])) fun (po, v) n =>
    let (po', v') := dfsForward outAdj v n
    (po ++ po', v')
  -- Pass 2: reverse DFS on reverse-graph in reverse-post-order.
  let order := postOrder.reverse
  let (sccs, _) := order.foldl (init := ([], [])) fun (sccs, v) n =>
    if v.elem n then (sccs, v)
    else
      let (component, v') := dfsForward inAdj v n
      (sccs ++ [component], v')
  sccs

/-! ### Wehr Thm 3.2.4 step: pick a (variable, bud) for one SCC

For one SCC η of the bud-companion graph, find a position x such that:

  * every back-edge in η has *some* self-loop (≥ or >) at position x —
    "x is preserved along γ(t) for every t ∈ η",
  * at least one back-edge has a *strict* (>) self-loop at position x
    — "γ(s) progresses x for some s ∈ η".

Tie-breaking: prefer the smallest position number, then the
lexicographically-smallest bud label, for determinism. -/
def pickProgressing
    (scc : List String)
    (labeledGraphs : List (String × SCGraph))
    (arity : Nat)
    : Option (Nat × String) :=
  let sccGraphs : List (String × SCGraph) :=
    labeledGraphs.filter (fun (lbl, _) => scc.elem lbl)
  -- Iterate positions in numeric order; first qualifying (pos, bud) wins.
  (List.range arity).foldl (init := none) fun acc p =>
    match acc with
    | some _ => acc
    | none =>
      let preservedInAll := sccGraphs.all (fun (_, g) => g.selfLoopAny p)
      if !preservedInAll then none
      else
        let strictBuds : List String :=
          sccGraphs.filterMap fun (lbl, g) =>
            if g.selfLoopStrict p then some lbl else none
        match strictBuds with
        | []      => none
        | b :: _  => some (p, b)

/-! ### The iterative algorithm

`computeOrderForSCC` recursively partitions a single SCC, returning a
list of (bud, position) pairs in removal order. `findInductionOrder`
applies this across all top-level SCCs. -/

partial def computeOrderForSCC
    (scc : List String)
    (labeledGraphs : List (String × SCGraph))
    (bcEdges : List (String × String))
    (arity : Nat)
    : Option (List (String × Nat)) :=
  if scc.isEmpty then some []
  else
    match pickProgressing scc labeledGraphs arity with
    | none           => none
    | some (pos, s)  =>
      let scc' := scc.filter (· != s)
      let restrictedEdges := bcEdges.filter fun (a, b) => scc'.elem a && scc'.elem b
      let subSccs := computeSCCs scc' restrictedEdges
      let rec processSubs : List (List String) → Option (List (String × Nat))
        | []        => some []
        | sub :: rs =>
          match computeOrderForSCC sub labeledGraphs bcEdges arity with
          | none      => none
          | some res' =>
            match processSubs rs with
            | none     => none
            | some tl  => some (res' ++ tl)
      match processSubs subSccs with
      | none        => none
      | some subRes => some ((s, pos) :: subRes)

/-- Top-level Wehr 3.2.4 driver. Returns a list of (bud-label,
    progressing-position) pairs in removal order — earlier entries
    correspond to outer inductions in the eventual Lean emission.

    Returns `none` when the algorithm fails for the proof — typically
    when SCT passes via a non-lex measure (e.g. swap/sum cases). The
    caller falls back to other measure schemas in that case. -/
def findInductionOrder
    (tree : ProofTree)
    (labeledGraphs : List (String × SCGraph))
    (arity : Nat)
    : Option (List (String × Nat)) :=
  let contexts := collectBudContexts tree
  let bcEdges := buildBCEdges contexts
  let buds := contexts.map (·.bud)
  let topSccs := computeSCCs buds bcEdges
  let rec processTops : List (List String) → Option (List (String × Nat))
    | []        => some []
    | s :: rest =>
      match computeOrderForSCC s labeledGraphs bcEdges arity with
      | none     => none
      | some res =>
        match processTops rest with
        | none    => none
        | some tl => some (res ++ tl)
  processTops topSccs

/-- Deduplicate positions in encounter order. The lex induction order
    on positions, outer-to-inner, is the deduplication of the positions
    in the per-bud assignment. -/
def lexOrderFromAssignment (assignment : List (String × Nat)) : List Nat :=
  Id.run do
    let mut out : List Nat := []
    for (_, pos) in assignment do
      if !out.elem pos then out := out ++ [pos]
    return out

/-! ### Diagnostic checks -/

-- Direct test of the SCC step on synthetic SCGs (no proof tree).
-- Two back-edges, both strict on position 0 (Ackermann shape).
#eval pickProgressing
  ["B0", "B1"]
  [("B0", ⟨2, 2, [⟨0, 0, .strict⟩]⟩),
   ("B1", ⟨2, 2, [⟨0, 0, .strict⟩]⟩)] 2
-- expected: some (0, "B0")

-- Lex shape: B0 strict on 0; B1 has 0 preserved + strict on 1.
-- First call should pick (0, "B0"); after removing B0, second pick on
-- {B1} should give (0, "B1") (since B0 having strict-at-0 is gone, but
-- B1's own SCG is `[0 ≥, 1 >]` so position 0 is preserved + strict at 1).
#eval pickProgressing
  ["B0", "B1"]
  [("B0", ⟨2, 2, [⟨0, 0, .strict⟩]⟩),
   ("B1", ⟨2, 2, [⟨0, 0, .nonstrict⟩, ⟨1, 1, .strict⟩]⟩)] 2
-- expected: some (0, "B0")  (position 0 is preserved in both, strict
--                            in B0; we tiebreak by smallest position)

#eval pickProgressing
  ["B1"]
  [("B1", ⟨2, 2, [⟨0, 0, .nonstrict⟩, ⟨1, 1, .strict⟩]⟩)] 2
-- expected: some (1, "B1")  (position 0 is preserved but not strict;
--                            position 1 is strict.)

end CyclicTactic.InductionOrder
