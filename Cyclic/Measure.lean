import Cyclic.SizeChange

/-!
# Termination measure synthesis from size-change graphs

Given a list of size-change graphs (as produced by `extractAllSCGs` on
the function side, or `extractTraceSCGs` on the proof side), try to
synthesize a syntactic termination measure that Lean's well-founded
recursion machinery can verify.

The synthesizer tries several schemas, in order of complexity:

1. **Lex measure on a permutation of positions** — every input graph has
   a strict self-loop at some position with nonstrict self-loops at all
   earlier positions in the permutation. Captures classic lex termination
   like Ackermann.
2. **Lex measure on an ordered subset** — same but allowing positions to
   be omitted from the lex tuple. Catches cases where some arguments
   don't participate in any descent.
3. **Sum measure** — the bag of arguments shrinks as a whole (every
   position has an incoming ≥ edge, with at least one strict). Catches
   swap-style recursions.
4. **Closure-witness lex** — compute the SCT composition closure, extract
   for each idempotent the set of positions with strict self-loops, and
   try lex orderings prioritising those positions. This is the paper-
   faithful synthesis: the measure is constructed from the witnesses
   that the SCT soundness check produces.

All schemas validate the chosen measure against the **input** graphs, not
just the closure idempotents — Lean's `termination_by` requires every
recursive call to decrease, not just every cycle.
-/

namespace SCGraph

/-- Does `g` have a strict self-loop at parameter `i`? -/
def selfLoopStrict (g : SCGraph) (i : Nat) : Bool :=
  g.edges.any fun e => e.src == i && e.tgt == i && e.label == .strict

/-- Does `g` have any self-loop at parameter `i` (strict or nonstrict)? -/
def selfLoopAny (g : SCGraph) (i : Nat) : Bool :=
  g.edges.any fun e => e.src == i && e.tgt == i

/-- All positions on which `g` has a strict self-loop. -/
def strictSelfLoopPositions (g : SCGraph) (arity : Nat) : List Nat :=
  (List.range arity).filter g.selfLoopStrict

end SCGraph

/-! ### Permutation enumeration -/

/-- Enumerate all permutations of a list of distinct naturals. -/
partial def allPerms : List Nat → List (List Nat)
  | [] => [[]]
  | xs =>
    xs.flatMap fun x =>
      (allPerms (xs.filter (· != x))).map (x :: ·)

/-- Enumerate all *ordered subsets* of a list of distinct naturals. Each
    subset appears in every possible ordering. Excludes the empty subset
    since lex on `[]` always fails. -/
partial def allOrderedSubsets : List Nat → List (List Nat)
  | []  => []
  | xs  =>
    xs.flatMap fun x =>
      let rest := allOrderedSubsets (xs.filter (· != x))
      [x] :: rest.map (x :: ·)

/-! ### Lex synthesis -/

/-- Along permutation `perm`, graph `g` strictly decreases iff we find some
    position with a strict self-loop, with all earlier positions having at
    least a nonstrict self-loop. -/
partial def lexValidates (perm : List Nat) (g : SCGraph) : Bool :=
  match perm with
  | [] => false
  | i :: rest =>
    if g.selfLoopStrict i then true
    else if g.selfLoopAny i then lexValidates rest g
    else false

/-- Find a parameter-index permutation of *all* arity positions that
    validates every graph, if one exists. -/
def synthLexOrder (gs : List SCGraph) (arity : Nat) : Option (List Nat) :=
  (allPerms (List.range arity)).find? fun perm => gs.all (lexValidates perm)

/-- Find an *ordered subset* of arity positions that validates every
    graph. Strictly more lenient than `synthLexOrder` (every full
    permutation is itself an ordered subset). -/
def synthLexSubset (gs : List SCGraph) (arity : Nat) : Option (List Nat) :=
  (allOrderedSubsets (List.range arity)).find? fun perm => gs.all (lexValidates perm)

/-! ### Closure-witness synthesis (paper-faithful)

For every idempotent `G` in the SCT closure, the multi-graph SCT condition
guarantees `G` has a strict self-loop at *some* position. The set of such
positions is a *witness* of the cyclic proof's soundness. The paper's
unravelling extracts these witnesses and constructs a lex measure where
each component is a "name" (= position) annotated with a "sort" (= rank
in the lex priority); see Definition 5.1 of Grotenhuis-Otten.

For our flat-arity setting (where "names" are just argument positions),
the stack-annotated lex measure reduces to a *greedy rank construction*:

  1. Compute the SCT closure and extract idempotents.
  2. Iteratively choose lex priorities. At each step, the next-priority
     position is the one that:
       (a) has a *strict* self-loop in the most idempotents that haven't
           yet been "covered" by earlier-priority positions,
       (b) AND has a *nonstrict* (or strict) self-loop in those
           idempotents at every previously-chosen position (otherwise lex
           semantics would fall through past it).
  3. Stop when every idempotent is covered, or no progress is possible.
  4. Validate the resulting lex order against the *input* graphs (not just
     the closure) — Lean's `termination_by` requires per-call decrease.

This is constructive: when SCT passes, the algorithm always produces a
witness lex order for the cyclic structure (even if for some inputs the
per-call validation fails, indicating a richer-than-lex measure is
needed — a case the paper handles via more general stack annotations).
-/

/-- Compute the strict-self-loop position sets of every idempotent in the
    SCT closure of `gs`. Returns one `List Nat` per idempotent. -/
def closureWitnesses (gs : List SCGraph) (arity : Nat) (fuel : Nat := 100)
    : List (List Nat) :=
  let closed := SCGraph.closure gs fuel
  let idempotents := closed.filter SCGraph.isIdempotent
  idempotents.map (fun g => g.strictSelfLoopPositions arity)

/-- Score positions by how many idempotent witnesses include them. Higher
    score = appears in more idempotents = better lex priority. -/
def positionFrequencies (witnesses : List (List Nat)) (arity : Nat)
    : List (Nat × Nat) :=
  (List.range arity).map fun i =>
    (i, (witnesses.filter (·.elem i)).length)

/-- Greedy rank construction (paper-faithful): build the lex order
    incrementally by picking, at each step, the position that strictly
    covers the most uncovered idempotents (with nonstrict at all chosen
    positions). The output is the constructed lex order, or `none` if
    the result fails per-call validation against the input graphs. -/
partial def synthLexGreedy (gs : List SCGraph) (arity : Nat) (fuel : Nat := 100)
    : Option (List Nat) :=
  let closed := SCGraph.closure gs fuel
  let idempotents := closed.filter SCGraph.isIdempotent
  if idempotents.isEmpty then none
  else
    let positions := List.range arity
    -- Iterate up to `arity` times — the lex order can have at most
    -- `arity` components, since positions are distinct.
    let candidate := buildLex positions idempotents [] arity
    if candidate.isEmpty then none
    else if gs.all (lexValidates candidate) then some candidate
    else none
where
  /-- One iteration of the greedy: pick the position with the highest
      "strict-coverage score" among those that haven't been chosen yet,
      subject to the constraint that prior positions have nonstrict self-
      loops in the idempotents being covered. -/
  buildLex (positions : List Nat) (idempotents : List SCGraph)
           (chosen : List Nat) (steps : Nat) : List Nat :=
    if steps = 0 then chosen
    else
      let uncovered := idempotents.filter (fun g => ¬ lexValidates chosen g)
      if uncovered.isEmpty then chosen
      else
        let remaining := positions.filter (fun p => ¬ chosen.elem p)
        let scored : List (Nat × Nat) := remaining.map fun p =>
          let count := (uncovered.filter (fun g =>
            g.selfLoopStrict p && chosen.all (g.selfLoopAny ·))).length
          (p, count)
        let positiveScores := scored.filter (·.2 > 0)
        match positiveScores with
        | [] => chosen
        | first :: _ =>
          let best := positiveScores.foldl
            (fun acc x => if x.2 > acc.2 then x else acc) first
          buildLex positions idempotents (chosen ++ [best.1]) (steps - 1)

/-! ### Sum synthesis -/

/-- Does the sum `a₀ + … + a_{n-1}` strictly decrease on this graph?
    Needs a bijection callee→caller with each edge ≥ and at least one strict. -/
partial def sumDecreasesIn (g : SCGraph) : Bool :=
  if g.dom != g.codom then false
  else
    let arity := g.dom
    (allPerms (List.range arity)).any fun perm =>
      let matched := (List.range arity).all fun j =>
        g.edges.any fun e => e.src == perm[j]! && e.tgt == j
      let hasStrict := (List.range arity).any fun j =>
        g.edges.any fun e => e.src == perm[j]! && e.tgt == j && e.label == .strict
      matched && hasStrict

/-- Is the sum-of-args a valid termination measure for this graph set? -/
def sumMeasureWorks (gs : List SCGraph) : Bool :=
  gs.all sumDecreasesIn

/-! ### Unified synthesis -/

/-- A synthesized termination measure. -/
inductive Measure where
  /-- Lex order on the parameter indices (outermost first). May be a
      proper subset of all positions if some arguments don't participate
      in any descent. -/
  | lex (order : List Nat)
  /-- Sum of the first `arity` parameters. -/
  | sum (arity : Nat)
  deriving Repr

instance : ToString Measure where
  toString
    | .lex order =>
      let elems := order.map (fun i => s!"a{i}")
      s!"lex ({String.intercalate ", " elems})"
    | .sum n =>
      if n == 0 then "0"
      else String.intercalate " + " ((List.range n).map (fun i => s!"a{i}"))

/-- Try the schemas in order. Returns `none` if none work.

    Order: the cheapest and most natural schemas first, paper-faithful
    closure-based last as the fallback for tricky cyclic structures. -/
def synthMeasure (gs : List SCGraph) (arity : Nat) : Option Measure :=
  match synthLexOrder gs arity with
  | some order => some (.lex order)
  | none =>
    match synthLexSubset gs arity with
    | some order => some (.lex order)
    | none =>
      if sumMeasureWorks gs then some (.sum arity)
      else
        match synthLexGreedy gs arity with
        | some order => some (.lex order)
        | none       => none

/-! ### Closure-witness diagnostics

Expose the closure analysis as a separate function so the `cyclic_thm`
command can include it in its info messages — making the SCT soundness
witness visible to the user even when measure synthesis succeeds via a
simpler schema. -/

/-- Render the closure witnesses as a human-readable string: one line
    per idempotent, listing its strict-self-loop positions. -/
def witnessesToString (gs : List SCGraph) (arity : Nat) (fuel : Nat := 100) : String :=
  let witnesses := closureWitnesses gs arity fuel
  if witnesses.isEmpty then "(no idempotents in closure)"
  else
    let lines := (witnesses.zip (List.range witnesses.length)).map fun (ps, i) =>
      let posStr := if ps.isEmpty then "∅"
                    else "{" ++ String.intercalate ", " (ps.map toString) ++ "}"
      s!"  idempotent #{i}: strict self-loops at {posStr}"
    String.intercalate "\n" lines

/-! ### Diagnostic checks: the greedy synthesis on the existing examples -/

-- Ackermann-shape: lex on slot 0 alone covers every back-edge
#eval synthLexGreedy
  [⟨2, 2, [⟨0, 0, .strict⟩]⟩,                          -- back-edge 1
   ⟨2, 2, [⟨0, 0, .strict⟩]⟩,                          -- back-edge 2
   ⟨2, 2, [⟨0, 0, .nonstrict⟩, ⟨1, 1, .strict⟩]⟩] 2
-- expected: some [0]  (slot 0 has strict self-loop in every idempotent)

-- Swap-shape: closure idempotents have strict on both 0 and 1
#eval synthLexGreedy
  [⟨2, 2, [⟨0, 1, .strict⟩, ⟨1, 0, .nonstrict⟩]⟩] 2
-- expected: none  (the input graph has no per-call self-loop, so lex
--                  can't validate inputs even though closure witnesses
--                  are non-empty — sum is the right answer here)

-- Lex on first arg works for both
#eval witnessesToString
  [⟨2, 2, [⟨0, 0, .strict⟩]⟩,
   ⟨2, 2, [⟨0, 0, .nonstrict⟩, ⟨1, 1, .strict⟩]⟩] 2
-- prints idempotents with their strict-self-loop position sets
