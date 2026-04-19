import Cyclic.SizeChange
import Cyclic.Extract
import Cyclic.Syntax

/-!
# Example: Swapped Addition

Demonstrates the cyclic proof → inductive proof pipeline on a concrete example.

## The cyclic definition

  swapAdd(0, x₁)        = x₁
  swapAdd(suc(x₀'), x₁) = suc(swapAdd(x₁, x₀'))

The recursive call swaps the two arguments, so structural recursion on either
argument alone doesn't apply. This is a simple instance of a cyclic recursive
definition: the call graph has a single back-edge with a non-trivial
size-change graph.

## Size-change analysis

The size-change graph G for the recursive call has two edges:
  • param 1 (x₁) ≥→ callee param 0    (value preserved)
  • param 0 (suc x₀') >→ callee param 1  (strict decrease: x₀' < suc x₀')

Composing G with itself (G²) yields:
  • param 0 >→ param 0   (strict diagonal)
  • param 1 >→ param 1   (strict diagonal)

Both diagonal entries are strict, so SCT confirms termination.

## Transformation to well-founded recursion

The SCT analysis tells us the sum x₀ + x₁ is a valid termination measure:
each call decreases it by 1 (since x₁ + x₀' < suc(x₀') + x₁).
-/

/-! ### Size-change analysis -/

/-- Size-change graph for the recursive call in swapAdd.
    Caller params: (x₀ = suc(x₀'), x₁) at indices (0, 1)
    Callee params: (x₁, x₀') at indices (0, 1) -/
def swapAddGraph : SCGraph where
  dom := 2
  codom := 2
  edges := [
    ⟨1, 0, .nonstrict⟩,  -- x₁ ≥ x₁ (preserved)
    ⟨0, 1, .strict⟩       -- suc(x₀') > x₀' (strict decrease)
  ]

/-- G composed with itself: after two calls, both params strictly decrease. -/
def swapAddGraph2 : SCGraph := swapAddGraph.comp swapAddGraph

-- G: swaps params with one strict descent
#eval toString swapAddGraph
-- "SCGraph(2 → 2): [1 -≥→ 0, 0 ->→ 1]"

-- G²: both diagonal entries are strict
#eval toString swapAddGraph2
-- "SCGraph(2 → 2): [0 ->→ 0, 1 ->→ 1]"

-- SCT check passes: G² has strict diagonal
#eval swapAddGraph2.hasStrictDiag  -- true

-- Full SCT check (finds it in 2 iterations)
#eval swapAddGraph.checkSCT  -- true

/-! ### Well-founded definition (the transformation output) -/

/-- Swapped addition, defined with well-founded recursion.
    This is what the cyclic proof transformation produces:
    the same equations, but with an explicit termination measure
    derived from the size-change analysis. -/
def swapAdd (x₀ x₁ : Nat) : Nat :=
  match x₀ with
  | 0 => x₁
  | .succ x₀' => .succ (swapAdd x₁ x₀')
termination_by x₀ + x₁

-- Verify correctness
#eval swapAdd 3 5   -- 8
#eval swapAdd 0 42  -- 42
#eval swapAdd 10 0  -- 10

/-- swapAdd agrees with Nat.add -/
theorem swapAdd_eq_add (x₀ x₁ : Nat) : swapAdd x₀ x₁ = x₀ + x₁ := by
  induction x₀, x₁ using swapAdd.induct with
  | case1 x₁ => simp [swapAdd]
  | case2 x₀' x₁ ih => simp [swapAdd, ih]; omega

/-! ### Automated SCG extraction

Instead of constructing the size-change graph by hand (as in `swapAddGraph`
above), we can describe the equations syntactically and let `extractAllSCGs`
compute the graph automatically. -/

/-- Swapped addition as a list of equations in our AST. -/
def swapAddEqs : List Equation := [
  -- swapAdd(0, x₁) = x₁
  { patterns := [.ctor "zero" [], .var "x₁"],
    body := .var "x₁" },
  -- swapAdd(suc(x₀'), x₁) = suc(swapAdd(x₁, x₀'))
  { patterns := [.ctor "succ" [.var "x₀'"], .var "x₁"],
    body := .ctor "succ" [.recCall [.var "x₁", .var "x₀'"]] }
]

/-- Graphs extracted automatically from the equations. -/
def swapAddExtracted : List SCGraph := extractAllSCGs swapAddEqs

-- Equation 1 has no recursive calls; equation 2 has one.
-- The extracted graph has the same edges as the hand-written `swapAddGraph`
-- (possibly in a different order).
#eval swapAddExtracted.map toString
-- ["SCGraph(2 → 2): [0 ->→ 1, 1 -≥→ 0]"]

-- Run SCT on the extracted graph
#eval match swapAddExtracted with
  | [g] => g.checkSCT
  | _ => false
-- true

-- Confirm that composing the extracted graph with itself gives strict diagonal
#eval match swapAddExtracted with
  | [g] => (g.comp g).hasStrictDiag
  | _ => false
-- true

/-! #### A second example: Ackermann

Lean's built-in termination checker handles Ackermann with lexicographic order.
Our extractor produces the size-change graphs purely from the patterns and
argument shapes:

  A(0, x₁)                = suc(x₁)
  A(suc(x₀'), 0)          = A(x₀', 1)
  A(suc(x₀'), suc(x₁'))   = A(x₀', A(suc(x₀'), x₁'))
-/

def ackEqs : List Equation := [
  { patterns := [.ctor "zero" [], .var "x₁"],
    body := .ctor "succ" [.var "x₁"] },
  { patterns := [.ctor "succ" [.var "x₀'"], .ctor "zero" []],
    body := .recCall [.var "x₀'", .ctor "succ" [.ctor "zero" []]] },
  { patterns := [.ctor "succ" [.var "x₀'"], .ctor "succ" [.var "x₁'"]],
    body := .recCall [
      .var "x₀'",
      .recCall [.ctor "succ" [.var "x₀'"], .var "x₁'"]
    ] }
]

-- Expect three graphs (one per recursive call):
--   eq 2 → [(0 ->→ 0)]                       (x₀' strict-inside suc x₀')
--   eq 3 outer → [(0 ->→ 0)]                 (x₀' strict-inside suc x₀')
--   eq 3 inner → [(0 -≥→ 0, 1 ->→ 1)]        (suc x₀' = pattern 0, x₁' strict-inside suc x₁')
#eval (extractAllSCGs ackEqs).map toString

/-! ### Multi-graph SCT: closure + idempotent check

The single-graph `checkSCT` only checks whether successive powers of ONE
graph eventually yield a strict diagonal. The full SCT principle requires
that every **idempotent** graph in the composition-closure of the entire
call-set has a strict self-loop. This handles cases like Ackermann where
termination is lexicographic (no single graph has strict self-loops on
every parameter).
-/

-- Single-graph case: swapAdd still passes under the multi-graph check
#eval SCGraph.checkMultiSCT (extractAllSCGs swapAddEqs)  -- true

-- The closure contains swapAdd's graph G plus G² = [(0 ->→ 0), (1 ->→ 1)]
-- and compositions G∘G² = G²∘G = [(0 ->→ 1), (1 ->→ 0)].
#eval (SCGraph.closure (extractAllSCGs swapAddEqs)).map toString

-- Ackermann: multi-graph SCT now passes thanks to the improved extractor
#eval SCGraph.checkMultiSCT (extractAllSCGs ackEqs)  -- true

-- Closure of the Ackermann graph set
#eval (SCGraph.closure (extractAllSCGs ackEqs)).map toString

-- Counterexample: a contrived graph where one call swaps and neither arg decreases.
-- No strict edges at all, so no idempotent can have a strict self-loop.
def badSwap : List SCGraph := [
  { dom := 2, codom := 2, edges := [⟨0, 1, .nonstrict⟩, ⟨1, 0, .nonstrict⟩] }
]
#eval SCGraph.checkMultiSCT badSwap  -- false

/-- A non-terminating recursion extracted end-to-end from its equation AST:
    `loop(x, y) = loop(y, x)` — a pure swap with no descent. -/
def loopEqs : List Equation := [
  { patterns := [.var "x", .var "y"],
    body := .recCall [.var "y", .var "x"] }
]

-- The extracted graph is [(0 -≥→ 1), (1 -≥→ 0)]: a nonstrict swap.
#eval (extractAllSCGs loopEqs).map toString
-- Squaring it gives [(0 -≥→ 0), (1 -≥→ 1)], which is idempotent but has NO strict
-- self-loop — so the multi-SCT check correctly rejects it.
#eval SCGraph.checkMultiSCT (extractAllSCGs loopEqs)  -- false

/-! ### The `cyclic_def` macro in action

Instead of manually writing the `def ... termination_by ...` and the
`swapAddEqs : List Equation` separately, we can ask the `cyclic_def`
command to do both at once. It emits:

  1. a normal `def` with `termination_by a₀ + a₁` (hard-coded sum measure)
  2. a `#eval` that prints the SCGs extracted from the user's equations
-/

-- Without `cyclic_def`, Lean's auto-termination fails on the swapped call:
--
--   def swapAddFail : Nat → Nat → Nat
--     | 0, x₁        => x₁
--     | .succ x₀', x₁ => .succ (swapAddFail x₁ x₀')
--
-- gives "failed to infer structural recursion … Could not find a decreasing
-- measure". The sum-of-args measure (a₀ + a₁) works, and `cyclic_def` finds
-- it automatically.
cyclic_def swapAdd2 : Nat → Nat → Nat
  | 0, y        => y
  | .succ x', y => .succ (swapAdd2 y x')

-- Verify the emitted def behaves like swapAdd.
-- (Sum measure synthesized: `a₀ + a₁` — swapAdd's single graph has no self-
-- loops, so lex fails, and sum works because each callee arg matches exactly
-- one caller param, with one strict descent.)
#eval swapAdd2 3 5   -- 8
#eval swapAdd2 0 42  -- 42
#eval swapAdd2 10 0  -- 10

/-! ### A case that forces lex synthesis: Ackermann

Sum-of-args does NOT work for Ackermann (`A(suc x, 0) → A(x, 1)` keeps the
sum equal), but lex on `(x, y)` does. `cyclic_def` should detect that lex
succeeds and emit `termination_by _ _ => (a₀, a₁)`.
-/

cyclic_def ack2 : Nat → Nat → Nat
  | 0, y               => .succ y
  | .succ x, 0         => ack2 x (.succ .zero)
  | .succ x, .succ y   => ack2 x (ack2 (.succ x) y)

#eval ack2 2 3    -- 9
#eval ack2 3 3    -- 61
#eval ack2 0 10   -- 11

/-! ### Enforcement: failing `cyclic_def`

Now that the macro runs `checkMultiSCT` at elaboration time, an obviously
non-terminating recursion like a pure swap is rejected with a compile
error rather than producing a bogus `def`. The `#guard_msgs` block below
captures the expected error so the build doesn't fail.
-/

/--
error: cyclic_def 'loopDef': multi-SCT check FAILED.
Extracted graphs:
  SCGraph(2 → 2): [0 -≥→ 1, 1 -≥→ 0]
Some idempotent in the composition-closure has no strict self-loop, so no SCT-based measure exists.
-/
#guard_msgs in
cyclic_def loopDef : Nat → Nat → Nat
  | x, y => loopDef y x
