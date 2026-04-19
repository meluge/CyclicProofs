import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic

/-!
# Validating WF emission: a cyclic proof nested induction can't express

The previous examples (myP, myQ, myB, myL, myT, …) all happen to have a
case-split tree that aligns with what Lean's structural / nested
`induction` accepts. So while the new WF-recursion emission
(`termination_by` with the SCT-synthesized measure) is **paper-faithful**,
it didn't *enable* anything beyond presentation on those examples.

This file gives an example where it does enable something new: a
**swap-style** cyclic proof whose back-edge re-binds *both* arguments,
swapping them. Neither variable strictly decreases on its own, so no
`induction` on a single variable suffices — the cyclic-proof's
soundness rests on the **sum** measure `x + y`, which Lean's structural
induction can't express directly. WF emission with `termination_by` can.

## The predicate

```
swapP 0       y = ⊤
swapP (suc x) y = swapP y x      -- recursive call swaps the args
```

Itself a `cyclic_def`-style definition (we just hand-write the
`termination_by`). Lean accepts it because `y + x < (suc x) + y` is the
sum-measure decrease.

## The cyclic proof of `∀ x y, swapP x y`

```
[R]  swapP(x, y)                       (case-split on x)
 ├── 0      => leaf (unfold ⇒ ⊤)
 └── suc x' => swapP(suc x', y)         unfold ⇒ swapP(y, x')
       └── back to R via σ = {x ↦ y, y ↦ x'}
```

Trace at the back-edge: under the path-substitution `[(x, suc x')]`, the
ancestor's args become `[suc x', y]`. The back-edge's args are `[y, x']`.

  * Slot 0 → slot 1: `x'` is a strict subterm of `suc x'`. Edge `0 ->→ 1`.
  * Slot 1 → slot 0: `y` is structurally equal to `y`. Edge `1 -≥→ 0`.

Composing this graph with itself yields edges `0 ->→ 0` and `1 ->→ 1`
(both diagonal, both strict) — every idempotent in the closure has a
strict self-loop. SCT passes.

The `synthMeasure` function tries lex first: at slot 0 the graph has
*no* self-loop (the strict edge goes off-diagonal to slot 1), so lex on
`[0, 1]` fails. It then tries sum: every callee arg matches a caller
slot (with the swap bijection), and at least one match is strict. Sum
works → `Measure.sum 2`, rendered as `x + y`.

That `x + y` is exactly what nested induction can't capture but
`termination_by` can — the WF emission carries it into Lean.
-/

def swapP : Nat → Nat → Prop
  | 0,        _ => True
  | .succ x', y => swapP y x'
termination_by x y => x + y

cyclic_thm swapP_all (x : Nat) (y : Nat) : swapP x y by_cyclic
  cases x with
    | 0       => done by simp [swapP]
    | succ x' => back {x := y, y := x'} by
        simp [swapP]
        recurse

/-! ### Verify it elaborates as a real theorem -/

example : swapP 7 11      := swapP_all 7 11
example (a b : Nat) : swapP a b := swapP_all a b

#check @swapP_all   -- ∀ (x y : Nat), swapP x y

/-!
The emission for `swapP_all` should look like

```
def swapP_all : ∀ (x : Nat) (y : Nat), swapP x y := fun x y =>
  match x with
  | 0           => by simp [swapP]
  | (Nat.succ x') => by simp [swapP]; exact swapP_all y x'
termination_by x y => x + y
```

The `termination_by x y => x + y` clause is the cyclic proof's
soundness witness, synthesized from the SCT graph by `synthMeasure`.
The recursive call `swapP_all y x'` swaps the args; Lean's well-founded
recursion accepts because `y + x' < (Nat.succ x') + y`.
-/
