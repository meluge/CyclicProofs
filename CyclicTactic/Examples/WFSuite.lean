import CyclicTactic.Tactic

set_option warningAsError false

/-!
# WF-emission suite: cyclic proofs that need a well-founded measure

Companion to `MergeSort.lean`. Each example here is a `cyclic_thm` whose
recursion is *not* structural on any single argument, so the dispatcher
falls through `canStructural` to the WF backend, synthesises a measure
from the per-back-edge size-change graphs, and emits
`def … termination_by <measure> decreasing_by …`.

The point of the suite is to exercise the *distinct measure shapes* the
synthesiser/emitter can produce:

* `MergeSort.merge_length` (in `MergeSort.lean`) — **lex** measure
  `(xs.length, ys.length)`, recursion inside a recorded `cyc_by_cases`.
* `n2_holds` (below) — **sum** measure `x + y`, recursion that *swaps*
  its two arguments.

Cyclist first-order benchmark mapping: this is **Test 14**
(`N(x) ∧ N(y) ⊢ N2(x, y)`), previously documented in
`CyclistComparison.lean` as the WF-emission gap. It now goes through.
(It lives here, not in `CyclistComparison.lean`, because that file has a
pre-existing `SubjectTerm.toString` stack overflow that hangs the build.)
-/

namespace WFSuite

/-! ## Test 14 — `N2` with an argument-swapping recursion

```
N2 { N(y) ⇒ N2(0, y) | N2(y, x) ⇒ N2(s x, y) }
```

The `step` rule's premise is `N2(y, x)` but the conclusion is
`N2(s x, y)`: the recursive call **swaps** the two arguments. So neither
argument decreases on its own across the back-edge — position 0 goes
`y ⇝ s x` (can grow) and position 1 goes `x ⇝ y` (can grow) — but the
*sum* `x + y` strictly decreases (`y + x` at the call vs `(s x) + y`
in the conclusion). No single-argument structural induction witnesses
this; no lexicographic order does either (the swap defeats any fixed
priority). The WF backend synthesises `Measure.sum 2`, rendered as
`termination_by x + y`, and `decreasing_by simp_wf; omega` discharges it. -/

inductive N2p : Nat → Nat → Prop where
  | base (y : Nat) : N2p 0 y
  | step (x y : Nat) : N2p y x → N2p (Nat.succ x) y

-- Every `Nat` is `N2p`-related to every other, by the swapping recursion.
-- Emitted via the WF backend with the synthesised `sum` measure `x + y`.
cyclic_thm n2_holds (x y : Nat) : N2p x y by
  cyclic R
  cyc_cases x with
  | zero => exact N2p.base y
  | succ x' =>
    apply N2p.step x' y
    back R {x := y, y := x'}     -- swap: descends on the SUM x + y

-- The emitted `n2_holds` is a real, kernel-checked term.
example (x y : Nat) : N2p x y := n2_holds x y

/-! ## Test 15 — 2-Hydra: lex `(x, y)` with a *growing* back-edge

Cyclist first-order benchmark Test 15. Two heads `x` and `y`. Cutting the
first head (`dropX`) strips one `x` but REGROWS the second head
(`y → succ y`); `dropY` shrinks `y` while `x = 0`. Totality `∀ x y, Hyd x y`
needs the lexicographic measure `(x, y)`: on the `dropX` back-edge `x` drops
strictly (and `y` may grow — irrelevant under lex); on the `dropY` back-edge
`x` is fixed at `0` and `y` drops strictly. No single argument decreases on
both edges, and — unlike `merge_length` / `n2_holds` — one back-edge makes an
argument GROW (`back R {y := Nat.succ y}`).

That growing edge is what makes this the hardest of the WF examples: it
produces a *cyclic* path-substitution and an age-inverted name stack, which
exposed two non-termination bugs in the recorded-tree pipeline (both fixed):
`SubjectTerm.subst` looping on a cyclic σ (now occurs-guarded), and
`PaperAnnotation.resetLoop` spinning on a no-progress reset when the older
name sits above its coverer (now progress-guarded). With those fixed the
dispatcher synthesises `Measure.lex [0,1]` and emits a kernel-clean
`def … termination_by (x, y)`. -/

inductive Hyd : Nat → Nat → Prop where
  | base              : Hyd 0 0
  | dropY (y : Nat)   : Hyd 0 y → Hyd 0 (Nat.succ y)
  | dropX (x y : Nat) : Hyd x (Nat.succ y) → Hyd (Nat.succ x) y

-- NB: the arm WITHOUT a nested split (`succ x'`) comes FIRST and the arm WITH
-- the nested `cyc_cases y` comes LAST. The event recorder mis-attributes a
-- nested `cyc_cases` that sits in a non-final arm (the later sibling arm gets
-- absorbed into the inner split), so the nested split must be the last arm.
cyclic_thm hyd_total (x y : Nat) : Hyd x y by
  cyclic R
  cyc_cases x with
  | succ x' =>
    apply Hyd.dropX x' y
    back R {x := x', y := Nat.succ y}
  | zero =>
    cyc_cases y with
    | zero => exact Hyd.base
    | succ y' =>
      apply Hyd.dropY y'
      back R {x := 0, y := y'}

example (x y : Nat) : Hyd x y := hyd_total x y

end WFSuite
