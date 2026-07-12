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

/-! ## Test 13 — Sprenger–Dam two-step descent via a PHASE argument

Cyclist benchmark Test 13 (R/R2). A two-phase predicate: `flip` moves the
`Bool` phase `true ⟶ false` with `n` PRESERVED; `down` moves `false ⟶ true`
while shrinking `n`. The cycle alternates phases, and the only progress on the
`flip` step lives in the phase, not in `n` — so NO size-change on the inductive
argument `n` decreases on every back-edge, and the structural extractor sees
the `Bool` transition as stagnation. This is the case that fails the plain SCT
gate (GAP1-FINDINGS tier T2).

GAP-2 PHASE-AWARE EXTRACTION handles it: the `flip` back-edge is "stalled"
(no structural strict descent), so its phase transition `true ⟶ false` is
*required* strict, forcing the order `true > false`; `down`'s phase transition
is then a (free) increase covered by `n`'s structural descent. The solver finds
this order is consistent (acyclic), patches a strict self-loop at the phase
position, and the synthesised measure becomes lex `(n, phaseRank b)` with
`phaseRank` rendered as `match b with | true => 1 | false => 0`. Emits a
kernel-clean `def … termination_by (n, match b with …)`. A genuinely
non-terminating phase cycle (progress nowhere) would make the order cyclic and
be correctly REJECTED (→ recursive fallback), so the augmentation is sound. -/

inductive Ph : Nat → Bool → Prop where
  | base : Ph 0 true
  | flip (n : Nat)  : Ph n true  → Ph n false
  | down (n : Nat)  : Ph n false → Ph (Nat.succ n) true

cyclic_thm ph_total (n : Nat) (b : Bool) : Ph n b by
  cyclic R
  cyc_cases b with
  | false =>
    apply Ph.flip n
    back R {n := n, b := true}
  | true =>
    cyc_cases n with
    | zero => exact Ph.base
    | succ n' =>
      apply Ph.down n'
      back R {n := n', b := false}

example (n : Nat) (b : Bool) : Ph n b := ph_total n b

/-! ## Test 13b — three-state phase: a `>` b `>` c order solved from TWO stalled edges

`ph_total` exercises the phase mechanism only in its easy corner: a 2-element
phase (`Bool`), a single stalled back-edge, and a trivial 2-element order. The
parts of the GAP-2 machinery that a 2-state phase never touches are:

* `rankConstructors` building a topological chain LONGER than 2;
* the emitter rendering a `match` over THREE-plus constructors;
* MULTIPLE stalled-edge constraints composing into one consistent order.

This example stresses exactly those. The phase domain `Tri` has three nullary
constructors and the cycle runs `a ⟶ c ⟶ b ⟶ a`, with the strict `Nat`
descent living ONLY on the `a`-step (`to_a : Q n c → Q (succ n) a`). The other
two steps preserve `n`, so their back-edges are *stalled*:

* `b`-arm: `Q n b` ← `Q n a`  — back-edge `(n,b) ⟶ (n,a)`, `n` preserved ⇒
  STALLED ⇒ phase `b ⟶ a` required strict ⇒ `b > a`;
* `c`-arm: `Q n c` ← `Q n b`  — back-edge `(n,c) ⟶ (n,b)`, `n` preserved ⇒
  STALLED ⇒ phase `c ⟶ b` required strict ⇒ `c > b`;
* `a`-arm (`succ`): `Q (succ n') a` ← `Q n' c` — `n` STRICT, not stalled; the
  phase `a ⟶ c` is a free increase carried by the `n` descent.

The solver composes `{b > a, c > b}` into the chain `a < b < c` (ranks
`a:0, b:1, c:2`) and patches a strict self-loop on the phase position of both
stalled edges. Measure becomes lex `(n, phaseRank t)` with `phaseRank` rendered
as `match t with | Tri.a => 0 | Tri.b => 1 | Tri.c => 2`. Unlike `ph_total`,
this also checks that `buildSortInfo` enumerates a *user-defined* enum's
constructors (not just built-in `Bool`) and that the emitter renders the match
patterns with FULLY-QUALIFIED ctor names (a bare lowercase `a` would parse as a
catch-all variable, silently swallowing the match). -/

inductive Tri where | a | b | c

inductive Q : Nat → Tri → Prop where
  | base                : Q 0 Tri.a
  | to_b (n : Nat)      : Q n Tri.a → Q n Tri.b
  | to_c (n : Nat)      : Q n Tri.b → Q n Tri.c
  | to_a (n : Nat)      : Q n Tri.c → Q (Nat.succ n) Tri.a

-- Arms with NO nested split (`b`, `c`) come first; the arm WITH the nested
-- `cyc_cases n` (`a`) comes LAST (same event-recorder constraint as `hyd_total`).
cyclic_thm q_total (n : Nat) (t : Tri) : Q n t by
  cyclic R
  cyc_cases t with
  | b =>
    apply Q.to_b n
    back R {n := n, t := Tri.a}
  | c =>
    apply Q.to_c n
    back R {n := n, t := Tri.b}
  | a =>
    cyc_cases n with
    | zero => exact Q.base
    | succ n' =>
      apply Q.to_a n'
      back R {n := n', t := Tri.c}

example (n : Nat) (t : Tri) : Q n t := q_total n t

end WFSuite
