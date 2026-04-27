import CyclicTactic.Tactic

/-!
# v0.5 smoke test — tree-building cyclic proof system

`cyc_cases` now manually elaborates each arm and pushes
`caseSplitStart`/`armStart`/`armEnd`/`caseSplitEnd` events to the cyclic
state, so the Phase-B finalizer (next turn) can reconstruct a real
`ProofTree` value.

`back R {σ}` continues to issue a recursive call (interactive layer
that closes the goal in real time), and ALSO records a `.back` event
into the cyclic state.

After elaborating each theorem, `cyc_state` shows the recorded events
as an indented tree — the structure the Phase-B builder will turn into
a `ProofTree`.

The proofs are still kernel-checked the same way as v0.4 (recursive
def + Lean's structural recursion).
-/

/-! ### Example 1: zeroAddT with `cyc_cases` -/

cyclic_thm zeroAddT (n : Nat) : 0 + n = n by
  cyclic R
  cyc_cases n with
  | zero => rfl
  | succ n' =>
    show Nat.succ (0 + n') = Nat.succ n'
    apply congrArg Nat.succ
    back R {n := n'}

example : True := by
  cyc_state
  trivial

/-! ### Example 2: addCommT — two-arg lex-style with cyc_cases -/

cyclic_thm addCommT (n m : Nat) : n + m = m + n by
  cyclic R
  cyc_cases n with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ n' =>
    rw [Nat.succ_add, Nat.add_succ]
    apply congrArg Nat.succ
    back R {n := n', m := m}

example : True := by
  cyc_state
  trivial

/-! ### Reverse-arm test: back-edge in the FIRST arm

Demonstrates that position-based attribution isn't just "last arm wins" —
here the inductive case is `succ` written FIRST. The tree builder
should still attribute the back-edge to the right arm via positions. -/

cyclic_thm zeroAddRev (n : Nat) : 0 + n = n by
  cyclic R
  cyc_cases n with
  | succ n' =>
    show Nat.succ (0 + n') = Nat.succ n'
    apply congrArg Nat.succ
    back R {n := n'}
  | zero => rfl

/-! ### Manual test: does the Unravel-emitted form actually work?

We hand-elaborate the exact script Unravel emitted for `zeroAddRev`.
Expected: `simp` closes the zero case, but the succ case `exact ih_n'`
fails because the goal is `0 + Nat.succ n' = Nat.succ n'` (not yet
reduced to `0 + n' = n'`). To make the emission self-elaborating we'd
need to capture per-arm preludes (`apply congrArg Nat.succ`, etc.). -/

set_option warningAsError false in
theorem zeroAddRev_emitted_attempt (n : Nat) : 0 + n = n := by
  induction n with
  | succ n' ih_n' =>
    show Nat.succ (0 + n') = Nat.succ n'
    apply congrArg Nat.succ
    exact ih_n'
  | zero => simp

/-! ### Sanity check: proofs still kernel-clean -/

/-- info: 'zeroAddT' does not depend on any axioms -/
#guard_msgs in #print axioms zeroAddT

/-- info: 'addCommT' does not depend on any axioms -/
#guard_msgs in #print axioms addCommT

example (k : Nat) : 0 + k = k := zeroAddT k
example (a b : Nat) : a + b = b + a := addCommT a b
