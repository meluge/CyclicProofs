import CyclicTactic.Tactic

/-!
# Probe examples — what works, what doesn't

A battery of test theorems with different shapes, to map the boundary
of what the v0.5 cyclic-tactic system handles.

Each example is annotated with what we expect (`✓ works`, `△ partial`,
`✗ fails`) and what the failure mode is.
-/

set_option warningAsError false

/-! ### Test 1: associativity (3 args, structural on c)

EXPECT: ✓ works.
- 3 binders (a, b, c)
- single back-edge descending on c (position 2)
- Wehr 3.2.4 should pick `lex [a2]`
- Lean's structural recursion should accept (descent on the last arg) -/

cyclic_thm assocT (a b c : Nat) : (a + b) + c = a + (b + c) by
  cyclic R
  cyc_cases c with
  | zero => rfl
  | succ c' =>
    show Nat.succ ((a + b) + c') = Nat.succ (a + (b + c'))
    apply congrArg Nat.succ
    back R {a := a, b := b, c := c'}

/-! ### Test 2: Ackermann totality (lex on (m, n))

EXPECT: △ partial.
- Two back-edges both targeting R, both descending on m
- Existential goal `∃ z, ack m n = z`
- Wehr 3.2.4 should pick `lex [a0]` (just m)
- Lean's STRUCTURAL recursion will likely fail because the recursion
  doesn't always descend on the same single arg without `termination_by`. -/

def ack' : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => ack' m 1
  | m + 1, n + 1 => ack' m (ack' (m + 1) n)

cyclic_thm ackTotalT (m n : Nat) : ∃ z, ack' m n = z by
  cyclic R
  cyc_cases m with
  | zero =>
    exact ⟨n + 1, by simp [ack']⟩
  | succ m' =>
    cyc_cases n with
    | zero =>
      simp only [ack']
      back R {m := m', n := 1}
    | succ n' =>
      simp only [ack']
      back R {m := m', n := ack' (Nat.succ m') n'}

/-! ### Test 3: existsEq — back-free proof

EXPECT: ✓ works structurally; SCT trivially passes (no back-edges, so
no graphs); Wehr returns nothing useful but it's not needed. -/

cyclic_thm existsEqT (n : Nat) : ∃ m, m = n by
  cyclic R
  cyc_cases n with
  | zero => exact ⟨0, rfl⟩
  | succ n' => exact ⟨Nat.succ n', rfl⟩

/-! ### Test 4: multi-rec (BinTree)

EXPECT: △ partial.
- `node l r` arm produces 2 subgoals via `refine ⟨?_, ?_⟩`
- 2 back-edges in the same arm
- Our position-based attribution treats multi-event arms as
  "multi-event arm not yet supported" leaf
- Lean's structural recursion likely accepts (descent on subterms)
- BUT the reconstructed tree won't match what Unravel needs -/

inductive BTr where
  | leaf  : BTr
  | node  : BTr → BTr → BTr

def btPred : BTr → Nat → Prop
  | .leaf,     _ => True
  | .node l r, n => btPred l n ∧ btPred r n

cyclic_thm btPredT (t : BTr) (n : Nat) : btPred t n by
  cyclic R
  cyc_cases t with
  | leaf => trivial
  | node l r =>
    refine ⟨?_, ?_⟩
    · back R {t := l, n := n}
    · back R {t := r, n := n}

/-! ### Test 5: have step

EXPECT: ✓ works. The `have` is internal (not recorded by our system);
should pass through transparently. -/

cyclic_thm zeroAddHaveT (n : Nat) : 0 + n = n by
  cyclic R
  cyc_cases n with
  | zero => rfl
  | succ n' =>
    have hUnfold : 0 + Nat.succ n' = Nat.succ (0 + n') := by rfl
    rw [hUnfold]
    apply congrArg Nat.succ
    back R {n := n'}

/-! ### Test: hand-elaborate the Unravel-emitted scripts to verify -/

theorem zeroAddT_unravel (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n' ih_n' =>
    show Nat.succ (0 + n') = Nat.succ n'
    apply congrArg Nat.succ
    exact ih_n'

theorem addCommT_unravel (n m : Nat) : n + m = m + n := by
  induction n generalizing m with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ n' ih_n' =>
    rw [Nat.succ_add, Nat.add_succ]
    apply congrArg Nat.succ
    exact ih_n' m

theorem assocT_unravel (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c generalizing a b with
  | zero => rfl
  | succ c' ih_c' =>
    show Nat.succ ((a + b) + c') = Nat.succ (a + (b + c'))
    apply congrArg Nat.succ
    exact ih_c' a b

theorem ackTotalT_unravel (m n : Nat) : ∃ z, ack' m n = z := by
  induction m generalizing n with
  | zero =>
    exact ⟨n + 1, by simp [ack']⟩
  | succ m' ih_m' =>
    induction n with
    | zero =>
      simp only [ack']
      exact ih_m' (Nat.succ 0)
    | succ n' ih_n' =>
      simp only [ack']
      exact ih_m' (ack' (Nat.succ m') n')

theorem existsEqT_unravel (n : Nat) : ∃ m, m = n := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n' ih_n' => exact ⟨Nat.succ n', rfl⟩

/-- info: 'ackTotalT_unravel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ackTotalT_unravel
