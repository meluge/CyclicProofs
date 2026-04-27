import CyclicTactic.Tactic


set_option warningAsError false



/-! ### Standard Lean -/

theorem addComm_std (n m : Nat) : n + m = m + n := by
  induction n generalizing m with
  | zero => 
    rw [Nat.zero_add]
    rw [Nat.add_zero]
  | succ n' ih_n' =>
    rw [Nat.succ_add]
    rw [Nat.add_succ]
    apply congrArg Nat.succ
    exact ih_n' m

/-! ### Cyclic -/

cyclic_thm addComm_cyc (n m : Nat) : n + m = m + n by
  cyclic R
  cyc_cases n with
  | zero => 
    rw [Nat.zero_add]
    rw [Nat.add_zero]
  | succ n' =>
    rw [Nat.succ_add]
    rw [Nat.add_succ]
    apply congrArg Nat.succ
    back R {n := n', m := m}




/-! ## Example 2: Ackermann totality -/

def myAck : Nat → Nat → Nat
  | 0,     n     => n + 1
  | m + 1, 0     => myAck m 1
  | m + 1, n + 1 => myAck m (myAck (m + 1) n)

/-! ### Standard Lean -/

theorem ackTotal_std (m n : Nat) : ∃ z, myAck m n = z := by
  induction m generalizing n with
  | zero => exact ⟨n + 1, by simp [myAck]⟩
  | succ m' ih_m' =>
    induction n with
    | zero =>
      simp only [myAck]
      exact ih_m' 1                       -- uses OUTER IH
    | succ n' ih_n' =>
      simp only [myAck]
      exact ih_m' (myAck (m' + 1) n')      -- uses OUTER IH again
                                          -- (ih_n' bound but never used!)

/-! ### Cyclic -/

cyclic_thm ackTotal_cyc (m n : Nat) : ∃ z, myAck m n = z by
  cyclic R
  cyc_cases m with
  | zero => exact ⟨n + 1, by simp [myAck]⟩
  | succ m' =>
    cyc_cases n with
    | zero =>
      simp only [myAck]
      back R {m := m', n := 1}
    | succ n' =>
      simp only [myAck]
      back R {m := m', n := myAck (Nat.succ m') n'}

