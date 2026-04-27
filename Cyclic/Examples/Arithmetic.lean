import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic

/-!
# Cyclic Proofs of Standard Arithmetic Theorems

Real Lean theorems with non-trivial content, proved cyclically. These
exercise the structural emission path on substantive predicates — not
the trivial-`True` placeholders in `Advanced.lean#threeR_all`.

Each example is also expressible by `induction` directly; the value of
writing them cyclically is that the *structure* of the proof (case-
splits + back-edges) is decoupled from the choice of induction
principle (now mechanically extracted by SCT + the annotation pass).
-/

/-! ### 1. `0 + n = n` — zero as left-additive identity

`Nat.add` in Lean recurses on its *second* argument, so `n + 0 = n` is
definitional but `0 + n = n` requires induction on `n`. Single back-
edge, single var. -/

cyclic_thm zeroAdd_cyc (n : Nat) : 0 + n = n by_cyclic
  cases n with
    | 0       => done by rfl
    | succ n' => back {n := n'} by
        show Nat.succ (0 + n') = Nat.succ n'
        apply congrArg Nat.succ
        recurse

example (n : Nat) : 0 + n = n := zeroAdd_cyc n

/-! ### 2. `n + m = m + n` — commutativity of addition

Two variables, single induction on `n` with `m` generalised. The IH at
`succ n'` has type `∀ m, n' + m = m + n'` — universal in `m` because
`induction n generalizing m`. The back-edge `back {n := n'}` becomes
`exact ih_n' m` in emission: the path substitution doesn't bind `m`
(no case-split has narrowed it), so the bare name is preserved. -/

cyclic_thm addComm_cyc (n : Nat) (m : Nat) : n + m = m + n by_cyclic
  cases n with
    | 0       => done by rw [Nat.zero_add, Nat.add_zero]
    | succ n' => back {n := n'} by
        rw [Nat.succ_add, Nat.add_succ]
        apply congrArg Nat.succ
        recurse

example (n m : Nat) : n + m = m + n := addComm_cyc n m

/-! ### 3. `(a + b) + c = a + (b + c)` — associativity of addition

Three variables, single induction on `c` (the second arg of `+`). IH at
`succ c'` is `∀ a b, (a + b) + c' = a + (b + c')` — universal in both
`a` and `b`. The back-edge supplies them via path-substitution (still
their bare names: no enclosing case-split binds them). -/

cyclic_thm addAssoc_cyc (a : Nat) (b : Nat) (c : Nat) : (a + b) + c = a + (b + c) by_cyclic
  cases c with
    | 0       => done by rfl
    | succ c' => back {c := c'} by
        show Nat.succ ((a + b) + c') = Nat.succ (a + (b + c'))
        apply congrArg Nat.succ
        recurse

example (a b c : Nat) : (a + b) + c = a + (b + c) := addAssoc_cyc a b c

/-! ### 4. `0 + n = n` with an explicit `have` (Cut / intermediate lemma)

Same proof shape as `zeroAdd_cyc` but uses `have` to name the unfolding
step `0 + Nat.succ n' = Nat.succ (0 + n')` as a local lemma `hUnfold`,
then references it via `rw` in the back-edge's tactic block.

The `have` step doesn't change the trace SCG (it's not a case-split,
doesn't substitute root variables, and isn't a back-edge target). The
SCT analysis sees through it to the back-edge directly. The structural
emitter outputs the `have` verbatim before the rest of the tactic body,
preserving the user's intermediate-lemma structure in the kernel-checked
output.

This is the analogue of Wehr's Cut rule (Ch 2 / 3) and the paper's
typical `Cut` step in CHA proofs (e.g. Fig. 4 — Ackermann totality
proof — which uses Cut to introduce `A(Sx, y, z')` before `∃L`). -/

cyclic_thm zeroAdd_have (n : Nat) : 0 + n = n by_cyclic
  cases n with
    | 0       => done by rfl
    | succ n' =>
      have hUnfold : 0 + Nat.succ n' = Nat.succ (0 + n') := by rfl
      back {n := n'} by
        rw [hUnfold]
        apply congrArg Nat.succ
        recurse

example (n : Nat) : 0 + n = n := zeroAdd_have n

/-! ### 5. Existential goal via `exists` (∃R) step

A cyclic proof whose conclusion is an existential. The `exists <term>`
DSL step provides the witness, leaving the continuation to prove
`φ[witness/x]` — Wehr / Grotenhuis-Otten's ∃R rule. After the witness,
the rest of the proof proceeds as usual (`done`, `back`, etc.).

The key Lean-side translation: `exists t` emits `refine ⟨t, ?_⟩`, which
peels the existential and leaves the residual goal for the continuation.
-/

def existsEq (n : Nat) : Prop := ∃ m, m = n

cyclic_thm existsEq_all (n : Nat) : existsEq n by_cyclic
  cases n with
    | 0 =>
      -- Witness: 0. Residual goal `(0 : Nat) = 0`, closed by rfl.
      exists 0
      done by simp [existsEq]
    | succ n' =>
      -- Witness: Nat.succ n'. Residual goal `Nat.succ n' = Nat.succ n'`.
      exists Nat.succ n'
      done by simp [existsEq]

example (n : Nat) : ∃ m, m = n := existsEq_all n
