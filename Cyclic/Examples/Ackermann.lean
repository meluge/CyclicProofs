import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Annotation
import Cyclic.Reorganize
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic
import Cyclic.Examples.Advanced  -- for `ack`

/-!
# Ackermann totality (Wehr Fig. 4 / Grotenhuis-Otten Example 4.2)

The canonical paper-faithful demonstration: prove `∀ m n, ∃ z, ack m n = z`
cyclically. Exercises:

  * `exists` (∃R) — the base case witness `n + 1` and the inductive
    cases' implicit witness via the IH.
  * Two back-edges in the `succ m'` arm, both descending on `m` (lex
    `(m, n)` measure).
  * The non-trivial substitution `{m := m', n := ack (succ m') n'}` —
    the second back-edge instantiates the IH at an `ack`-application
    (not a simple constructor pattern). Tests our `termToLean` rendering
    of `SubjectTerm.ctor "ack" […]`.

Note on Lean's `ack`: `ack` is defined functionally (terminates by lex
`(m, n)`), so `∃ z, ack m n = z` is *technically* provable by
`⟨ack m n, rfl⟩` directly. The cyclic proof here demonstrates the
*structural* unravelling of the totality theorem — the structural
emitter routes each back-edge through the corresponding lex-IH.
-/

-- Inline-goal form: the existential goal lives directly in the theorem
-- statement, no separate `def ackTotal` required.
cyclic_thm ackTotal_all (m n : Nat) : ∃ z, ack m n = z by_cyclic
  R: cases m with
    | 0 =>
      -- ack 0 n = n + 1, so the witness is n + 1.
      exists n + 1
      done by simp [ack]
    | succ m' =>
      cases n with
        | 0 =>
          -- ack (succ m') 0 = ack m' 1, so the IH at {m := m', n := 1}
          -- gives the witness directly. `simp only [ack]` unfolds the
          -- LHS; `recurse` substitutes for `exact ih_m' 1`.
          back R {m := m', n := 1} by
            simp only [ack]
            recurse
        | succ n' =>
          -- ack (succ m') (succ n') = ack m' (ack (succ m') n').
          -- IH at {m := m', n := ack (succ m') n'} gives exactly the
          -- needed shape.
          back R {m := m', n := ack (succ m') n'} by
            simp only [ack]
            recurse

example (m n : Nat) : ∃ z, ack m n = z := ackTotal_all m n
