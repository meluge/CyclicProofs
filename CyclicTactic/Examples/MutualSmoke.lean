import CyclicTactic.Tactic

set_option warningAsError false

/-!
# Mutual smoke test — `cyclic_mutual` baseline + §6 emission target

Isolated test file for the `cyclic_mutual` block. Holds the Od/Ev →
Nlike example from `CyclistComparison.lean` *without* the surrounding
content that triggers an unrelated crash in `SubjectTerm.toString`,
so we can iterate on Theorem 6.1 emission for mutual blocks against a
clean baseline.

The single judgement here is `Od n → Nlike n` / `Ev n → Nlike n`, a
canonical "cyclist-style" cross-companion proof: each entry has one
back-edge that targets the *other* entry's companion. Cyclist proves
this; the standard Lean version uses `mutual theorem` + structural
recursion on `h`.

Once mutual §6 emission is wired up, the synthesised body for each
entry should be `cases h with …` + a cross-theorem call (`exact
ev_is_nlike_cyc k h'`) for the recursive arm.
-/

/-! ### Inductive predicates -/

inductive Nlike : Nat → Prop where
  | zero : Nlike 0
  | succ (n : Nat) : Nlike n → Nlike (Nat.succ n)

mutual
  inductive Ev : Nat → Prop where
    | zero : Ev 0
    | succ (n : Nat) : Od n → Ev (Nat.succ n)
  inductive Od : Nat → Prop where
    | succ (n : Nat) : Ev n → Od (Nat.succ n)
end

/-! ### Standard Lean baseline — what we want §6 emission to produce -/

mutual
  theorem od_is_nlike_std : ∀ n, Od n → Nlike n
    | _, .succ k h => .succ _ (ev_is_nlike_std k h)
  theorem ev_is_nlike_std : ∀ n, Ev n → Nlike n
    | _, .zero      => .zero
    | _, .succ k h  => .succ _ (od_is_nlike_std k h)
end

/-! ### Cyclic — using `cyclic_mutual ... end_mutual`

Each entry registers its own companion (`R_O`, `R_E`). Cross-companion
back-edges (`back R_E {…}` from inside the Od-side, `back R_O {…}`
from inside the Ev-side) resolve via the mutual companion table.
Currently elaborates as a recursive `mutual def`; the §6 emitter does
NOT yet handle mutual blocks. -/

cyclic_mutual
  thm od_is_nlike_cyc (n : Nat) (h : Od n) : Nlike n by
    cyclic R_O
    cyc_cases h with
    | succ k h' =>
      apply Nlike.succ
      back R_E {n := k, h := h'}
  thm ev_is_nlike_cyc (n : Nat) (h : Ev n) : Nlike n by
    cyclic R_E
    cyc_cases h with
    | zero      => exact Nlike.zero
    | succ k h' =>
      apply Nlike.succ
      back R_O {n := k, h := h'}
end_mutual

example (n : Nat) (h : Od n) : Nlike n := od_is_nlike_cyc n h
example (n : Nat) (h : Ev n) : Nlike n := ev_is_nlike_cyc n h
