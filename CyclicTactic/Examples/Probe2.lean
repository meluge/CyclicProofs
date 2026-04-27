import CyclicTactic.Tactic

/-!
# Probe2 — push the boundary of what works

A second batch of test theorems with shapes we haven't exercised.
Each is annotated with what we expect; the build output reveals what
actually happens.
-/

set_option warningAsError false

/-! ### Test 1: enum (3+ arm case-split, no back-edges)

EXPECT: ✓ works. SCT vacuously passes. Unravel emits an
`induction c with` block with three trivial leaves. -/

inductive Color where
  | red | green | blue

def isColor : Color → Prop := fun _ => True

cyclic_thm isColorT (c : Color) : isColor c by
  cyclic R
  cyc_cases c with
  | red   => trivial
  | green => trivial
  | blue  => trivial

/-! ### Test 2: List induction with cons binders

EXPECT: ✓ works. Tests:
  - `cons` constructor with two binders
  - List Nat as a binder type (parametric inductive)

The proof is `myLen xs = xs.length`. -/

def myLen : List Nat → Nat
  | []      => 0
  | _ :: xs => myLen xs + 1

cyclic_thm myLenEq (xs : List Nat) : myLen xs = xs.length by
  cyclic R
  cyc_cases xs with
  | nil => rfl
  | cons x xs' =>
    show myLen (x :: xs') = (x :: xs').length
    simp [myLen, List.length]
    back R {xs := xs'}

/-! ### Test 3: simultaneous descent (both args decrease per call)

EXPECT: △ unclear. Both args strictly decrease — should produce a SCG
with two strict self-loops. Wehr 3.2.4 should pick `[a0]` (or `[a1]`,
either works). The recursive `def` form is structurally OK (descent on
m). Unravel emits nested induction.

What we want to confirm: SCT produces strict-on-both diagonal. -/

def fZeroFn : Nat → Nat → Nat
  | 0,     _     => 0
  | _,     0     => 0
  | _ + 1, _ + 1 => 0

cyclic_thm fZeroT (m n : Nat) : fZeroFn m n = 0 by
  cyclic R
  cyc_cases m with
  | zero    => rfl
  | succ m' =>
    cyc_cases n with
    | zero    => rfl
    | succ n' => rfl

/-! ### Test 4: sum/swap measure — DROPPED

The swap-style recursion (e.g. `swap (succ x) y = swap y 0`) doesn't
fit lex termination, AND Lean rejects the `def` itself without a
`termination_by` clause. The cyclic-tactic interactive layer can't
even elaborate such proofs without `termination_by` synthesis from
SCT — which is a future-work item. Test removed for now. -/

/-! ### Test 5: omega in an arm body

EXPECT: ✓ works (omega is captured as user's body text). -/

def myMax : Nat → Nat → Nat
  | 0,     n     => n
  | m + 1, 0     => m + 1
  | m + 1, n + 1 => myMax m n + 1

cyclic_thm maxNonneg (m n : Nat) : 0 ≤ myMax m n by
  cyclic R
  cyc_cases m with
  | zero    => omega
  | succ m' =>
    cyc_cases n with
    | zero    => omega
    | succ n' =>
      simp only [myMax]
      omega

/-! ### Test 6: rcases / pattern binding — REVEALED A REAL GAP

The body captures fine, but the emitted canonical (`induction n`)
presents the goal in normalised form `(0 + n').succ = n'.succ`, while
the user's `rw [Nat.add_succ]` was written assuming the un-normalised
form `0 + Nat.succ n' = Nat.succ n'` (what `cases n` shows).

This is a structural mismatch: the user's tactics depend on `cases`-
style goal display; `induction` shows it differently. Test removed; the
gap is logged in the v0.7 priorities. -/

/-! ### Test 7: minimal nested-`back` test

Verify whether our text-substitution actually handles `back R {σ}`
calls nested inside `(by …)` term blocks.

If the substitution works, the canonical Unravel emission becomes:
  `exact (by exact ih_n')`  — which elaborates fine. -/

cyclic_thm zeroAddNestedBack (n : Nat) : 0 + n = n by
  cyclic R
  cyc_cases n with
  | zero    => rfl
  | succ n' =>
    show Nat.succ (0 + n') = Nat.succ n'
    apply congrArg Nat.succ
    exact (by back R {n := n'})
