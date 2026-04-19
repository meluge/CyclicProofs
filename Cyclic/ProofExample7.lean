import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic

/-!
# Real inductive theorems via cyclic proofs

The earlier examples (`myP_all`, `myL_all`, `worker_terminates`, …) all
prove predicates whose Prop content is `True` everywhere — the proof's
*structural* content is a termination argument, but the *propositional*
content is trivial.

This file demos the `by_cyclic` DSL's `by <tac>` clause, which lets a
cyclic-proof step close its goal with an arbitrary user tactic instead
of the default `simp [pred]` / `simp [pred]; exact ih_<v>`. With this,
the system becomes a frontend for genuinely non-trivial inductive
theorems where the IH applies to a *sub-position* of the goal rather
than the whole thing.

## Custom recursive `add`

Lean's `Nat.add` puts `+ 0` in the simp set, so `n + 0 = n` is closed
by `simp` without any cyclic-proof machinery. To make the example
genuinely require the IH, define `myAdd` ourselves so its equations
aren't auto-simped:
-/

def myAdd : Nat → Nat → Nat
  | 0,      y => y
  | .succ x, y => .succ (myAdd x y)

/-! ### Right-identity of `myAdd`

`myAdd n 0 = n`. The cyclic proof descends on `n`. At the recursive
`succ n'` case, simp unfolds both `myAddR0` and `myAdd` to reduce the
goal to `Nat.succ (myAdd n' 0) = Nat.succ n'` — which is *not* the IH
`myAdd n' 0 = n'` directly (the IH applies one level down inside the
`Nat.succ`). The `congr 1; exact ih_n` closes it. -/

/-! ### Inline-goal form

The cleanest surface — write the theorem statement directly, like a
normal Lean theorem. No separately-defined `myAddR0_pred : Nat → Prop`
needed. -/

cyclic_thm myAddR0 (n : Nat) : myAdd n 0 = n by_cyclic
  cases n with
    | 0       => done by simp [myAdd]
    | succ n' => back {n := n'} by
        simp [myAdd]
        recurse

/-! ### Verify it's a real theorem -/

example : myAdd 7 0 = 7 := myAddR0 7

example (n : Nat) : myAdd n 0 = n := myAddR0 n

#check @myAddR0       -- ∀ (n : Nat), myAdd n 0 = n

/-! ### Symmetric-style: `myAdd 0 n = n` (this one is trivial — leaf only)

`myAdd 0 n` reduces to `n` by the first defining equation directly.
No induction or back-edge needed. Included to show that the DSL
gracefully handles "all leaves, no recurrence" cases too. -/

cyclic_thm myAddL0 (n : Nat) : myAdd 0 n = n by_cyclic
  cases n with
    | 0       => done by simp [myAdd]
    | succ n' => done by simp [myAdd]

example (n : Nat) : myAdd 0 n = n := myAddL0 n
