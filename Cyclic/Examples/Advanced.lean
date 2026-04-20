import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic

/-!
# Cyclic Proofs: Advanced (paper-faithful cases)

The cases that demonstrate why paper-faithful WF-recursion emission is
*more powerful* than just nested-induction with cyclic-flavoured
syntax. Each example below exercises something the simpler examples in
`DSL.lean` don't.
-/

/-! ### 1. Sum measure: swap-style recursion

Neither `x` nor `y` strictly decreases on its own — the back-edge
swaps both arguments. SCT passes via the *closure*: composing the swap
graph with itself yields strict diagonals on both positions.

The measure synthesiser tries lex first (fails — the strict edge goes
off-diagonal `0 → 1`, not `0 → 0`), then sum, which works because the
swap admits a bijection callee↔caller with at least one strict edge.

The emitted `termination_by x y => x + y` is what makes Lean accept
the recursive call `swapP_all y x'` (`y + x' < (suc x') + y`). Nested
`induction` could not handle this — the IH at `induction x` doesn't
allow re-binding `x` to anything other than its predecessor.

This example is the cleanest demonstration that WF emission with the
synthesised measure carries the cyclic proof's soundness witness into
the kernel-checked output. -/

def swapP : Nat → Nat → Prop
  | 0,        _ => True
  | .succ x', y => swapP y x'
termination_by x y => x + y

cyclic_thm swapP_all (x : Nat) (y : Nat) : swapP x y by_cyclic
  cases x with
    | 0       => done by simp [swapP]
    | succ x' => back {x := y, y := x'} by
        simp [swapP]
        recurse

example (a b : Nat) : swapP a b := swapP_all a b

/-! ### 2. Multi-recursive constructor: branching back-edges (BinTree)

`BinTree.node l r` has two recursive arguments. A genuine cyclic proof
of a property over `BinTree` must back-edge twice from the `node`
case — once for each subtree. The DSL's `branch · <step> · <step>`
constructs an n-ary subgoal split (auto-emits `refine ⟨?_, ?_⟩`); each
branch can independently emit a back-edge.

SCT extracts two trace graphs (one per back-edge), each with strict
descent on slot 0. The closure idempotents have strict self-loops on
slot 0; greedy rank construction finds the lex measure. -/

inductive BinTree : Type
  | leaf : BinTree
  | node : BinTree → BinTree → BinTree

def myT : BinTree → Prop
  | .leaf     => True
  | .node l r => myT l ∧ myT r

cyclic_thm myT_all : myT t by_cyclic
  cases t with
    | leaf      => done
    | node l r  =>
        branch
          · back {t := l}
          · back {t := r}

example : myT (.node .leaf (.node .leaf .leaf)) := myT_all _

/-! ### 3. Ackermann (Grotenhuis-Otten Example 4.2)

The paper uses Ackermann to motivate the importance of progress
conditions in cyclic proofs (§4.2). The function uses lex `(m, n)` for
its own termination; the cyclic proof of `0 < ack m n` has two
back-edges in the `succ m'` arm — both strictly descending on `m`.

The second back-edge has a *compound* substitution
(`n := ack (suc m') n'`) — the σ-image is itself an ack-application,
testing the trace machinery's ability to handle non-trivial subject-
term values in σ. Both back-edges contribute trace graphs with strict
descent on slot 0, so lex `(m, n)` is the synthesised measure.

This is the canonical "real cyclic proof" from the paper, end-to-end
in our framework. -/

def ack : Nat → Nat → Nat
  | 0,         n        => n + 1
  | .succ m,   0        => ack m 1
  | .succ m,   .succ n  => ack m (ack (.succ m) n)
termination_by m n => (m, n)

def ackPos (m n : Nat) : Prop := 0 < ack m n

cyclic_thm ackPos_all (m : Nat) (n : Nat) : ackPos m n by_cyclic
  R: cases m with
    | 0       => done by simp [ackPos, ack]
    | succ m' =>
      cases n with
        | 0       => back R {m := m', n := 1} by
            simp [ackPos, ack]
            recurse
        | succ n' => back R {m := m', n := ack (succ m') n'} by
            simp [ackPos, ack]
            recurse

example (m n : Nat) : 0 < ack m n := ackPos_all m n
#eval ack 3 3   -- 61

/-! ### 4. Three-position lex with distinct progressing names

A pedagogical example designed to exercise the paper-style reset
annotation (`Cyclic.Annotation`): three back-edges, each descending on
a *different* argument position. The greedy synthesis from closure
witnesses produces induction order `a₀ ≻ a₁ ≻ a₂`; per back-edge,
`prog` is attributed to the slot that strictly descends in *its* cycle.

This is what the diagnostic surfaces (with auto-generated back-edge
labels):

```text
induction order: a0 ≻ a1 ≻ a2
back-edges:
  _B?: prog = a0; …  (back to outermost R, descends on x)
  _B?: prog = a1; …  (back to middle S, descends on y)
  _B?: prog = a2; …  (back to nearest inner, descends on z)
```

Each recursive call in the emitted def carries a matching
`-- back-edge … prog = aN` comment, making the SCT cycle's descent
witness inspectable both in the diagnostic *and* in the kernel-checked
output. The predicate itself is trivial — what's exercised here is the
annotation's per-back-edge attribution, not the proof content. -/

def threeR : Nat → Nat → Nat → Prop := fun _ _ _ => True

-- The predicate is constant `True`, so `simp [threeR]` closes any goal —
-- but then the recursive `exact` would have no goal. Each back uses bare
-- `recurse`, which the translator expands to `exact threeR_all <args>`;
-- Lean accepts it because both `threeR <call args>` and the narrowed
-- goal `threeR <local args>` reduce to `True`. The leaf uses `trivial`.
cyclic_thm threeR_all : threeR x y z by_cyclic
  R: cases x with
    | 0       => done by trivial
    | succ x' =>
      S: cases y with
        | 0       => back R {x := x'} by recurse
        | succ y' =>
          cases z with
            | 0       => back S {y := y'} by recurse
            | succ z' => back {z := z'} by recurse

example (a b c : Nat) : threeR a b c := threeR_all a b c
