import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic

/-!
# Ackermann-style cyclic proof (paper Example 4.2)

Grotenhuis & Otten use Ackermann to motivate the importance of *progress
conditions* in cyclic proofs (§4.2). The function

```
ack 0       n         = n + 1
ack (suc m) 0         = ack m 1
ack (suc m) (suc n)   = ack m (ack (suc m) n)
```

terminates by lex `(m, n)` — the inner call `ack (suc m) n` preserves
`m` and decreases `n`; the outer `ack m _` decreases `m`. Both back-
edges in a cyclic proof of any property of `ack` must show strict
descent in *some* slot of every cycle, with the lex measure as witness.

We pick a simple property: `∀ m n, 0 < ack m n`. The cyclic proof has
two back-edges, both targeting the root, both showing strict descent on
slot 0 (the `m` argument). The second one's σ contains a *non-trivial*
RHS — `n := ack (suc m') n'` — exercising the substitution machinery's
ability to handle compound subject terms.

## What's interesting compared to earlier examples

  * **Genuinely classic** — Ackermann is the textbook example for
    multi-arg termination and is explicitly discussed in the paper.
  * **Compound σ values** — the back-edge substitution maps `n` to a
    full ack-application term, not just a variable.
  * **Lex-measure-of-the-function** vs **lex-measure-of-the-proof**
    — the function `ack` itself needs lex `(m, n)` to terminate, but
    the *proof* of `ackPos` only needs lex on `m` alone (since both
    back-edges strictly descend on `m`).
  * **Soundness flows through the WF emission** — Lean's kernel
    rechecks the recursive `def ackPos` against `termination_by m`
    and the recursive call's measure decrease.
-/

def ack : Nat → Nat → Nat
  | 0,        n         => n + 1
  | .succ m,  0         => ack m 1
  | .succ m,  .succ n   => ack m (ack (.succ m) n)
termination_by m n => (m, n)

/-- The property we cyclically prove: `ack m n` is always positive. -/
def ackPos (m n : Nat) : Prop := 0 < ack m n

/-! ### Cyclic proof of `∀ m n, ackPos m n`

```
[R]  ackPos(m, n)                            (case-split on m)
 ├── 0       => leaf  (0 < n + 1, by simp)
 └── suc m'  => ackPos(suc m', n)             (case-split on n)
      ├── 0       => unfold ⇒ ackPos(m', 1)
      │              └── back to R via σ = {m ↦ m', n ↦ 1}
      └── suc n'  => unfold ⇒ ackPos(m', ack (suc m') n')
                     └── back to R via σ = {m ↦ m', n ↦ ack (suc m') n'}
```

Trace for both back-edges: `m'` is a strict subterm of `suc m'` →
edge `0 ->→ 0` on slot 0. SCT passes via lex `[0]` (just `m`). The
emitted `def ackPos` will have `termination_by m n => m`. -/

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

/-! ### Verify it's a real theorem -/

example : 0 < ack 2 3       := ackPos_all 2 3
example (m n : Nat) : 0 < ack m n := ackPos_all m n

#check @ackPos_all   -- ∀ (m n : Nat), ackPos m n
#eval ack 3 3        -- 61 (computes quickly for small inputs)
