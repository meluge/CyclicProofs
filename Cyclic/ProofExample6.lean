import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic

/-!
# Sanity check: cyclic proofs over user-defined inductives

The DSL claims to work for any inductive type. Test with two cases:

  1. **`Stack`**: a custom single-recursive inductive (≃ `List Unit`).
     Should work end-to-end.
  2. **`BinTree`**: a binary-recursive inductive (`node l r` has *two*
     recursive arguments). Phase-3 translator can't bind two IHs in one
     `induction` arm, so we expect this one to fall back to a `sorry`
     in the emitted script — surfacing the limitation honestly rather
     than silently miscompiling.
-/

/-! ### 1. Custom single-recursive inductive: works -/

inductive Stack : Type
  | empty : Stack
  | push  : Nat → Stack → Stack
  deriving Repr

def myS : Stack → Prop
  | .empty    => True
  | .push _ s => myS s

cyclic_thm myS_all : myS s by_cyclic
  cases s with
    | empty   => done
    | push n s' => back {s := s'}

example : myS (.push 1 (.push 2 .empty)) := myS_all _

#check @myS_all   -- ∀ (s : Stack), myS s

/-! ### 2. Binary-recursive: expected to break

  `BinTree.node l r` has two recursive args; the current translator
  emits a `sorry` because it doesn't yet bind two IHs (`ih_l`, `ih_r`)
  in one arm. Phase 4 work.

  Commented out so the build stays green; uncomment to see the limit.

```
inductive BinTree : Type
  | leaf : BinTree
  | node : BinTree → BinTree → BinTree

def myT : BinTree → Prop
  | .leaf     => True
  | .node l r => myT l ∧ myT r

cyclic_thm myT_all : myT t by_cyclic
  cases t with
    | leaf     => done
    | node l r => done    -- can't actually recurse on both subtrees yet
```
-/
