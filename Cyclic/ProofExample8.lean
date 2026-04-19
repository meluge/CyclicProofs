import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic

/-!
# Phase 4: genuine cyclic proofs over multi-recursive inductives

`BinTree.node l r` has *two* recursive arguments. A real cyclic proof
of `∀ t, P t` over BinTree must back-edge from the `node l r` arm to
the root *twice* — once for the `l` subtree, once for `r`. SCT then
validates strict descent on each.

This is what the literature calls a "branching" cyclic proof: one
case-split, multiple back-edges per arm.
-/

inductive BinTree : Type
  | leaf : BinTree
  | node : BinTree → BinTree → BinTree
  deriving Repr

/-! ### Predicate that's structurally `True` everywhere

The cyclic-proof content is the descent argument: from `myT (node l r)`,
back-edge into `myT l` AND `myT r`, both of which are strict subterms
of `node l r`. SCT extracts two trace graphs (one per back-edge), each
with a strict self-loop on slot 0; the multi-graph closure passes.
-/

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

#check @myT_all   -- ∀ (t : BinTree), myT t

/-! ### Why `size_pos` doesn't fit the cyclic-branch pattern

A goal like `1 ≤ size t` (not propositionally a conjunction at the
`node` case) doesn't decompose cleanly via `branch`'s `refine ⟨…⟩`.
You'd need to use both subtrees' bounds as *facts* (not subgoals),
which is closer to direct recursion than to a cyclic-proof branch.
Such proofs are still expressible with `back` + a custom close tactic
that calls the recursive function directly, but the cleanest way to
express them is just an ordinary Lean theorem with `induction`. -/
