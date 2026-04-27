import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Annotation
import Cyclic.Reorganize
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic

/-!
# Tree-reorganisation test (Grotenhuis-Otten Prop 5.8 / Wehr Ch. 7)

A cyclic proof written with case-splits in the *wrong* order — `cases y`
outer, `cases x` inner — even though the trace SCGs require lex `(x, y)`
(so `x` must be outer for structural emission to discharge each
back-edge with the right IH).

The dispatcher pipeline:
  1. `canStructural` runs `treeMatchesOrder [x, y]` on the user's tree.
     The top is `cases y`, expected `x`. Returns *false*.
  2. `Cyclic.Reorganize.reorder ["x", "y"]` swaps the two case-split
     levels via `swapAdjacent`. Bodies are moved to their new positions
     by transposition; back-edge `anc` labels are *not* touched here.
  3. `Cyclic.Reorganize.retargetBacks` walks the reorganised tree and,
     for each back-edge, looks up its descending variable (from the
     annotation's per-back-edge `progPos`) and rewires `anc` to the
     case-split on that variable in the current scope. So the back-edge
     descending on `x` (originally targeting outer `cases y`) now
     targets the new outer `cases x`; the back-edge descending on `y`
     targets the new inner `cases y`.
  4. SCGs are re-extracted and `canStructural` is rechecked. The
     reorganised tree passes both checks, so structural emission
     proceeds on it. The diagnostic notes "structural (nested
     `induction`, after reorganisation)".
-/

def reorderP : Nat → Nat → Prop := fun _ _ => True

cyclic_thm reorderP_all (x : Nat) (y : Nat) : reorderP x y by_cyclic
  -- Wrong order: y outer, x inner. SCT requires lex (x, y).
  R: cases y with
    | 0 =>
      cases x with
        | 0       => done by trivial
        | succ x' => back R {x := x', y := 1} by recurse
    | succ y' =>
      cases x with
        | 0       => done by trivial
        | succ x' => back R {x := succ x', y := y'} by recurse

example (a b : Nat) : reorderP a b := reorderP_all a b

/-! ## Multi-recursive reorganisation

A cyclic proof over `BTr × Nat` written with `cases n` outer (the wrong
order — SCT requires `t` outer because each back-edge descends on `t`,
the BinTree variable, and `n` doesn't descend at all).

The `cases t` inside each n-arm uses the multi-recursive `node l r`
constructor, dispatched by `branch · back {t := l} · back {t := r}`.
This is the multi-rec extension to reorganisation: `extractInnerStructure`
classifies each outer arm's body as `.single` (direct caseSplit) or
`.branch` (multi-rec). After the swap, the new inner case-split's
body at the `node l r` cell rebuilds the branch with each child
extracted from the corresponding original branch slot.
-/

inductive BTr : Type where
  | leaf : BTr
  | node : BTr → BTr → BTr

def btPred : BTr → Nat → Prop
  | .leaf,     _ => True
  | .node l r, n => btPred l n ∧ btPred r n

-- Predicate form (`cyclic_thm name : pred args …`) — the default-simp
-- hint uses `pred`, so the branch's auto-`simp` prelude unfolds `btPred`
-- into its conjunctive form and `refine ⟨?_, ?_⟩` succeeds.
cyclic_thm btPred_wrong : btPred t n by_cyclic
  cases n with
    | 0 =>
      cases t with
        | leaf => done
        | node l r =>
          branch
            · back {t := l, n := 0}
            · back {t := r, n := 0}
    | succ n' =>
      cases t with
        | leaf => done
        | node l r =>
          branch
            · back {t := l, n := succ n'}
            · back {t := r, n := succ n'}

example (t : BTr) (n : Nat) : btPred t n := btPred_wrong t n
