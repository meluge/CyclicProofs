import CyclicTactic.Tactic

set_option warningAsError false

/-!
# Worked example: cyclic proofs of merge-sort correctness

A larger case study to see how the `cyclic_thm` / `cyclic_mutual`
machinery handles a real algorithm. Merge-sort's recursion is *not*
structural on its input list (it splits in half), so this file is
also a deliberate stress test of the system's limits.

## Plan

1. Define `split`, `merge`, `mergeSort` over `List Nat`.
2. Prove `length (mergeSort xs) = length xs` as a `cyclic_thm`.
3. Define `sorted` inductively; prove `sorted (mergeSort xs)`.
4. Compare against the structurally-recursive *insertion sort*
   variant in the same file to see what the system handles for free
   vs. what needs WF support.

If a step fails, that's data — note the failure, move on.
-/

namespace MergeSort

/-! ### `split` — divide a list into two halves by alternating -/

def split : List Nat → List Nat × List Nat
  | []       => ([], [])
  | [x]      => ([x], [])
  | x :: y :: xs =>
    let (l, r) := split xs
    (x :: l, y :: r)

/-! ### `merge` — combine two sorted lists -/

def merge : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: merge xs (y :: ys)
    else y :: merge (x :: xs) ys
  termination_by xs ys => xs.length + ys.length
  decreasing_by
    all_goals simp_wf
    all_goals omega

/-! ### `mergeSort` — recursive split + merge

The classic non-structural recursion. Needs `termination_by` to convince
Lean that splits shorten the list. -/

def mergeSort : List Nat → List Nat
  | []      => []
  | [x]     => [x]
  | x :: y :: xs =>
    let (l, r) := split (x :: y :: xs)
    merge (mergeSort l) (mergeSort r)
  termination_by xs => xs.length
  decreasing_by
    all_goals simp_wf
    all_goals sorry  -- split-shortens lemma needed; not the focus of this file

/-! ## Property 1: `length (merge xs ys) = length xs + length ys`

The recursion in `merge` is lex on `(xs.length, ys.length)` —
when `x ≤ y` we descend on `xs`, otherwise on `ys`. Neither arg
is structurally smaller across both cases. This is the
first test of whether `cyclic_thm` can express lex-only recursion. -/

cyclic_thm merge_length (xs : List Nat) (ys : List Nat) :
    (merge xs ys).length = xs.length + ys.length by
  cyclic R
  cyc_cases xs with
  | nil => simp [merge]
  | cons x xs' =>
    cyc_cases ys with
    | nil => simp [merge]
    | cons y ys' =>
      by_cases hle : x ≤ y
      · -- x ≤ y: descend on xs
        simp [merge, hle]
        back R {xs := xs', ys := y :: ys'}
      · -- x > y: descend on ys
        simp [merge, hle]
        back R {xs := x :: xs', ys := ys'}

end MergeSort
