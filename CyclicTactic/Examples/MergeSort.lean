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
2. Prove `length (merge xs ys) = length xs + length ys` as a `cyclic_thm`
   — a lex-only recursion that exercises the WF emission backend.

`mergeSort` itself is defined for context but its `decreasing_by` is left
as `sorry` (the split-shortening lemmas are not the focus here); it is not
referenced by the property we prove. If a step fails, that's data — note
the failure, move on.
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
Lean that splits shorten the list; the split-shortening lemma is left as
`sorry` since `mergeSort` is not exercised by the property below. -/

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

The recursion in `merge` is lex on `(xs.length, ys.length)` — when
`x ≤ y` we descend on `xs`, otherwise on `ys`. Neither argument is
structurally smaller across both cases, so structural induction cannot
witness termination. Written with `cyc_by_cases` (a recorded `by_cases`)
so the back-edges inside the decidable split `x ≤ y` are visible to the
event recorder; the dispatcher then detects no single-variable order,
synthesises the lex measure `(xs.length, ys.length)`, and emits a
kernel-checked `def … termination_by … decreasing_by`. -/

cyclic_thm merge_length (xs : List Nat) (ys : List Nat) :
    (merge xs ys).length = xs.length + ys.length by
  cyclic R
  cyc_cases xs with
  | nil => simp [merge]
  | cons x xs' =>
    cyc_cases ys with
    | nil => simp [merge]
    | cons y ys' =>
      cyc_by_cases hle : x ≤ y with
      | pos =>
        -- x ≤ y: descend on xs
        simp [merge, hle]
        back R {xs := xs', ys := y :: ys'}
      | neg =>
        -- x > y: descend on ys
        simp [merge, hle]
        back R {xs := x :: xs', ys := ys'}

end MergeSort
