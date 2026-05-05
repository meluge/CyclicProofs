import CyclicTactic.Tactic
import CyclicTactic.Examples.drp

set_option warningAsError false

/-!
# Comparison with Cyclist (Brotherston-Gorogiannis-Petersen 2012)

Ports cyclist's first-order benchmark `benchmarks/fo/` to
`CyclicTactic`. Each cyclist `.tst` (or `.tst-no` / `.tst.no`) maps
to a comparable Lean theorem.

Naming convention in the cyclist suite:
* plain `.tst`               — cyclist proves it
* `.tst-no` / `.tst.no`      — cyclist gives up

Headline results from this file:

| # | Cyclist sequent                                    | Cyclist | CyclicTactic |
|---|----------------------------------------------------|---------|--------------|
| 07 | `N(x) ⊢ ADD(x,0,x)`                               | ✓       | ✓ (`zeroAdd_cyc`) |
| 09 | `ADD(x,y,z) ⊢ ADD(x,s y,s z)`                     | ✓       | ✓ (`succAdd_cyc`) |
| 10 | `… ⊢ associativity of ADD`                         | ✗       | **✓** (`addAssoc_cyc`) |
| 11 | `… ⊢ commutativity of ADD`                         | ✗       | **✓** (`addComm_cyc`, drp.lean) |
| 01 | `O(x) ⊢ N(x)` (mutual)                             | ✓       | **✗** (no mutual surface) |

Tests 10 and 11 are the headline wins: cyclist's first-order prover
fails because its proof search applies sequent rules without
equational reasoning, while ours plugs into Lean's tactic repertoire
(`congrArg`, `rw`) for the per-arm algebra. The cyclic structure
contributed by `cyclic_thm` is identical to what cyclist would emit;
the difference is in the per-arm reasoning surface.

Test 01 is the headline gap, exercising the mutual / cross-predicate
cycle support that cyclist has and we don't.
-/


/-! ## Test 07 — `N(x) ⊢ ADD(x, 0, x)`

`Nat.add` in Lean recurses on its *second* argument, so cyclist's
`ADD(x,0,x)` (recursion on the first arg) becomes `0 + n = n`
under the convention swap. Single induction on `n`. Already proved
in `drp.lean :: zeroAdd_cyc`. -/

example (n : Nat) : 0 + n = n := zeroAdd_cyc n


/-! ## Test 09 — `ADD(x,y,z) ⊢ ADD(x, s y, s z)`

Predicate-form: `n + m = z → n + (m+1) = z + 1`. With Lean's `+`
recursing on the RHS, this is `Nat.add_succ` definitionally. The
non-trivial mirror is `Nat.succ n + m = Nat.succ (n + m)`, induction
on `m`. -/

cyclic_thm succAdd_cyc (n m : Nat) : Nat.succ n + m = Nat.succ (n + m) by
  cyclic R
  cyc_cases m with
  | zero => rfl
  | succ m' =>
    rw [Nat.add_succ, Nat.add_succ]
    apply congrArg Nat.succ
    back R {n := n, m := m'}


/-! ## Test 10 — associativity of ADD (cyclist FAILS)

Cyclist's `10-add-associative.tst-no`:
```
N(x) & N(y) & N(z) & ADD(x,y,w) & ADD(y,z,a) & ADD(w,z,b) ⊢ ADD(x,a,b)
```
i.e. `(x + y) + z = x + (y + z)` in predicate form with the
intermediate sums named.

Cyclist's first-order prover gives up: its proof search applies
sequent rules with no equational simplification, so it cannot
manipulate the predicate hypotheses. Ours succeeds because
the cyclic structure (cases-on-c + back-edge) is decoupled from
the per-arm algebra (`congrArg Nat.succ` + `rw`), which Lean
discharges. -/

cyclic_thm addAssoc_cyc (a b c : Nat) : (a + b) + c = a + (b + c) by
  cyclic R
  cyc_cases c with
  | zero => rfl
  | succ c' =>
    rw [Nat.add_succ, Nat.add_succ, Nat.add_succ]
    apply congrArg Nat.succ
    back R {a := a, b := b, c := c'}


/-! ## Test 11 — commutativity of ADD (cyclist FAILS)

Cyclist's `11-add-commutative.tst-no`. We already prove this in
`drp.lean :: addComm_cyc`. Listed here for table completeness. -/

example (n m : Nat) : n + m = m + n := addComm_cyc n m


/-! ## Test 01 — `O(x) ⊢ N(x)` (cyclist SUCCEEDS, we **cannot express**)

Cyclist's first-order benchmark uses N, E, O as *separate*
inductive predicates with rules:
```
N { true ⇒ N(0) | N(x) ⇒ N(s x) }
E { true ⇒ E(0) | O(x) ⇒ E(s x) }
O { E(x) ⇒ O(s x) }
```
The cyclic proof of `O(x) ⊢ N(x)` is a *coupled* system with two
companions, one per RHS predicate, and back-edges that *cross*
predicate boundaries (the proof of `O ⊢ N` recurses into the proof
of `E ⊢ N` and vice versa).

To make the test non-trivial in Lean (where Nat is a host type), we
mirror cyclist's setup faithfully: define `Nlike` as an independent
inductive predicate, then ask whether `Od n → Nlike n`. -/

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

/-! ### Standard Lean — works fine via mutual structural induction -/

mutual
  theorem od_is_nlike_std : ∀ n, Od n → Nlike n
    | _, .succ k h => .succ _ (ev_is_nlike_std k h)
  theorem ev_is_nlike_std : ∀ n, Ev n → Nlike n
    | _, .zero      => .zero
    | _, .succ k h  => .succ _ (od_is_nlike_std k h)
end

/-! ### Cyclic — using the new `cyclic_mutual ... end_mutual` block

The MVP mutual frontend. Each `thm` entry registers its own
companion (`R_O` for `od_is_nlike`, `R_E` for `ev_is_nlike`); a
back-edge to a *different* companion (`back R_E {…}` from inside
the Od-side proof) is resolved against the global companion table
to find the target theorem's name + binders, then issued as
`exact ev_is_nlike_cyc <args>`.

Lean's mutual-recursion termination check provides soundness;
SCT validation across mutual blocks is not yet wired up (future
work — would extend `extractTraceSCGsLabeled` to cross-companion
trace closure). -/

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

/-! ### Status of remaining gaps relative to cyclist's mutual support

The MVP `cyclic_mutual` block above closes the *expressibility* gap:
back-edges that cross companion boundaries (`back R_E` from inside
`od_is_nlike_cyc`, `back R_O` from inside `ev_is_nlike_cyc`) resolve
to the right theorem and the proof type-checks.

What's still future work:

* **SCT validation across the mutual block.** Each entry's events
  are recorded into a shared log but trees aren't built per-entry
  yet, so cross-companion size-change graphs aren't extracted. For
  the MVP, soundness comes from Lean's mutual-recursion termination
  check (which is what accepts the synthesised `mutual def … end`).
  Adding mutual SCT is a localised follow-up: per-entry tree
  construction → vertices labelled with `(entry-id, position)` →
  one multi-graph `checkMultiSCT` call.

* **Unravel emission for mutual.** The single-`cyclic_thm` Unravel
  pass replaces the recursive form with a structural-induction
  theorem. Mutual emission would target a `mutual theorem …
  | _, .succ k h => … end` style block, deriving the case-split
  pattern from each entry's `cyc_cases`. Useful but not blocking.
-/

#check @od_is_nlike_std
#check @ev_is_nlike_std
#check @od_is_nlike_cyc
#check @ev_is_nlike_cyc
