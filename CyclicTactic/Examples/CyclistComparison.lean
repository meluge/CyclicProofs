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


/-! ## Predicate-form ADD (for tests 06, 08)

Cyclist's `ADD` predicate (recursing on the first arg) ported as a
Lean inductive Prop. -/

inductive ADDp : Nat → Nat → Nat → Prop where
  | base (y : Nat) : Nlike y → ADDp 0 y y
  | step (x y z : Nat) : ADDp x y z → ADDp (Nat.succ x) y (Nat.succ z)


/-! ## Test 06 — `true ⊢ ADD(0, 0, 0)` (cyclist FAILS, we win trivially)

Cyclist's `06-zero-plus-zero.tst.no`: cyclist's first-order proof
search can't synthesise the `Nlike 0` premise that `ADDp.base`
demands. In Lean it's a one-liner. -/

example : ADDp 0 0 0 := ADDp.base 0 Nlike.zero


/-! ## Test 08 — `N(x) ∧ N(y) ∧ ADD(x,y,z) ⊢ N(z)` (cyclist passes)

"ADD's third argument is a nat." Induction on the ADD derivation.
The `cyc_cases` on `h : ADDp x y z` peels constructors with their
explicit args; we follow with the back-edge on the recursive
witness.

Note the σ uses the constructor's freshly-introduced names: `cases`
substitutes the outer `x, y, z` to the constructor's RHS, so the
back-edge supplies the *new* (smaller) `x, y, z` corresponding to
the recursive premise. -/

cyclic_thm sum_is_nlike_cyc
    (x y z : Nat) (h : ADDp x y z) (hy : Nlike y) : Nlike z by
  cyclic R
  cyc_cases h with
  | base y' hy' => exact hy'
  | step x' y' z' h' =>
    apply Nlike.succ
    back R {x := x', y := y', z := z', h := h', hy := hy}


/-! ## Test 14 — `N(x) ∧ N(y) ⊢ N2(x, y)` (probe the WF-emission gap)

```
N2 { N(y) ⇒ N2(0, y) | N2(y, x) ⇒ N2(s x, y) }
```

The recursive call **swaps** the args: `N2 (s x) y` from `N2 y x`.
Lex lookup descends only on the first arg under the *swap*, which
isn't structural in either single arg. Lean's structural-recursion
check rejects it; a sum measure (`a0 + a1`) would discharge it via
`termination_by`, but `cyclic_thm` in `CyclicTactic` doesn't yet
emit `termination_by` (the older `Cyclic/` library does).

Expected outcome: this proof is rejected for termination reasons,
documenting the WF-emission gap. Disabled below to keep the file
buildable; uncomment to reproduce the failure.

```
inductive N2p : Nat → Nat → Prop where
  | base (y : Nat) : Nlike y → N2p 0 y
  | step (x y : Nat) : N2p y x → N2p (Nat.succ x) y

theorem nat_is_nlike : ∀ n, Nlike n
  | 0     => .zero
  | n + 1 => .succ n (nat_is_nlike n)

cyclic_thm n2_holds (x y : Nat) : N2p x y by
  cyclic R
  cyc_cases x with
  | zero    => exact N2p.base y (nat_is_nlike y)
  | succ x' =>
    apply N2p.step x' y
    back R {x := y, y := x'}     -- swap; structural recursion rejects
```
-/


/-! ## Test 05 — `N(x) ∧ N(y) ⊢ Q(x, y)` (cyclist passes; mutual P/Q)

```
P { true ⇒ P(0) | P(x) ∧ Q(x, s x) ⇒ P(s x) }
Q { true ⇒ Q(x, 0) | Q(x, y) ∧ P(x) ⇒ Q(x, s y) }
```

Mutually-defined predicates with cross-references in their rules.
The cyclic proof needs a coupled system on `prove_p` and `prove_q`,
each with two recursive calls per `succ` arm — one to itself, one
to the partner. Tests `cyclic_mutual` on a fresh example. -/

mutual
  inductive P : Nat → Prop where
    | zero : P 0
    | succ (x : Nat) : P x → Q x (Nat.succ x) → P (Nat.succ x)
  inductive Q : Nat → Nat → Prop where
    | zero (x : Nat) : Q x 0
    | succ (x y : Nat) : Q x y → P x → Q x (Nat.succ y)
end

cyclic_mutual
  thm prove_p (x : Nat) : P x by
    cyclic R_P
    cyc_cases x with
    | zero    => exact P.zero
    | succ k  =>
      refine P.succ k ?_ ?_
      · back R_P {x := k}
      · back R_Q {x := k, y := Nat.succ k}
  thm prove_q (x y : Nat) : Q x y by
    cyclic R_Q
    cyc_cases y with
    | zero    => exact Q.zero x
    | succ k  =>
      refine Q.succ x k ?_ ?_
      · back R_Q {x := x, y := k}
      · back R_P {x := x}
end_mutual

example (x y : Nat) : Q x y := prove_q x y
example (x : Nat)   : P x   := prove_p x


/-! ## Notes on the remaining cyclist FO tests

* **Tests 02 / 04** — `E(x) ∨ O(x) ⊢ N(x)` and `N(x) ⊢ O(x) ∨ E(x)`.
  Test 02 reduces via `Or.elim` to the existing 01 proof (no new
  cyclic structure). Test 04 needs a back-edge whose result is then
  case-split on (i.e. introduce an IH as a hypothesis, then `cases`
  it) — our `back` primitive consumes the goal directly via
  `exact`, so this pattern isn't expressible cyclically. The
  theorem proves fine via standard Lean `induction`, but that's not
  a cyclic proof.

* **Tests 12 / 13 / 15** — Sprenger-Dam two-step descent (R / R2)
  and the 2-Hydra. All require WF emission with a specific
  measure (lex / sum) because no single argument structurally
  decreases on every recursive call. The older `Cyclic/` library
  has WF emission via `Cyclic.Unravel.translateWF`; porting it to
  `CyclicTactic` is the same scope-of-work as adding mutual SCT
  (per-entry tree → measure synthesis → `def + termination_by`
  emission instead of plain `def`).

* **Test 03** — `E^1(x) ∨ O^1(x) ⊢ N(x)` with cyclist's exotic
  predicate-unfolding superscript. Cyclist marks failing; not
  ported.
-/
