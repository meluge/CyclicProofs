import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd

/-!
# Beyond Nat: a cyclic-proof example over `List Nat`

Goal: `∀ xs : List Nat, L(xs)` where `L` is the trivial predicate
defined by

  L([])      ⇔ ⊤
  L(x :: xs) ⇔ L(xs)

Same shape as the single-variable Nat example (`myP_all`), but the
inducted variable is `List Nat` rather than `Nat`. This exercises the
Phase-3 sort introspection: `cyclic_thm` walks the predicate's signature
to discover the constructor names (`List.nil`, `List.cons`) and
recursive-arg positions (cons's tail), and the translator emits

```
induction xs with
| nil => …
| cons x xs' ih_xs => …
```

without any user-side type annotations beyond the predicate itself.

## Cyclic derivation

```
[R]   L(xs)                          (case-split on xs)
 ├── [C0]  L([])                      leaf (unfold ⇒ ⊤)
 └── [C1]  L(x :: xs')                unfold ⇒ L(xs')
      └── [U]  L(xs')                  back-edge to R via σ = {xs ↦ xs'}
```

Trace: position 0 strictly descends (xs' is a proper subterm of x::xs').
SCT: a single graph with `[0 -→ 0]`, idempotent, strict self-loop ✓.
-/

open Cyclic.Proof

/-! ### Formulas -/

def lAtXs    : Formula := { pred := "L", args := [.var "xs"] }
def lAtNil   : Formula := { pred := "L", args := [.ctor "nil" []] }
def lAtCons  : Formula :=
  { pred := "L", args := [.ctor "cons" [.var "x", .var "xs'"]] }
def lAtTail  : Formula := { pred := "L", args := [.var "xs'"] }

def sLAtXs   : Sequent := .succ1 lAtXs
def sLAtNil  : Sequent := .succ1 lAtNil
def sLAtCons : Sequent := .succ1 lAtCons
def sLAtTail : Sequent := .succ1 lAtTail

/-! ### Proof tree -/

def lProof : ProofTree :=
  .caseSplit "R" sLAtXs "xs" [
    (.ctor "nil" [],
      .leaf "C0" sLAtNil "unfold ⇒ ⊤"),
    (.ctor "cons" [.var "x", .var "xs'"],
      .node "C1" sLAtCons "unfold" [
        .back "U" sLAtTail "R" [("xs", .var "xs'")]
      ])
  ]

#eval toString lProof.sequent             -- "⊢ L(xs)"
#eval lProof.backEdges                     -- [("U", "R")]

#eval (extractTraceSCGs lProof).map toString
-- Expected: ["SCGraph(1 → 1): [0 ->→ 0]"]

#eval SCGraph.checkMultiSCT (extractTraceSCGs lProof)   -- true

/-! ### Stage 3: the real theorem -/

def myL : List Nat → Prop
  | []       => True
  | _ :: xs  => myL xs

cyclic_thm myL_all : myL := lProof

/-! ### Using it downstream -/

example : myL [1, 2, 3, 4, 5] := myL_all [1, 2, 3, 4, 5]

example (xs ys : List Nat) : myL xs ∧ myL ys :=
  ⟨myL_all xs, myL_all ys⟩

#check @myL_all                          -- ∀ (xs : List Nat), myL xs
