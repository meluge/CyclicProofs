import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd

/-!
# Two-variable cyclic-proof example

Goal: `∀ x y : Nat, Q(x, y)` where `Q` is defined by
  Q(0, y)      ⇔ ⊤
  Q(suc x, y)  ⇔ Q(x, suc y)

The recursive unfolding descends on `x` while *growing* `y`. This
exercises features the single-variable toy doesn't:

  * a multi-arg predicate;
  * a back-edge substitution that re-binds a non-induction variable
    (`y ↦ suc y`), forcing the unravelling translator to emit
    `induction x generalizing y` and apply `ih` at `Nat.succ y`.

## Cyclic derivation

```
[R]   Q(x, y)                (root; case-split on x)
 ├── [C0]  Q(0, y)            leaf (unfold ⇒ ⊤)
 └── [C1]  Q(suc x', y)       unfold ⇒ Q(x', suc y)
      └── [U]  Q(x', suc y)   back-edge to R with σ = {x ↦ x', y ↦ suc y}
```

Trace for U → R: ancestor's args are [x, y]; under path σ = {x ↦ suc x'}
they become [suc x', y]. Back-edge args are [x', suc y]. Arg-slot 0
strictly descends (x' < suc x'); slot 1 doesn't descend, so no edge
from/to slot 1. The SCGraph `[0 -→ 0]` is already idempotent and has
a strict self-loop — SCT passes.
-/

open Cyclic.Proof

/-! ### Formulas and sequents -/

def qAtXY    : Formula :=
  { pred := "Q", args := [.var "x", .var "y"] }
def qAt0Y    : Formula :=
  { pred := "Q", args := [.ctor "zero" [], .var "y"] }
def qAtSucXY : Formula :=
  { pred := "Q", args := [.ctor "succ" [.var "x'"], .var "y"] }
def qAtXpSy  : Formula :=
  { pred := "Q", args := [.var "x'", .ctor "succ" [.var "y"]] }

def sQAtXY    : Sequent := .succ1 qAtXY
def sQAt0Y    : Sequent := .succ1 qAt0Y
def sQAtSucXY : Sequent := .succ1 qAtSucXY
def sQAtXpSy  : Sequent := .succ1 qAtXpSy

/-! ### The proof tree -/

def qProof : ProofTree :=
  .caseSplit "R" sQAtXY "x" [
    (.ctor "zero" [],          .leaf "C0" sQAt0Y "unfold ⇒ ⊤"),
    (.ctor "succ" [.var "x'"], .node "C1" sQAtSucXY "unfold" [
       .back "U" sQAtXpSy "R"
         [("x", .var "x'"), ("y", .ctor "succ" [.var "y"])]
    ])
  ]

#eval toString qProof.sequent              -- "⊢ Q(x, y)"
#eval qProof.backEdges                     -- [("U", "R")]

/-! ### Trace extraction + SCT check -/

#eval (extractTraceSCGs qProof).map toString
-- ["SCGraph(2 → 2): [0 ->→ 0]"]

#eval SCGraph.checkMultiSCT (extractTraceSCGs qProof)   -- true

/-! ### Stage 3: unravelling to a real Lean theorem -/

def myQ : Nat → Nat → Prop
  | 0,        _ => True
  | .succ x,  y => myQ x (.succ y)

cyclic_thm myQ_all : myQ := qProof

/-! ### Using the generated theorem like any other Lean theorem -/

example : myQ 3 5 := myQ_all 3 5

example (a b : Nat) : myQ a b ∧ myQ b a :=
  ⟨myQ_all a b, myQ_all b a⟩

#check @myQ_all        -- myQ_all : ∀ (x y : Nat), myQ x y
