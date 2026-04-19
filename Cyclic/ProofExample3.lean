import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd

/-!
# Lex-descent cyclic-proof example

Goal: `∀ x y : Nat, B(x, y)` where `B` is defined by

  B(0,          y)         ⇔ ⊤
  B(suc x,      0)         ⇔ B(x, 1)
  B(suc x,      suc y)     ⇔ B(suc x, y)

This exercises **lexicographic** descent. Neither `x` alone nor `y`
alone strictly decreases on every back-edge: the succ/0 clause drops
`x` but *increases* `y` (to 1), while the succ/succ clause preserves `x`
and drops `y`. Only the lex pair (`x`, `y`) descends on both.

## Cyclic derivation

```
[R]   B(x, y)                       (case-split on x)
 ├── [C0]  B(0, y)                   leaf (unfold ⇒ ⊤)
 └── [C1]  B(suc x', y)               (case-split on y)
      ├── [C10] B(suc x', 0)          unfold ⇒ B(x', 1)
      │    └── [U1] B(x', 1)          back to R via σ = {x ↦ x', y ↦ 1}
      └── [C11] B(suc x', suc y')     unfold ⇒ B(suc x', y')
           └── [U2] B(suc x', y')     back to R1 via σ = {x' ↦ x', y ↦ y'}
```

Trace graphs:

  * `U1 → R`: arg-slot 0 strictly descends (x' < suc x'); slot 1 doesn't
    relate (1 is not a subterm of y). `SCGraph(2→2): [0 -→ 0]`.
  * `U2 → R1`: arg-slot 0 preserves (suc x' = suc x'); slot 1 strictly
    descends (y' < suc y'). `SCGraph(2→2): [0 -≥→ 0, 1 -→ 1]`.

Multi-SCT closure:

  * U1∘U1: `[0 -→ 0]` — idempotent, has strict self-loop. ✓
  * U2∘U2: composing `[0 ≥ 0, 1 > 1]` with itself gives `[0 ≥ 0, 1 > 1]`
    (≥∘≥=≥, >∘>=>) — idempotent, has strict self-loop on slot 1. ✓
  * U1∘U2 and U2∘U1: both have strict on slot 0. Idempotents among the
    composites all carry at least one strict self-loop.

So SCT passes, and the measure-synthesiser finds lex (a0, a1) — exactly
the lex pair the proof relies on.
-/

open Cyclic.Proof

/-! ### Formulas -/

def bAtXY      : Formula := { pred := "B", args := [.var "x", .var "y"] }
def bAt0Y      : Formula := { pred := "B", args := [.ctor "zero" [], .var "y"] }
def bAtSxY     : Formula :=
  { pred := "B", args := [.ctor "succ" [.var "x'"], .var "y"] }
def bAtSx0     : Formula :=
  { pred := "B", args := [.ctor "succ" [.var "x'"], .ctor "zero" []] }
def bAtSxSy    : Formula :=
  { pred := "B", args := [.ctor "succ" [.var "x'"], .ctor "succ" [.var "y'"]] }
def bAtXpOne   : Formula :=
  { pred := "B", args := [.var "x'", .ctor "succ" [.ctor "zero" []]] }
def bAtSxYp    : Formula :=
  { pred := "B", args := [.ctor "succ" [.var "x'"], .var "y'"] }

def sBAtXY     : Sequent := .succ1 bAtXY
def sBAt0Y     : Sequent := .succ1 bAt0Y
def sBAtSxY    : Sequent := .succ1 bAtSxY
def sBAtSx0    : Sequent := .succ1 bAtSx0
def sBAtSxSy   : Sequent := .succ1 bAtSxSy
def sBAtXpOne  : Sequent := .succ1 bAtXpOne
def sBAtSxYp   : Sequent := .succ1 bAtSxYp

/-! ### Proof tree -/

def bProof : ProofTree :=
  .caseSplit "R" sBAtXY "x" [
    (.ctor "zero" [],          .leaf "C0" sBAt0Y "unfold ⇒ ⊤"),
    (.ctor "succ" [.var "x'"],
      .caseSplit "R1" sBAtSxY "y" [
        (.ctor "zero" [],
          .node "C10" sBAtSx0 "unfold" [
            .back "U1" sBAtXpOne "R"
              [("x", .var "x'"),
               ("y", .ctor "succ" [.ctor "zero" []])]
          ]),
        (.ctor "succ" [.var "y'"],
          .node "C11" sBAtSxSy "unfold" [
            .back "U2" sBAtSxYp "R1"
              [("x'", .var "x'"), ("y", .var "y'")]
          ])
      ])
  ]

#eval toString bProof.sequent            -- "⊢ B(x, y)"
#eval bProof.backEdges                    -- [("U1", "R"), ("U2", "R1")]

/-! ### Trace extraction + SCT check -/

#eval (extractTraceSCGs bProof).map toString
-- Expected: one strict-on-0 graph and one ≥0,>1 graph.

#eval SCGraph.checkMultiSCT (extractTraceSCGs bProof)   -- true

#eval (synthMeasure (extractTraceSCGs bProof) 2 |>.map toString).getD "none"
-- Expected: "lex (a0, a1)"

/-! ### Stage 3: the real theorem -/

def myB : Nat → Nat → Prop
  | 0,         _        => True
  | .succ x,   0        => myB x 1
  | .succ x,   .succ y  => myB (.succ x) y

cyclic_thm myB_all : myB := bProof

/-! ### Using it downstream -/

example : myB 4 9 := myB_all 4 9

#check @myB_all                         -- ∀ (x y : Nat), myB x y
