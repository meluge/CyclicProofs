import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd

/-!
# Stage-1 cyclic-proof example

The simplest non-trivial cyclic proof: `∀ x : Nat, P(x)` where `P` is a
trivial predicate defined by `P(0) ⇔ ⊤` and `P(suc x) ⇔ P(x)`.

## The cyclic derivation

```
[R]   P(x)                      (root; case split on x)
 ├── [C0]  P(0)                 (leaf: unfold ⇒ ⊤)
 └── [C1]  P(suc x')            (unfold ⇒ P(x'))
      └── [U]  P(x')            (back-edge to R with σ = {x ↦ x'})
```

The back-edge `U → R` has **one trace**: predicate position 0. Along
the path R→C1→U the ancestor's variable `x` has been substituted (via
the case split) to `suc x'`, and then the back-edge reinstates position
0 with `x'`, which is a strict subterm of `suc x'`. Hence the trace
graph is `dom=1, codom=1, [(0 -→ 0)]` (strict self-loop).

Stage 1 just hand-builds this graph and runs the existing multi-SCT
check on it — validating that the shared kernel is the right target
for the proof-side extractor to plug into.
-/

open Cyclic.Proof

/-! ### The proof tree, built as data -/

def pAtX     : Formula := { pred := "P", args := [.var "x"] }
def pAt0     : Formula := { pred := "P", args := [.ctor "zero" []] }
def pAtSucXp : Formula := { pred := "P", args := [.ctor "succ" [.var "x'"]] }
def pAtXp    : Formula := { pred := "P", args := [.var "x'"] }

def sAtX     : Sequent := .succ1 pAtX
def sAt0     : Sequent := .succ1 pAt0
def sAtSucXp : Sequent := .succ1 pAtSucXp
def sAtXp    : Sequent := .succ1 pAtXp

def pProof : ProofTree :=
  .caseSplit "R" sAtX "x" [
    (.ctor "zero" [],           .leaf "C0" sAt0 "unfold ⇒ ⊤"),
    (.ctor "succ" [.var "x'"],  .node "C1" sAtSucXp "unfold" [
       .back "U" sAtXp "R" [("x", .var "x'")]
    ])
  ]

-- Root sequent prints as the goal we're proving.
#eval toString pProof.sequent        -- "⊢ P(x)"

-- The tree has exactly one back-edge, U → R.
#eval pProof.backEdges               -- [("U", "R")]

/-! ### Automatic trace extraction (Stage 2)

`extractTraceSCGs` walks the tree, accumulating the case-split
substitution along the path, and emits one `SCGraph` per back-edge.
For the derivation above, the path R → C1 → U carries σ = {x ↦ succ x'},
so the ancestor's instantiated args are [succ x'] and the back-edge's
args are [x']. Position 0 maps to position 0 strictly. -/

#eval (extractTraceSCGs pProof).map toString
-- ["SCGraph(1 → 1): [0 ->→ 0]"]

#eval SCGraph.checkMultiSCT (extractTraceSCGs pProof)   -- true

/-! ### Hand-built reference graph (same shape)

Kept as a sanity comparison; `extractTraceSCGs pProof` should produce
exactly this. -/

def pTraceGraph : SCGraph where
  dom := 1
  codom := 1
  edges := [⟨0, 0, .strict⟩]

#eval toString pTraceGraph                         -- SCGraph(1 → 1): [0 ->→ 0]
#eval SCGraph.checkMultiSCT [pTraceGraph]          -- true

/-! ### Counterexample: a back-edge that fails to descend

A hypothetical proof tree where the back-edge's trace preserves (≥)
rather than strictly decreasing — the cyclic proof is unsound and
`checkMultiSCT` must reject it.
-/

def pBadTraceGraph : SCGraph where
  dom := 1
  codom := 1
  edges := [⟨0, 0, .nonstrict⟩]

#eval SCGraph.checkMultiSCT [pBadTraceGraph]       -- false

/-! ### Stage 3: unravelling to a real Lean theorem

`Cyclic.Unravel.translate` turns the validated `pProof` into a
Lean 4 tactic-script theorem. We define a matching Lean-side
predicate `myP : Nat → Prop` whose unfold equations line up with
the abstract `P(0) ⇔ ⊤` / `P(suc x) ⇔ P(x)` the proof tree uses,
then paste the emitted script verbatim as the body of `myP_all`.

The `#eval` below prints the emitted script; the theorem below it
is the paste. Both should line up — if the translator drifts, the
paste stops matching and the build breaks, which is the check.
-/

def myP : Nat → Prop
  | 0       => True
  | .succ x => myP x

cyclic_thm myP_all : myP := pProof

/-! ### Using the generated theorem like any other Lean theorem -/

-- Direct application at a concrete argument.
example : myP 7 := myP_all 7

-- As a hypothesis in a larger proof.
example (n : Nat) : myP n ∧ myP (n + 1) :=
  ⟨myP_all n, myP_all (n + 1)⟩

-- Check the elaborated type.
#check @myP_all        -- myP_all : ∀ (x : Nat), myP x
