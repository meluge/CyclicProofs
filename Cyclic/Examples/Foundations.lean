import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd

/-!
# Cyclic Proofs: Foundations

What does a "cyclic proof" actually look like as a *data structure*?
This file builds the simplest possible cyclic proof — one variable,
one back-edge — by hand, so the moving parts are visible.

For day-to-day use, write cyclic proofs in the DSL form (see
`Cyclic/Examples/DSL.lean`); this file is for "look under the hood."

## The proof we'll build

Goal: `∀ x : Nat, myP x` where `myP` is defined by

  myP 0       ⇔ ⊤
  myP (suc x) ⇔ myP x

The cyclic derivation:

```
[R]   myP(x)                  (root; case-split on x)
 ├── [C0]  myP(0)              leaf — unfold ⇒ ⊤
 └── [C1]  myP(suc x')         unfold ⇒ myP(x')
      └── [U]  myP(x')         back-edge to R via σ = {x ↦ x'}
```

The back-edge says: "the goal at U is an instance of R's goal under
σ." SCT validates: under the path σ_path = {x ↦ suc x'}, R's args
become [suc x']; U's args are [x']. Position 0: x' is a strict subterm
of suc x' → strict descent. SCT passes; the synthesised lex measure
is just `x`.
-/

open Cyclic.Proof

/-! ### Step 1: build the formulas and sequents -/

def pAtX     : Formula := { pred := "P", args := [.var "x"] }
def pAt0     : Formula := { pred := "P", args := [.ctor "zero" []] }
def pAtSucXp : Formula := { pred := "P", args := [.ctor "succ" [.var "x'"]] }
def pAtXp    : Formula := { pred := "P", args := [.var "x'"] }

def sAtX     : Sequent := .succ1 pAtX
def sAt0     : Sequent := .succ1 pAt0
def sAtSucXp : Sequent := .succ1 pAtSucXp
def sAtXp    : Sequent := .succ1 pAtXp

/-! ### Step 2: build the proof tree as data -/

def pProof : ProofTree :=
  .caseSplit "R" sAtX "x" [
    (.ctor "zero" [],          .leaf "C0" sAt0 "unfold ⇒ ⊤"),
    (.ctor "succ" [.var "x'"], .node "C1" sAtSucXp "unfold" [
       .back "U" sAtXp "R" [("x", .var "x'")]
    ])
  ]

#eval toString pProof.sequent              -- "⊢ P(x)"
#eval pProof.backEdges                      -- [("U", "R")]

/-! ### Step 3: SCT trace extraction validates the cyclic structure

`extractTraceSCGs` walks the tree, accumulates path-substitutions
through every `caseSplit`, and emits one `SCGraph` per back-edge.
For our proof: one back-edge → one graph with strict descent on slot 0.
-/

#eval (extractTraceSCGs pProof).map toString
-- ["SCGraph(1 → 1): [0 ->→ 0]"]

#eval SCGraph.checkMultiSCT (extractTraceSCGs pProof)   -- true

/-! ### Step 4: hand off to `cyclic_thm` for unravelling

The matching Lean predicate. Its defining equations must line up with
how the cyclic proof unfolds. (Named `simpleP` to avoid collision with
the DSL example file.) -/

def simpleP : Nat → Prop
  | 0       => True
  | .succ x => simpleP x

/- `cyclic_thm` consumes the explicit `ProofTree` value, runs SCT,
   synthesises a measure from the closure witnesses, and emits a
   kernel-checked `def simpleP_all : ∀ x, simpleP x` with
   `termination_by`. The cyclic proof's measure travels into the output
   as the termination certificate. -/
cyclic_thm simpleP_all : simpleP := pProof

example : simpleP 7 := simpleP_all 7
#check @simpleP_all          -- ∀ (x : Nat), simpleP x

/-! ### Negative example: SCT rejects unsound cyclic structure

A back-edge whose trace doesn't strictly descend (only `≥`) would be
unsound. The multi-graph closure has an idempotent with no strict
self-loop, so `checkMultiSCT` returns false — and `cyclic_thm` would
refuse to elaborate such a proof. The soundness of the entire
framework lives in this check.
-/

def pBadTraceGraph : SCGraph where
  dom := 1
  codom := 1
  edges := [⟨0, 0, .nonstrict⟩]   -- ≥ instead of >

#eval SCGraph.checkMultiSCT [pBadTraceGraph]   -- false
