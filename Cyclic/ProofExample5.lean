import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic

/-!
# Cyclic proofs in tactic-style DSL (`by_cyclic`)

The same four cyclic proofs as `ProofExample{,2,3,4}.lean`, but written
in the tactic-style DSL instead of by hand-constructing `ProofTree`
values. The DSL is parsed into the same `ProofTree` representation and
fed through the same SCT-validation + unravelling pipeline.

Compare: the explicit-tree version of `myL_all` was

```
def lProof : ProofTree :=
  .caseSplit "R" sLAtXs "xs" [
    (.ctor "nil" [], .leaf "C0" sLAtNil "unfold ⇒ ⊤"),
    (.ctor "cons" [.var "x", .var "xs'"],
      .node "C1" sLAtCons "unfold" [
        .back "U" sLAtTail "R" [("xs", .var "xs'")]
      ])
  ]

cyclic_thm myL_all : myL := lProof
```

— vs. the DSL version below. No separate `Formula` / `Sequent` defs,
no labels for the boring cases, no quoted predicate strings.
-/

/-! ### Predicates -/

def myP' : Nat → Prop
  | 0       => True
  | .succ x => myP' x

def myQ' : Nat → Nat → Prop
  | 0,        _ => True
  | .succ x,  y => myQ' x (.succ y)

def myB' : Nat → Nat → Prop
  | 0,         _        => True
  | .succ x,   0        => myB' x 1
  | .succ x,   .succ y  => myB' (.succ x) y

def myL' : List Nat → Prop
  | []       => True
  | _ :: xs  => myL' xs

/-! ### Cyclic proofs in DSL form

`done` is the leaf, `back` is the back-edge, `cases ... with` is the
case-split. Auto-generated labels are used unless the user writes
`R: cases ...`. The substitution `{var := term}` is optional (defaults
to identity); `back` without an ancestor label defaults to the nearest
enclosing case-split.
-/

cyclic_thm myP'_all : myP' x by_cyclic
  cases x with
    | 0      => done
    | succ x' => back {x := x'}

cyclic_thm myQ'_all : myQ' x y by_cyclic
  cases x with
    | 0      => done
    | succ x' => back {x := x', y := Nat.succ y}

cyclic_thm myB'_all : myB' x y by_cyclic
  R: cases x with
    | 0      => done
    | succ x' =>
      cases y with
        | 0      => back R {x := x', y := 1}
        | succ y' => back {y := y'}

cyclic_thm myL'_all : myL' xs by_cyclic
  cases xs with
    | []         => done
    | cons x xs' => back {xs := xs'}

/-! ### Use them like real theorems -/

example : myP' 7        := myP'_all 7
example : myQ' 3 5      := myQ'_all 3 5
example : myB' 4 9      := myB'_all 4 9
example : myL' [1,2,3]  := myL'_all [1,2,3]

#check @myP'_all   -- ∀ (x : Nat), myP' x
#check @myQ'_all   -- ∀ (x y : Nat), myQ' x y
#check @myB'_all   -- ∀ (x y : Nat), myB' x y
#check @myL'_all   -- ∀ (xs : List Nat), myL' xs

/-! ### A more honestly-named example: termination of a state-machine model

The `Worker` type models a stateful process with two operations: `tick`
(do work, decrement an internal counter) and `idle` (terminal state).
The predicate `eventuallyIdles w` asserts that any reachable state
eventually reduces to `idle` — i.e., the worker terminates.

Strict descent on `tick`'s argument (the remaining work) lines up with
the cyclic-proof's back-edge structure exactly: this is the termination
proof of the Worker abstract machine, not just a predicate that happens
to be `True`. The `True` form is what falls out *because* termination
holds for all states.

This is the kind of theorem cyclic proofs were designed for: structural
well-foundedness of a recursive state space. The proof's
mathematical content is the descent argument, even though the `Prop`
itself is propositionally trivial.
-/

inductive Worker : Type
  | tick : Worker → Worker
  | idle : Worker

def eventuallyIdles : Worker → Prop
  | .idle    => True
  | .tick w  => eventuallyIdles w

cyclic_thm worker_terminates : eventuallyIdles w by_cyclic
  cases w with
    | idle    => done
    | tick w' => back {w := w'}

example : eventuallyIdles (.tick (.tick .idle)) := worker_terminates _

/-! ### What we can't yet prove (and what would be needed)

Genuinely deep theorems like `n + 0 = n` need the back-edge tactic to
do more than `exact ih_n` — typically `congr; exact ih_n` or
`simp [ih_n]`, because the IH applies to a sub-position of the goal,
not the whole goal.

Adding that requires extending the DSL with a custom leaf/back tactic
hook, e.g.:

```
back {n := n'} by (congr; exact ih_n)
done by (decide)
```

That's a Phase-7-ish DSL extension. The current scope is faithful to
what cyclic proofs *fundamentally* are — termination arguments — but
doesn't yet repurpose them as a frontend for arbitrary inductive
proofs.
-/
