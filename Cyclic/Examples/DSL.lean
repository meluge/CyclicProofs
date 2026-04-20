import Cyclic.ProofTree
import Cyclic.SizeChange
import Cyclic.Unravel
import Cyclic.ThmCmd
import Cyclic.Tactic

/-!
# Cyclic Proofs: DSL Tour

The `by_cyclic` DSL hides the explicit `ProofTree` data construction
behind a tactic-mode-flavoured surface. Three forms are available; this
file demos each via a representative example.

  * `done`                              — leaf (default close `simp [<pred>]`)
  * `done by <tactic>`                  — leaf with user-supplied close
  * `back [<label>] [{var := term, …}]` — back-edge to an ancestor case-split
  * `back … by <tactic>`                — back-edge with user prelude;
                                          `recurse` substitutes for the
                                          auto-derived recursive call
  * `cases <var> with …`                — case-split
  * `branch · <step> · <step> · …`      — n-ary subgoal split (multi-rec)
  * `<label>: <step>`                   — name an ancestor for back-edge targeting

See `Cyclic/Examples/Foundations.lean` for what the underlying
`ProofTree` data structure looks like, and `Cyclic/Examples/Advanced.lean`
for paper-faithful cases that demonstrate WF-emission's added power.
-/

/-! ### 1. Predicate form, single Nat variable -/

def myP : Nat → Prop
  | 0       => True
  | .succ x => myP x

cyclic_thm myP_all : myP x by_cyclic
  cases x with
    | 0       => done
    | succ x' => back {x := x'}

example : myP 7 := myP_all 7

/-! ### 2. Non-Nat inductive (List) — auto-introspection

`cyclic_thm` walks the predicate's argument types via Lean's
`Environment` to discover constructors and their recursive-arg
positions. No per-type registration: any inductive in the environment
works. -/

def myL : List Nat → Prop
  | []       => True
  | _ :: xs  => myL xs

cyclic_thm myL_all : myL xs by_cyclic
  cases xs with
    | []         => done
    | cons x xs' => back {xs := xs'}

example : myL [1, 2, 3] := myL_all [1, 2, 3]

/-! ### 3. Lex descent (nested case-splits, multiple ancestors)

The two back-edges have different descent patterns: `U1` strictly
descends on slot 0 (x), `U2` preserves slot 0 and strictly descends on
slot 1 (y). The lex measure `(x, y)` covers both — synthesised
automatically from the SCT trace graphs.

Note the explicit `R:` label on the outer `cases`: when a back-edge
targets a non-nearest ancestor, the user names that ancestor so the
`back` step can address it. -/

def myB : Nat → Nat → Prop
  | 0,         _        => True
  | .succ x,   0        => myB x 1
  | .succ x,   .succ y  => myB (.succ x) y

cyclic_thm myB_all : myB x y by_cyclic
  R: cases x with
    | 0       => done
    | succ x' =>
      cases y with
        | 0       => back R {x := x', y := 1}    -- non-nearest: needs label
        | succ y' => back {y := y'}              -- nearest enclosing case-split

example : myB 4 9 := myB_all 4 9

/-! ### 4. Inline-goal form: write the theorem statement directly

The most natural surface — reads exactly like an ordinary Lean theorem.
Used together with `recurse`, the user types nothing about the
unravelled form's IH binding name. -/

def myAdd : Nat → Nat → Nat
  | 0,        y => y
  | .succ x,  y => .succ (myAdd x y)

cyclic_thm myAddR0 (n : Nat) : myAdd n 0 = n by_cyclic
  cases n with
    | 0       => done by simp [myAdd]
    | succ n' => back {n := n'} by
        simp [myAdd]
        recurse                  -- substituted for `exact myAddR0 n'`
                                 -- (the recursive call) in emission

example (n : Nat) : myAdd n 0 = n := myAddR0 n
#check @myAddR0   -- ∀ (n : Nat), myAdd n 0 = n
