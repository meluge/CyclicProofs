# cyclic

A Lean 4 implementation of Grotenhuis & Otten's translation from cyclic
proofs to proofs by well-founded recursion (*Unravelling Abstract Cyclic
Proofs into Proofs by Induction*, 2026; PDF in repo root).

Two user-facing commands:

- **`cyclic_def`** — pattern-matching recursive definitions whose
  termination is justified by the size-change principle. Validates SCT,
  synthesises a `termination_by` measure, emits a plain Lean `def`.
- **`cyclic_thm`** — cyclic proofs of inductive theorems. Three surface
  forms (legacy explicit-tree, predicate + `by_cyclic` DSL, inline-goal
  + `by_cyclic` DSL). Validates SCT, synthesises a measure from the SCT
  closure witnesses, emits a `def : ∀ args, goal := … termination_by …`
  where each cyclic back-edge becomes a recursive call discharged by the
  measure.

Soundness comes from the kernel: every emitted declaration is rechecked,
so an unraveller bug breaks the build, not the theorem.

## Quick taste

```lean
-- Cyclic recursive def: SCT termination, lex measure synthesised
cyclic_def ack2 : Nat → Nat → Nat
  | 0, y             => .succ y
  | .succ x, 0       => ack2 x (.succ .zero)
  | .succ x, .succ y => ack2 x (ack2 (.succ x) y)
-- info: [cyclic_def ack2] multi-SCT PASS; measure = lex (a0, a1)

-- Cyclic theorem in inline-goal DSL: write the goal directly
cyclic_thm myAddR0 (n : Nat) : myAdd n 0 = n by_cyclic
  cases n with
    | 0       => done by simp [myAdd]
    | succ n' => back {n := n'} by
        simp [myAdd]
        recurse                    -- back-edge as semantic primitive
-- emits a real theorem; #check @myAddR0 → ∀ (n : Nat), myAdd n 0 = n

-- Sum measure (swap-style, no per-arg structural decrease)
cyclic_thm swapP_all (x : Nat) (y : Nat) : swapP x y by_cyclic
  cases x with
    | 0       => done by simp [swapP]
    | succ x' => back {x := y, y := x'} by
        simp [swapP]
        recurse
-- info: measure = a0 + a1   ← sum measure synthesised from SCT closure

-- Multi-recursive (BinTree) with branching back-edges
cyclic_thm myT_all : myT t by_cyclic
  cases t with
    | leaf      => done
    | node l r  =>
        branch
          · back {t := l}
          · back {t := r}
```

## Paper-faithful pipeline

```
  user surface (def equations | proof tree | by_cyclic DSL)
        │
        ▼  parse / walk → abstract data
  ProofTree (case-splits + back-edges + σ)
        │
        ▼  extractTraceSCGs (per-occurrence, σ-substituted)
  size-change graphs, one per back-edge
        │
        ▼  SCGraph.checkMultiSCT (composition closure + idempotent check)
     pass / fail   ──► reject if SCT fails
        │
        ▼  synthMeasure: cascade of schemas
  measure (lex perm | lex subset | sum | greedy from closure witnesses)
        │
        ▼  Cyclic.Unravel.translateWF
  Lean script:  def name : ∀ args, goal := fun args => match … termination_by …
                each back-edge becomes a recursive call to `name`
        │
        ▼  Lean.elabCommand
  kernel-checked def + WF recursion validates each call against the measure
```

The cyclic proof's measure travels into the emitted code as the
`termination_by` clause. Lean's well-founded recursion machinery then
discharges each per-call descent — so the cyclic structure's soundness
witness is an explicit, kernel-checked artifact of the output. This is
the paper's unravelling step (§6) realised in Lean.

## `cyclic_thm` surface forms

```lean
-- Form 1 (legacy): explicit ProofTree value
cyclic_thm myL_all : myL := lProof

-- Form 2: predicate + DSL
cyclic_thm myL_all : myL xs by_cyclic
  cases xs with
    | []         => done
    | cons x xs' => back {xs := xs'}

-- Form 3: inline goal + DSL — reads like a normal Lean theorem
cyclic_thm myAddR0 (n : Nat) : myAdd n 0 = n by_cyclic
  cases n with
    | 0       => done by simp [myAdd]
    | succ n' => back {n := n'} by
        simp [myAdd]
        recurse
```

## `by_cyclic` DSL grammar

A *step* is one of:

| step | meaning |
| --- | --- |
| `done`                                 | leaf, default close `simp [<pred>]` (or bare `simp` for inline-goal form) |
| `done by <tactic>`                     | leaf with user-supplied close tactic |
| `back [<label>] [{var := term, …}]`    | back-edge to ancestor case-split (label defaults to nearest enclosing) |
| `back … by <tactic>`                   | back-edge with user prelude; `recurse` substitutes for the auto-derived recursive call |
| `cases <var> with \| <pat> => <step> …`| case-split on `<var>` with arms |
| `branch · <step> · … · <step>`         | split a goal into n subgoals (auto `refine ⟨?_, …⟩`); per-branch back-edges |
| `<label>: <step>`                      | attach a user label to the step (for back-edges to reach across nested cases) |

**Patterns:** `[]`, numeric literals, `x :: xs`, and generic
`<ctor> <var> …` applications. Constructors are introspected from the
binder type's inductive declaration in the Lean environment, so `Nat`,
`List α`, and any user-defined inductive (single- or multi-recursive)
work without registration.

**Substitution:** `{var := term, …}` is non-iterating; e.g.
`{y := Nat.succ y}` rewrites once and the inner `y` refers to the
current scope (no infinite-rewrite issues).

**`recurse`:** semantic primitive that the translator substitutes for
`exact <recursive-call-with-σ-args>`. The user never has to type
`exact name args` manually — the cyclic-proof flavour is preserved
even inside custom tactic blocks.

## Worked examples

| File | Theorem | What it shows |
| --- | --- | --- |
| `Cyclic/ProofExample.lean`   | `∀ x : Nat, myP x` | smallest cyclic proof; explicit-tree form |
| `Cyclic/ProofExample2.lean`  | `∀ x y : Nat, myQ x y` | back-edge re-binds non-induction var |
| `Cyclic/ProofExample3.lean`  | `∀ x y : Nat, myB x y` | lex descent, multiple ancestors, nested case-splits |
| `Cyclic/ProofExample4.lean`  | `∀ xs : List Nat, myL xs` | non-Nat inductive type via auto-introspection |
| `Cyclic/ProofExample5.lean`  | DSL versions of the above + `worker_terminates` | termination of a state-machine model |
| `Cyclic/ProofExample6.lean`  | `∀ s : Stack, myS s` | user-defined inductive |
| `Cyclic/ProofExample7.lean`  | `myAdd n 0 = n`, `myAdd 0 n = n` | inline-goal form proving real (not propositionally trivial) inductive theorems |
| `Cyclic/ProofExample8.lean`  | `∀ t : BinTree, myT t` | **multi-recursive constructor** (`node l r`); branching back-edges |
| `Cyclic/ProofExample9.lean`  | `∀ x y, swapP x y` | **sum-measure cyclic proof** — neither argument structurally decreases, but their sum does. Demonstrates WF emission enables proofs nested induction can't express. |
| `Cyclic/ProofExample10.lean` | `∀ m n, 0 < ack m n` | **Ackermann** (paper Example 4.2); compound substitution RHS, two back-edges, lex measure |

## Module layout

| File | Purpose |
| --- | --- |
| `Cyclic/SizeChange.lean` | `SCGraph`, composition, canonicalisation, `checkMultiSCT`. |
| `Cyclic/Extract.lean` | `Pattern` / `Term` / `Equation` AST; `extractAllSCGs`. |
| `Cyclic/Measure.lean` | Measure synthesis cascade: `synthLexOrder` → `synthLexSubset` → `sumMeasureWorks` → `synthLexGreedy`. Closure-witness extraction. |
| `Cyclic/Syntax.lean` | The `cyclic_def` command. |
| `Cyclic/ProofTree.lean` | `SubjectTerm` / `Formula` / two-sided `Sequent` / `ProofTree`; per-occurrence trace extraction (`extractTraceSCGs`). |
| `Cyclic/Unravel.lean` | `translateWF` — emit a Lean WF-recursion `def` with `termination_by`, with each back-edge as a recursive call. The legacy `translate` (induction-based) is still present but unused. |
| `Cyclic/ThmCmd.lean` | The `cyclic_thm` command (legacy form 1) + the shared `runCyclicThmCore` backend. |
| `Cyclic/Tactic.lean` | The `by_cyclic` DSL: syntax (`done` / `back` / `cases` / `branch` / labels / `by tac`), walker, elab rules for forms 2 and 3, the `recurse` placeholder tactic. |
| `Cyclic/Example.lean` | `cyclic_def` demos: `swapAdd`, `ack2`, a non-terminating swap rejected at elaboration. |
| `Cyclic/ProofExample{,2..10}.lean` | `cyclic_thm` demos. |
| `Main.lean` | Tiny executable. |

## Trace extraction (proofs side)

For each back-edge `B → A`:
1. Walk the path from the root, accumulating a *path substitution*
   `σ_path` from every enclosing `caseSplit`.
2. At the back-edge, instantiate the ancestor's sequent under `σ_path`
   and compare it occurrence-by-occurrence, arg-by-arg, to the
   back-edge's sequent (which is itself the result of applying the
   back-edge's own `σ` to the ancestor's args).
3. Emit one `SCGraph` per back-edge with vertices indexed by
   `(side, formula-occurrence, arg-position)` flattened to a single
   integer. Edges encode descent (≥ if structurally equal, > if strict
   subterm).

Multi-graph SCT is the same `checkMultiSCT` kernel `cyclic_def` uses.

## Measure synthesis (paper-faithful)

After SCT validates the cyclic structure, `synthMeasure` extracts a
concrete termination measure for `termination_by`. The cascade:

1. **`synthLexOrder`** — try every full permutation of the arity
   positions; check whether some permutation lex-validates every input
   graph (per-call decrease).
2. **`synthLexSubset`** — try ordered subsets of positions, not just
   full permutations. Catches measures where some arguments don't
   participate in any descent.
3. **`sumMeasureWorks`** — bijection-based check for sum-measure
   termination (every callee position covered by an incoming edge from
   some caller position, with at least one strict). Catches swap-style
   recursions.
4. **`synthLexGreedy`** — paper-faithful greedy rank construction:
   compute the SCT closure, extract for each idempotent the set of
   positions with strict self-loops (the *witnesses* the SCT
   theorem produces), then build a lex order incrementally by picking
   at each step the position that strictly covers the most uncovered
   idempotents while having nonstrict self-loops at all earlier
   positions. Validates against input graphs.

The greedy step (4) is the algorithmic core of Grotenhuis-Otten's
stack-based measure construction (Definition 5.1) reduced to our
flat-arity setting. Closure witnesses and the synthesised measure are
both surfaced in the `cyclic_thm` info message after every successful
elaboration.

## Pretty-print / introspection

`cyclic_thm` introspects the predicate's signature (or each binder's
type for the inline-goal form) via `forallTelescope` +
`Lean.Environment` lookup, then walks each inductive's constructor list
to discover names and recursive-arg positions. No per-type registration:
any inductive already in the environment works.

## Honest limitations

- **Mutual / cross-predicate cycles** aren't supported. The paper
  handles systems of mutually-defined predicates with cycles spanning
  them; we're single-predicate per `cyclic_thm`.
- **Tree-shaped proofs only.** Our `ProofTree` is literally a tree —
  back-edges target ancestors. The paper allows arbitrary DAG cycles
  in the proof graph.
- **Sequent rules that reindex occurrences** (weakening, contraction,
  exchange, cut) break position-based occurrence matching. We work at
  Lean's term-goal level, not in two-sided sequent calculus.
- **`identity`** is currently `assumption` — no real `Γ ∩ Δ ≠ ∅` check.
- **Pattern syntax** in the DSL is restricted: `[]`, `<num>`,
  `x :: xs`, and `<ctor> <var> …`. No nested patterns.
- **Inline-goal form** uses bare `simp` as the default close tactic
  (no predicate to unfold automatically); user supplies specifics via
  `done by simp [myAdd, …]` etc.
- **Per-call descent witnesses** are delegated to Lean's
  `decreasing_by` machinery rather than emitted explicitly. The paper's
  `avail(a)` witnesses are constructed as proof terms; ours are
  reconstructed by Lean's WF prover. Functionally equivalent for the
  cases that work.
- **Richer-than-lex/sum measures** (multiset orderings, polynomial
  measures) for SCT-passing graphs that the synthesis cascade can't
  capture. Rare in practice but theoretically possible.

The unraveller itself is **not** formally verified. Soundness comes
from Lean's kernel rechecking every emitted declaration; the worst
case of an unraveller bug is a broken build, not an unsound theorem.

## Building

```
lake build           # library + #eval demos + Main executable
lake exe cyclic      # runs Main.lean
```

Uses `leanprover/lean4:v4.29.0`.

## Reference

Grotenhuis & Otten, *Unravelling Abstract Cyclic Proofs into Proofs by
Induction* (2026), `2602.12054v1.pdf` in the repo root.
