# cyclic

A Lean 4 implementation of Grotenhuis & Otten's translation from cyclic
proofs to proofs by well-founded induction (*Unravelling Abstract Cyclic
Proofs into Proofs by Induction*, 2026; PDF in repo root). Two user-facing
commands:

- **`cyclic_def`** — pattern-matching recursive definitions whose
  termination is justified by the size-change principle. The macro
  validates SCT, synthesises a `termination_by` measure, and emits a
  plain Lean `def`.
- **`cyclic_thm`** — cyclic proofs of inductive theorems. Three surface
  forms (legacy explicit-tree, predicate + `by_cyclic` DSL, inline-goal
  + `by_cyclic` DSL). The macro validates SCT, builds a measure, and
  emits a regular `theorem` proven by (possibly nested) induction.

Both commands are sound because the kernel re-checks every emitted
declaration — the unraveller's correctness isn't formally proved, but
its output type-checks or it doesn't.

## Quick taste

```lean
-- Cyclic recursive def: size-change termination, lex measure synthesised
cyclic_def ack2 : Nat → Nat → Nat
  | 0, y             => .succ y
  | .succ x, 0       => ack2 x (.succ .zero)
  | .succ x, .succ y => ack2 x (ack2 (.succ x) y)
-- info: [cyclic_def ack2] multi-SCT PASS; measure = lex (a0, a1)

-- Cyclic theorem in inline-goal DSL form: write the goal directly
cyclic_thm myAddR0 (n : Nat) : myAdd n 0 = n by_cyclic
  cases n with
    | 0       => done by simp [myAdd]
    | succ n' => back {n := n'} by
        simp [myAdd]
        exact ih_n
-- emits a real theorem; #check @myAddR0 → ∀ (n : Nat), myAdd n 0 = n
```

## Pipeline

```
  user surface (def equations | proof tree | by_cyclic DSL)
        │
        ▼  (parse / walk into ProofTree or Equation list)
  abstract data
        │
        ▼  extractAllSCGs / extractTraceSCGs
  [size-change graphs]
        │
        ▼  checkMultiSCT       ──► reject if no termination certificate
        │
        ▼  synthMeasure         (diagnostic for cyclic_thm; required for cyclic_def)
  measure (lex / sum / none)
        │
        ▼  Unravel.translate / cyclic_def emit
  Lean script (def + termination_by | theorem ... := by ...)
        │
        ▼  elabCommand
  kernel-checked declaration
```

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
        exact ih_n
```

### `by_cyclic` DSL grammar

A *step* is one of:

| step | meaning |
| --- | --- |
| `done`                                 | leaf, default close `simp [<pred>]` (or bare `simp` for inline-goal form) |
| `done by <tactic>`                     | leaf with user-supplied close tactic |
| `back [<label>] [{var := term, …}]`    | back-edge to ancestor case-split (label defaults to nearest enclosing) |
| `back … by <tactic>`                   | back-edge with user-supplied close tactic |
| `cases <var> with \| <pat> => <step> …`| case-split on `<var>` with arms |
| `<label>: <step>`                      | attach a user label to the step (for back-edges to reach across nested cases) |

Patterns: `[]`, numeric literals, `x :: xs`, and generic `<ctor> <var> …`
applications. Constructors are introspected from the binder type's
inductive declaration in the Lean environment, so `Nat`, `List α`, and
user-defined inductives (any single-recursive constructor) work without
registration.

The *substitution* `{var := term, …}` is non-iterating: `{y := Nat.succ y}`
applies once and the inner `y` refers to the current scope (no
infinite-rewrite issues).

## Worked examples

| File | Theorem | What it shows |
| --- | --- | --- |
| `Cyclic/ProofExample.lean`  | `∀ x : Nat, myP x` | smallest non-trivial cyclic proof; explicit-tree form |
| `Cyclic/ProofExample2.lean` | `∀ x y : Nat, myQ x y` | back-edge re-binds non-induction var |
| `Cyclic/ProofExample3.lean` | `∀ x y : Nat, myB x y` | lex descent, multiple ancestors, nested case-splits |
| `Cyclic/ProofExample4.lean` | `∀ xs : List Nat, myL xs` | non-Nat inductive type via auto-introspection |
| `Cyclic/ProofExample5.lean` | DSL versions of all the above + `worker_terminates` | termination of a state-machine model |
| `Cyclic/ProofExample6.lean` | `∀ s : Stack, myS s` | user-defined inductive (`Stack`); also notes the multi-recursive limit |
| `Cyclic/ProofExample7.lean` | `myAdd n 0 = n` and `myAdd 0 n = n` | inline-goal form proving real (not propositionally trivial) inductive theorems |

## Module layout

| File | Purpose |
| --- | --- |
| `Cyclic/SizeChange.lean` | `SCGraph`, composition, canonicalisation, `checkMultiSCT`. |
| `Cyclic/Extract.lean` | `Pattern` / `Term` / `Equation` AST; `extractAllSCGs`. |
| `Cyclic/Measure.lean` | Lex- and sum-measure synthesis; `synthMeasure`. |
| `Cyclic/Syntax.lean` | The `cyclic_def` command (recursive defs with auto-termination). |
| `Cyclic/ProofTree.lean` | `SubjectTerm` / `Formula` / two-sided `Sequent` / `ProofTree`; per-occurrence trace extraction (`extractTraceSCGs`). |
| `Cyclic/Unravel.lean` | `translate` — emit a Lean tactic-script theorem from a validated `ProofTree`, parametric over the goal type and the default-simp predicate. |
| `Cyclic/ThmCmd.lean` | The `cyclic_thm` command (legacy form 1) + the shared `runCyclicThmCore` backend used by all forms. |
| `Cyclic/Tactic.lean` | The `by_cyclic` DSL: syntax, walker (DSL → `ProofTree`), and elab rules for forms 2 and 3. |
| `Cyclic/Example.lean` | `cyclic_def` demos: `swapAdd`, `ack2`, a non-terminating swap rejected at elaboration. |
| `Cyclic/ProofExample{,2..7}.lean` | `cyclic_thm` demos. |
| `Main.lean` | Tiny executable. |

## Trace extraction (proofs side)

For each back-edge `B → A`:
1. Walk the path from the root, accumulating a *path substitution*
   `σ_path` from every enclosing `caseSplit`.
2. At the back-edge, instantiate the ancestor's sequent under `σ_path`
   and compare it occurrence-by-occurrence, arg-by-arg, to the
   back-edge's sequent.
3. Emit one `SCGraph` per back-edge with vertices indexed by
   `(side, formula-occurrence, arg-position)` flattened to a single
   integer. Edges encode descent (≥ if structurally equal, > if strict
   subterm).

Multi-graph SCT is exactly the kernel from `cyclic_def` — same
`checkMultiSCT` for the function and the proof side.

## Pretty-print / introspection

`cyclic_thm` introspects the predicate's signature (or each binder's
type for the inline-goal form) via `forallTelescope` + `Lean.Environment`
lookup, then walks each inductive's constructor list to discover names
and recursive-arg positions. No per-type registration: any inductive
already in the environment works as long as each constructor has at
most one recursive argument.

## Honest limitations

- **Multi-recursive constructors** (`Tree.node l r`, two recursive
  args) fall back to a `sorry` stub — the translator doesn't yet bind
  multiple IHs (`ih_l`, `ih_r`) per arm. Phase 4.
- **Cross-predicate / mutual** back-edges aren't supported.
- **Sequent rules that reindex occurrences** (weakening, contraction,
  exchange, cut) break position-based occurrence matching.
- **`identity`** is currently `assumption` — no real `Γ ∩ Δ ≠ ∅`
  check.
- **Inline-goal form** uses bare `simp` as the default close tactic
  (no predicate to unfold automatically); user supplies specifics
  via `by simp [myAdd, …]` etc.
- **Pattern syntax** in the DSL is restricted: `[]`, `<num>`,
  `x :: xs`, and `<ctor> <var> …`. No nested patterns.

The unraveller itself is **not** formally verified. Soundness comes
from Lean's kernel re-checking every emitted theorem; the worst case
of an unraveller bug is a broken build, not an unsound theorem.

## Building

```
lake build           # library + #eval demos + Main executable
lake exe cyclic      # runs Main.lean
```

Uses `leanprover/lean4:v4.29.0`.

## Reference

Grotenhuis & Otten, *Unravelling Abstract Cyclic Proofs into Proofs by
Induction* (2026), `2602.12054v1.pdf` in the repo root.
