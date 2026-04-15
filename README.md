# cyclic

A Lean 4 experiment in translating cyclic proofs into induction, following
Grotenhuis & Otten, *Unravelling Abstract Cyclic Proofs into Proofs by
Induction* (2026). The current work formalises the **termination substrate**
underneath that translation: size-change graphs, the multi-graph SCT
closure check, syntactic extraction from pattern-matching equations, and a
`cyclic_def` command that verifies termination and synthesises a Lean
`termination_by` measure automatically.

## What works today

### Pipeline

```
  equations (as AST)
        │
        ▼  extractAllSCGs
  [size-change graphs]
        │
        ▼  checkMultiSCT
     pass / fail   ──► (fail: reject definition)
        │
        ▼  synthMeasure
  lex / sum / fail ──► (fail: reject definition)
        │
        ▼  emit
  def … termination_by …
```

### `cyclic_def` command

Lets the user write a pattern-matching recursive definition in natural
Lean syntax. At elaboration time the macro:

1. Parses each equation into the `Equation` AST.
2. Extracts a size-change graph per recursive call.
3. Runs the multi-graph SCT check (composition-closure; every idempotent
   must have a strict self-loop).
4. Synthesises a termination measure — lex on a parameter permutation,
   else sum-of-args. Fails the command if neither works.
5. Emits a plain `def … termination_by …` and logs the chosen measure.

Demo definitions in `Cyclic/Example.lean`:

```lean
cyclic_def swapAdd2 : Nat → Nat → Nat          -- synthesises: a₀ + a₁
  | 0, y        => y
  | .succ x', y => .succ (swapAdd2 y x')

cyclic_def ack2 : Nat → Nat → Nat              -- synthesises: (a₀, a₁)
  | 0, y             => .succ y
  | .succ x, 0       => ack2 x (.succ .zero)
  | .succ x, .succ y => ack2 x (ack2 (.succ x) y)
```

A non-terminating swap is rejected at elaboration:

```lean
cyclic_def loopDef : Nat → Nat → Nat
  | x, y => loopDef y x
-- error: multi-SCT check FAILED
--   SCGraph(2 → 2): [0 -≥→ 1, 1 -≥→ 0]
--   Some idempotent in the composition-closure has no strict self-loop …
```

## Module layout

| File | Purpose |
| --- | --- |
| `Cyclic/SizeChange.lean` | `SCGraph`, composition, canonicalisation, `checkMultiSCT` (closure + idempotent check), single-graph `checkSCT` for comparison. |
| `Cyclic/Extract.lean` | `Pattern` / `Term` / `Equation` AST; structural comparison of callee args against caller patterns; `extractAllSCGs`. |
| `Cyclic/Measure.lean` | Lex- and sum-measure synthesis; `Measure` ADT; `synthMeasure`. |
| `Cyclic/Syntax.lean` | The `cyclic_def` command: value-returning syntax parsers, measure-to-syntax emitter, enforcement via `throwErrorAt` when SCT fails. |
| `Cyclic/Example.lean` | Driving demos: `swapAdd` (hand + extracted), Ackermann, multi-SCT closure tests, `cyclic_def` uses, a `#guard_msgs`-asserted failing case. |
| `Cyclic/ProofTree.lean` | `SubjectTerm` / `Formula` / two-sided `Sequent` / `ProofTree`; `extractTraceSCGs` with per-occurrence, per-arg flattened traces. |
| `Cyclic/Unravel.lean` | `Cyclic.Unravel.translate` — emits a Lean tactic-script theorem from a validated `ProofTree` (toy `Nat`-induction shape). |
| `Cyclic/ProofExample.lean` | `∀ x : Nat, P(x)` proof tree, hand + extracted trace graph, a negative example, and the unravelled `myP_all` theorem. |
| `Main.lean` | Tiny executable printing `swapAdd 3 5` and the SCT check result. |

## Extractor semantics

For each recursive call `f(a₀, …, a_{m-1})` in an equation with caller
patterns `(p₀, …, p_{n-1})`, edge `i →^ℓ j` is produced when:

| condition on `aⱼ` and `pᵢ` | label `ℓ` |
| --- | --- |
| `aⱼ` is structurally equal to `pᵢ` (variables by name) | ≥ |
| `aⱼ` is a strict subterm of `pᵢ` | > |
| otherwise | no edge |

This is slightly stronger than "callee arg must be a bare variable":
`ack(suc x, y') → ack(suc x, …)` correctly emits `(0 ≥ 0)` because
`suc x` structurally matches the caller pattern at position 0.

## Multi-graph SCT

Implemented in `Cyclic/SizeChange.lean`:

- `SCGraph.canon` — dedup edges on `(src,tgt)`, joining labels (strict
  wins) so graphs compare up to order/multiplicity.
- `SCGraph.equiv` — structural equality of canonical graphs.
- `SCGraph.comp` — composition (edge-chaining with label join).
- `SCGraph.closure` — smallest superset closed under pairwise
  composition, deduped by `equiv`; terminates because there are only
  finitely many canonical graphs on a fixed arity.
- `SCGraph.isIdempotent` — `g ∘ g ≡ g`.
- `SCGraph.checkMultiSCT` — every idempotent in the closure has a
  strict self-loop.

## Measure synthesis

Implemented in `Cyclic/Measure.lean`. Two schemas are tried on the
**original** graphs (not the closure — Lean needs the measure to decrease
on every call, not just over cycles):

1. **Lex**: find a permutation `π` of parameter indices such that for
   every graph `G` there is a position `j` where `G` has a strict
   self-loop at `π(j)`, with nonstrict self-loops at every earlier
   position. Emits `(a_{π(0)}, …, a_{π(k-1)})` as a nested pair,
   handled by Lean's default lex well-founded order on products.
2. **Sum**: every graph admits a bijection between callee args and
   caller params where every covering edge is ≥ and at least one is
   strict. Emits `a₀ + a₁ + …`.

If neither schema succeeds the `cyclic_def` command fails with a
pointed error. Not every SCT-valid function is covered by these two
schemas (e.g. mutual recursion or more elaborate measures), which is
where measure synthesis will need to grow.

## Cyclic proofs (stages 1–3)

On top of the termination substrate, the same SCT kernel now drives the
proof side: a data type for cyclic proof trees, automatic trace
extraction per back-edge, and an end-to-end unravelling of a validated
tree into an ordinary Lean theorem.

### Proof trees (`Cyclic/ProofTree.lean`)

- `SubjectTerm`, `Formula`, two-sided `Sequent` (`Γ ⊢ Δ`).
- `ProofTree` constructors: `leaf`, `identity`, `node` (generic rule,
  covers unfold), `caseSplit` (binds the variable being split so trace
  extraction sees the induced substitution), `back` (to an ancestor
  under a substitution).

### Trace extraction

`extractTraceSCGs` walks a tree accumulating a path-substitution from
every `caseSplit` and emits one `SCGraph` per back-edge. Vertices are
`(side, formula-occurrence, arg-position)` flattened to a single
index; edges are emitted only between **matched occurrences** (same
side, same position, same predicate, same arity), with descent labels
determined by structural subterm comparison of A's args under
`σ_path` against B's args. Unfolds don't need a dedicated constructor
— the unfolded form is already carried in the child node's sequent,
so endpoint comparison sees intervening unfolds implicitly.

The multi-graph SCT kernel (`SCGraph.checkMultiSCT`) is reused
unchanged to accept/reject the resulting graph set.

### Unravelling (`Cyclic/Unravel.lean`)

`Cyclic.Unravel.translate leanPred thmName t` emits a Lean 4 theorem
(as a `String`) that proves the sequent by well-founded induction on
the case-split variable. For the toy `∀ x : Nat, P(x)` derivation in
`Cyclic/ProofExample.lean`, the emitted script is pasted verbatim as
the proof of `myP_all` — if the translator drifts the paste stops
matching and the build fails, giving a mechanical end-to-end check.

Supported shape today: root `caseSplit` on one `Nat` variable, cases
closing as `leaf` (emit `simp [leanPred]`) or as a `back` (bare or
inside a `node`) to the root (emit `simp [leanPred]; exact ih`). Any
other shape emits a `sorry`-stub so the output still parses.

### Known generality gaps (vs. Grotenhuis & Otten)

- Rules that reindex occurrences (weakening, contraction, exchange,
  cut) break position-based occurrence matching.
- No rule-designated principal formula or trace-progress annotation;
  progress is inferred from structural subterm descent.
- No inductive-predicate productions (unfold is modelled only by the
  child sequent's explicit form).
- No cross-predicate traces — matched occurrences must share a
  predicate name.
- `identity` is currently a rubber stamp (no `Γ ∩ Δ ≠ ∅` check).
- Unravelling is specialised to single-arg single-predicate sequents
  with a `Nat` induction variable.

## Building

```
lake build           # builds the library + example evals + the Main executable
lake exe cyclic      # runs Main.lean
```

Uses `leanprover/lean4:v4.29.0`.

## Reference

Grotenhuis & Otten, *Unravelling Abstract Cyclic Proofs into Proofs by
Induction* (2026), `2602.12054v1.pdf` in the repo root.
