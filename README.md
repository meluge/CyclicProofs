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

## Where this leaves the cyclic-proof goal

Everything so far is the *termination* half of cyclic proofs — enough to
make Lean accept recursive **functions** whose termination is witnessed
by an SCT derivation. The step toward actual cyclic **proofs** (the
paper's subject) is still ahead: a data type for proof trees with
back-edges, an SCT-style trace condition on those back-edges, and a
translator that unfolds them into ordinary inductive Lean proofs.

## Building

```
lake build           # builds the library + example evals + the Main executable
lake exe cyclic      # runs Main.lean
```

Uses `leanprover/lean4:v4.29.0`.

## Reference

Grotenhuis & Otten, *Unravelling Abstract Cyclic Proofs into Proofs by
Induction* (2026), `2602.12054v1.pdf` in the repo root.
