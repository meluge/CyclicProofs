# CyclicTactic: end-to-end pipeline

How a `cyclic_thm` declaration flows from user source to kernel-checked
theorem. The running example is `btPredT` (multi-recursive over a
binary tree), which exercises every part of the pipeline.

## Source the user writes

```lean
cyclic_thm btPredT (t : BTr) (n : Nat) : btPred t n by
  cyclic R
  cyc_cases t with
  | leaf => trivial
  | node l r =>
    refine ⟨?_, ?_⟩
    · back R {t := l, n := n}
    · back R {t := r, n := n}
```

## Pipeline

### 1. Command elaboration — `Tactic.lean :: elabCyclicThm`

- Parses `name`, binders, type, tactic block.
- Snapshots the environment (`envBefore`) so we can later roll back if
  needed.
- Sets `thmCtx = (name.getId, [t, n])` so `back` knows which function
  to recursively call.

### 2. Recursive-form elaboration — Lean's standard `def` machinery

- Elaborates `def btPredT (t : BTr) (n : Nat) : btPred t n := by <tactics>`.
- The user's tactics fire one by one — the InfoView shows real Lean
  goals at every cursor position. This is the **interactive layer**.
- After this completes, the env temporarily contains `btPredT` as a
  recursive `def`. We snapshot it as `envWithRecursive` for the
  fallback path.

### 3. Event recording — three custom tactics

Each pushes an event into `CyclicState` (a global `IO.Ref`):

- **`cyclic R`** → `companion` event + records the goal-head name
  (`btPred`) for later use as Unravel's `defaultSimpPred`.
- **`cyc_cases t with | …`** → `caseSplitStart` event with arm
  position ranges + arm body source text (extracted via
  `Syntax.reprint`); delegates the actual case split to Lean's
  standard `cases`.
- **`back R {σ}`** → issues `exact btPredT l n` (recursive call to
  the def being defined), pushes a `back` event with σ + source
  position + source text.
- Closes with a `caseSplitEnd` after the cases tactic returns.

### 4. Tree construction — `Build.lean :: eventsToTree`

- Walks the linear event stream.
- For each `caseSplitStart` / `caseSplitEnd` scope: collect inner
  events, then **`assembleArms`** uses **source-position attribution**
  to map back events to arms (each back's position is checked against
  each arm's range — algorithmic, not heuristic).
- **One back per arm** → `.back` node (closeTac = arm body text with
  back call → `recurse`).
- **Two+ backs per arm** → `.node "branch"` (multi-rec, like btPredT's
  node arm).
- **No events** → `.leaf` (closeTac = arm body text).

For btPredT, the result is:

```
.caseSplit "R" (btPredT t n) "t"
  | leaf       → .leaf (closeTac = "trivial")
  | node(l,r)  → .node "branch"
                   · .back to R {t := l, n := n}
                   · .back to R {t := r, n := n}
```

### 5. SCT validation

`ProofTree.lean :: extractTraceSCGsLabeled` + `SizeChange.lean :: checkMultiSCT`:

- For each back-edge, builds an `SCGraph` by comparing the companion
  sequent (under path-substitution from case-split arms) against the
  back's sequent. For btPredT: `[0 ->→ 0, 1 -≥→ 1]` (strict descent
  on `t`, preserved on `n`).
- Multi-SCT runs the closure-idempotent check (Lee–Jones–Ben-Amram
  POPL 2001).

### 6. Wehr 3.2.4 — `InductionOrder.lean :: findInductionOrder`

SCC-based algorithm finds the lex induction order. For btPredT:
`[a0]` (just position 0, the `t` arg).

### 7. Unravel emission — `Unravel.lean :: translate`

Walks the tree, emits Lean tactic syntax as a string:

- `.caseSplit` → `induction var generalizing rest with | pat => …`.
- `.back` → `exact ih_…` (with σ args), or the user's closeTac with
  `recurse` substituted.
- `.node "branch"` → `simp [<defaultSimpPred>]; refine ⟨?_, …⟩; · child; …`.
- `.leaf` → user's closeTac (or default `simp`).

For btPredT, with `defaultSimpPred = "btPred"`:

```lean
theorem btPredT (t : BTr) (n : Nat) : btPred t n := by
  induction t generalizing n with
  | leaf => trivial
  | node l r ih_l ih_r =>
    simp [btPred]
    refine ⟨?_, ?_⟩
    · exact ih_l n
    · exact ih_r n
```

### 8. Canonical replacement — back in `Tactic.lean`

- Parses the emitted script via `Lean.Parser.runParserCategory`.
- **Rolls back env to `envBefore`** (the snapshot from step 1) — this
  removes the recursive `btPredT` from the env.
- Calls `Lean.Elab.Command.elabCommand` to add the Unravel-emitted
  `theorem btPredT`.
- Checks `Expr.hasSorry` on the resulting value:
  - **No sorry** → canonical Unravel form ✓ — `btPredT` in the env
    is now the Wehr structural-induction proof.
  - **Has sorry** → restore `envWithRecursive` + drop messages from the
    failed canonical attempt — `btPredT` is the recursive form
    (fallback).

The user-facing `btPredT` is **always exactly one declaration**, never
two. It's the Wehr-canonical structural-induction proof when SCT +
Unravel succeed, and the recursive form when they don't.

## The two layers (architectural, not user-visible)

| Layer | Purpose | Visibility |
|---|---|---|
| **Recursive (interactive)** | Real Lean goals during writing; back's recursive call closes goals in real time | Internal; rolled back when canonical succeeds |
| **Unravel (canonical)** | Wehr-translated structural-induction proof; the kernel-checked theorem | User-facing as `btPredT` (when it works) |

The cyclic-tactic system is essentially: **let the user write in cyclic
style with real interactivity, but make the kernel-checked artifact be
the Wehr-translated structural-induction form**. The interactive layer
is scaffolding for the InfoView and event capture; the Unravel emission
is the canonical proof. They never coexist in the env.

## Module map

| Module | Role |
|---|---|
| `Tactic.lean` | Tactics (`cyclic`, `cyc_cases`, `back`), the `cyclic_thm` command, event recording, finalizer orchestration |
| `Build.lean` | Cyclic state types, `Expr → SubjectTerm/Sequent` converters, `eventsToTree` builder, tree pretty-printer, `SortInfo` introspection |
| `ProofTree.lean` | Data-DSL `ProofTree` type, `Sequent`/`Formula`/`SubjectTerm`, `extractTraceSCGsLabeled` (Brotherston trace condition encoded into SCT) |
| `SizeChange.lean` | `SCGraph`, closure, idempotent check (Lee-Jones-Ben-Amram POPL 2001) |
| `Measure.lean` | Measure synthesis (lex / sum / closure-witness greedy), Lee TOPLAS 2009 |
| `InductionOrder.lean` | Wehr Theorem 3.2.4 SCC-based induction-order construction |
| `Annotation.lean` | Reset annotation (Grotenhuis-Otten / Wehr §3.3-3.4) |
| `Reorganize.lean` | Proof-tree restructuring for non-aligned case-splits (currently unused in tactic-mode) |
| `Unravel.lean` | Structural induction emission (Sprenger-Dam FoSSaCS 2003 Theorem 5) + WF emission (Wehr Ch. 6) |

## Where Wehr's framework fits

The system implements (or borrows the *vocabulary* of) several
threads from cyclic-proof theory:

- **Lee-Jones-Ben-Amram POPL 2001**: SCT closure + idempotent check
  (the soundness check we actually run).
- **Brotherston PhD 2006**: trace condition (encoded into SCT via
  per-occurrence subterm comparison in `ProofTree.lean`).
- **Sprenger-Dam FoSSaCS 2003 Theorem 5**: structural translation of
  cyclic proofs into nested induction (justifies what Unravel emits).
- **Wehr 2025 PhD thesis** §3.2 / Theorem 3.2.4: the SCC algorithm
  for finding the induction order from the bud-companion graph
  (`InductionOrder.lean`).

The Unravel-emitted `btPredT` proof is the kind of artifact Wehr's
unravelling theorem produces — except generated automatically from the
user's cyclic-style source rather than by hand.
