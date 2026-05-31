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
  (`btPred`) for later use as the emitter's `defaultSimpPred`.
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

### 6. Paper-faithful annotation (Grotenhuis-Otten §5)

`PaperAnnotation.lean`:

- **Def 5.1 step**: walks the tree, building per-node Stack/Name/Reset
  annotations from the parent's annotation + the edge SCG. Each step
  produces fresh names (smallest-available naming convention from
  Lemma 5.4), reuses ancestor stacks where the SCG permits, and runs
  the reset-loop to fixpoint.
- **Lemma 5.9 fixpoint unfolding**: when a bud's initial annotation
  fails Theorem 5.2, iterate the annotation up to a key-bounded
  fixpoint. By Lemma 5.4 the alphabet is finite (`2^m + m`), so a
  fixpoint exists.
- **Theorem 5.2 check**: for each bud, verify that a progressing name
  exists in `Reset(bud) ∩ preserved`. Surfaces a `PASS ✓` / `FAIL ✗`
  diagnostic at the `[cyclic_thm]` site.

### 7. §6 augmentation — `Theorem6.lean :: computeAug`

Builds per-node `RelAnc / Ineq / Hyp / cov / σ` data (Grotenhuis-Otten
Lemmas 6.2–6.4):

- **`RelAnc(n_k)`** — the relativised-ancestor set: which root args
  are still reachable at this node under the path substitution.
- **`Ineq(n_k)`** — pairwise inequalities between root args that this
  node enforces.
- **`Hyp(n_k)`** — the IHs in scope at this node (one per sprout
  ancestor that introduced a fresh IH).
- **`cov(b)`** — for each bud, the var that "covers" the progressing
  name (the IH binding the bud applies).
- **`σ`** — Lemma 6.4's substitution: maps sprout-slot vars to
  bud-slot vars, prog-slot var to cov.

For btPredT's `node` arm, RelAnc = `{t}`, the sprout is the root
case-split (it introduces `ih_l`, `ih_r`), and each bud's `cov` picks
the corresponding subterm var.

### 8. §6 emission — `Theorem6.lean :: Emit.translate`

Walks the tree, emits Lean tactic syntax driven by the §6 data:

- **`.caseSplit` at a sprout** → `induction var generalizing rest with`
  (per Theorem 6.1's `>-ind'_x_prog` step — the sprout is where new
  IHs are introduced).
- **`.caseSplit` not at a sprout** → `cases var with` (Lemma 6.3's
  rule application — no new IH, just decompose).
- **`.back`** → `exact ih_<recVar> <σ-args>`, where `recVar` is read
  from σ's image of the prog var and the args are the σ-substituted
  rest-of-slots.
- **`.node "branch"`** → `simp [<defaultSimpPred>]; refine ⟨?_, …⟩; · child; …`.
- **`.leaf`** → user's closeTac (or default `simp`).

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

The root case-split is a sprout (descendants of the `node` arm use
`ih_l` and `ih_r`), so it emits as `induction`. In examples like
`ackTotal_cyc`, an inner case-split whose subtree has no bud reaching
back here emits as plain `cases` instead — that's the §6 rule
selection in action, distinguishing inductive content from rule
application.

### 9. Canonical replacement — back in `Tactic.lean`

- Parses the §6-emitted script via `Lean.Parser.runParserCategory`.
- **Rolls back env to `envBefore`** (the snapshot from step 1) — this
  removes the recursive `btPredT` from the env.
- Calls `Lean.Elab.Command.elabCommand` to add the §6-emitted
  `theorem btPredT`.
- Checks `Expr.hasSorry` on the resulting value:
  - **No sorry** → canonical §6 form ✓ — `btPredT` in the env is now
    the Theorem 6.1 structural-induction proof.
  - **Has sorry** → restore `envWithRecursive` + drop messages from the
    failed canonical attempt — `btPredT` is the recursive form
    (fallback).

The user-facing `btPredT` is **always exactly one declaration**, never
two. It's the Theorem 6.1 structural-induction proof when SCT + §6
emission succeed, and the recursive form when they don't.

## Mutual blocks

`cyclic_mutual` follows the same flow with two differences:

- **Step 3 / 4**: events from all entries are interleaved in the single
  event log. `Tactic.lean :: demuxMutualEvents` walks the chronological
  stream, attributing each `.companion lbl _` event to a specific
  theorem via the companion-target table (populated by a pre-elab
  syntactic scan of each entry's tactic body). Each entry gets its own
  per-entry tree.
- **Step 8**: `Theorem6.lean :: Emit.translateMutual` emits a
  `mutual def … end` block. Cross-theorem buds (whose `ancestor` label
  resolves to a sibling entry's companion) emit as
  `exact <sibling-thm-name> <σ-args>` instead of `exact ih_<var> …` —
  the sibling theorem is the IH provided by Lean's mutual-recursion
  termination check.
- **Step 6+7 are skipped for mutual.** The §6 augmentation
  (`computeAug`) uses `annotateTree`'s Lemma 5.9 unfolding, which
  doesn't terminate when a bud's ancestor isn't in the tree's
  ancestor stack (the cross-theorem case). Since cross-theorem buds
  emit as direct sibling calls — not IH applications — the §6 aug
  isn't needed for emission. Within-entry cycles in `cyclic_mutual`
  aren't yet supported.

## The two layers (architectural, not user-visible)

| Layer | Purpose | Visibility |
|---|---|---|
| **Recursive (interactive)** | Real Lean goals during writing; back's recursive call closes goals in real time | Internal; rolled back when canonical succeeds |
| **§6 (canonical)** | Theorem 6.1 structural-induction proof; the kernel-checked theorem | User-facing as `btPredT` (when it works) |

The cyclic-tactic system is essentially: **let the user write in cyclic
style with real interactivity, but make the kernel-checked artifact be
the §6 structural-induction form**. The interactive layer is
scaffolding for the InfoView and event capture; the §6 emission is the
canonical proof. They never coexist in the env.

## Module map

| Module | Role |
|---|---|
| `Tactic.lean` | Tactics (`cyclic`, `cyc_cases`, `back`), the `cyclic_thm` and `cyclic_mutual` commands, event recording, finalizer orchestration |
| `Build.lean` | Cyclic state types, `Expr → SubjectTerm/Sequent` converters, `eventsToTree` builder, tree pretty-printer, `SortInfo` introspection |
| `ProofTree.lean` | Data-DSL `ProofTree` type, `Sequent`/`Formula`/`SubjectTerm`, `extractTraceSCGsLabeled` (Brotherston trace condition encoded into SCT) |
| `SizeChange.lean` | `SCGraph`, closure, idempotent check (Lee-Jones-Ben-Amram POPL 2001) |
| `Measure.lean` | Measure synthesis (lex / sum / closure-witness greedy), Lee TOPLAS 2009 |
| `InductionOrder.lean` | Wehr Theorem 3.2.4 SCC-based induction-order construction |
| `Annotation.lean` | Heuristic reset annotation (Wehr §3.3-3.4, coarse SCT-closure reduction). Carried alongside `PaperAnnotation` for diagnostic comparison. |
| `PaperAnnotation.lean` | Grotenhuis-Otten Def 5.1 step + Lemma 5.9 unfolding + Theorem 5.2 check |
| `Theorem6.lean` | Per-node §6 augmentation + `Emit.translate` (single) and `Emit.translateMutual` (mutual) |
| `EmitCommon.lean` | Shared script-emission utilities (SortInfo, CtorInfo, termToLean, patToInductionCase, indentation) |
| `Reorganize.lean` | Proof-tree restructuring for non-aligned case-splits (currently unused in tactic-mode) |

## Where the theory fits

The system implements (or borrows the *vocabulary* of) several threads
from cyclic-proof theory:

- **Lee-Jones-Ben-Amram POPL 2001**: SCT closure + idempotent check
  (the termination-soundness check we run on every cyclic proof).
- **Brotherston PhD 2006**: trace condition (encoded into SCT via
  per-occurrence subterm comparison in `ProofTree.lean`).
- **Grotenhuis-Otten 2026 §5**: Stack/Name/Reset annotation (Def 5.1
  + Lemma 5.9 unfolding + Theorem 5.2 verification — `PaperAnnotation.lean`).
- **Grotenhuis-Otten 2026 §6**: the cyclic-to-inductive transformation
  itself (RelAnc / Ineq / Hyp / cov / σ data + Theorem 6.1
  emission — `Theorem6.lean`). This is what produces the canonical
  declaration.
- **Wehr 2025 PhD thesis §3.2 / Theorem 3.2.4**: the SCC algorithm
  for finding the induction order from the bud-companion graph
  (`InductionOrder.lean`). Used as a fallback / diagnostic; the §6
  emission doesn't depend on it.
- **Sprenger-Dam FoSSaCS 2003 Theorem 5**: the structural-translation
  tradition that §6 generalises. Cited for context; the actual
  emission path is §6, not Sprenger-Dam.

The §6-emitted `btPredT` proof is exactly the kind of artifact
Grotenhuis-Otten Theorem 6.1 produces — generated automatically from
the user's cyclic-style source rather than by hand.
