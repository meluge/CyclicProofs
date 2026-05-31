# cyclic

A Lean 4 implementation of cyclic-proof unravelling. Cyclic proofs (Brotherston 2006) are validated for termination via the size-change principle (Lee, Jones, Ben-Amram 2001) and translated into kernel-checked Lean theorems by a paper-faithful implementation of Grotenhuis-Otten Theorem 6.1 (arXiv 2602.12054 §6). The cyclic structure is rewritten as nested `induction`/`cases` blocks with explicit IH applications. Soundness lives in Lean's kernel: every emitted declaration is rechecked, so an unraveller bug breaks the build, not the theorem.

The user writes cyclic proofs as **real Lean tactics**. The InfoView shows real goals at every cursor position; cyclic structure is recorded into a side-channel `ProofTree` for SCT validation and structural emission. Three primitive tactics:

- `cyclic <label>` — register the current goal as a named companion.
- `cyc_cases x with | <pat> => …` — case-split that records arm boundaries.
- `back <label> [{σ}]` — back-edge to `<label>`, with σ giving the recursive call's args.

## Quick taste

```lean
import CyclicTactic.Tactic

-- Standard Lean (for comparison)
theorem addComm_std (n m : Nat) : n + m = m + n := by
  induction n generalizing m with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ n' ih_n' =>
    rw [Nat.succ_add, Nat.add_succ]
    apply congrArg Nat.succ
    exact ih_n' m

-- Cyclic (same theorem)
cyclic_thm addComm_cyc (n m : Nat) : n + m = m + n by
  cyclic R
  cyc_cases n with
  | zero => rw [Nat.zero_add, Nat.add_zero]
  | succ n' =>
    rw [Nat.succ_add, Nat.add_succ]
    apply congrArg Nat.succ
    back R {n := n', m := m}
```

Standard Lean tactics (`rw`, `simp`, `apply`, `omega`, `have`, `refine`, …) work as normal inside arms.

### Mutual cyclic systems

```lean
mutual
  inductive Ev : Nat → Prop where
    | zero : Ev 0
    | succ (n : Nat) : Od n → Ev (Nat.succ n)
  inductive Od : Nat → Prop where
    | succ (n : Nat) : Ev n → Od (Nat.succ n)
end

cyclic_mutual
  thm od_is_nlike (n : Nat) (h : Od n) : Nlike n by
    cyclic R_O
    cyc_cases h with
    | succ k h' =>
      apply Nlike.succ
      back R_E {n := k, h := h'}    -- cross-companion back-edge
  thm ev_is_nlike (n : Nat) (h : Ev n) : Nlike n by
    cyclic R_E
    cyc_cases h with
    | zero      => exact Nlike.zero
    | succ k h' =>
      apply Nlike.succ
      back R_O {n := k, h := h'}    -- cross-companion back-edge
end_mutual
```

`cyclic_mutual` desugars to a `mutual def … end` block. Each entry registers its own companion; `back R_E` from inside one entry resolves to the *other* entry's recursive call via a pre-registered companion-target table. After the recursive form elaborates, the §6 emitter rewrites the block as `mutual def od_is_nlike … := by cases h with … exact ev_is_nlike k h' end` — each cross-companion bud becomes a direct sibling-theorem call. Soundness comes from Lean's mutual-recursion termination check.

## Pipeline

```
  user surface (`cyclic_thm` / `cyclic_mutual`)
        │
        ▼  recorder side-channel (events) → ProofTree
  ProofTree (case-splits + back-edges + σ + have + exists + branch)
        │
        ▼  extractTraceSCGsLabeled (per-occurrence, σ-substituted)
  size-change graphs, one per back-edge
        │
        ▼  SCGraph.checkMultiSCT (composition closure + idempotent check)
        │
        ▼  PaperAnnotation (Grotenhuis-Otten Def 5.1 + Lemma 5.9)
  per-node Stack/Name/Reset annotation; Theorem 5.2 PASS / FAIL
        │
        ▼  Theorem6 (RelAnc / Ineq / Hyp / cov + σ per Lemma 6.4)
  per-node §6 augmentation
        │
        ▼  Theorem6.Emit.translate   /   Theorem6.Emit.translateMutual
  nested `induction generalizing`     `mutual def … end` block
  for sprouts; `cases` otherwise;     case-splits in each entry;
  buds → `exact ih_<var> args`        cross-theorem buds →
                                      `exact <sibling-thm> args`
        │
        ▼  Lean.elabCommand (env rollback + canonical replace)
  kernel-checked theorem (single) or mutual def block
```

A case-split in the §6 emission becomes `induction <var> generalizing <rest> with` only if the node is a *sprout* (per Theorem 6.1: a node whose `Hyp(n_k)` extends the parent's); otherwise it emits as a plain `cases <var> with`, since no descendant bud needs an IH from this split. Cross-theorem buds in `cyclic_mutual` are routed via a companion-target table to the sibling theorem's name, relying on Lean's mutual-recursion termination check for soundness.

## Module layout

| File | Purpose |
| --- | --- |
| `SizeChange.lean` | `SCGraph`, composition, `checkMultiSCT` (Lee-Jones-Ben-Amram 2001). |
| `ProofTree.lean` | `Sequent`, `ProofTree`, per-occurrence trace extraction. |
| `Extract.lean` | `Pattern` / `Term` / `Equation` AST + SCG extraction. |
| `Measure.lean` | Lex / lex-subset / sum / greedy-closure measure synthesis. |
| `Annotation.lean` | Per-back-edge progressing name + global induction order. |
| `InductionOrder.lean` | Wehr 3.2.4-flavoured induction-order finder. |
| `Reorganize.lean` | Bubble-sort case-splits + descending-var back-edge retargeting. |
| `PaperAnnotation.lean` | Grotenhuis-Otten Def 5.1 (Stack/Name/Reset step) + Lemma 5.9 (unfolding fixpoint) + Theorem 5.2 checker. |
| `Theorem6.lean` | Per-node §6 augmentation (RelAnc / Ineq / Hyp / cov + σ) and `Emit.translate` / `Emit.translateMutual` — the Theorem 6.1 emitter. |
| `EmitCommon.lean` | Shared script-emission utilities — `SortInfo`, `CtorInfo`, `termToLean`, `patToInductionCase`, indentation helpers. |
| `Tactic.lean` | The `cyclic`, `cyc_cases`, `back` tactics; `cyclic_thm`, `cyclic_mutual` commands with §6 canonical-form replacement. |
| `Build.lean` | Event recorder + `ProofTree` builder + `Expr → SubjectTerm` + `buildSortInfo`. |
| `Examples/` | Worked examples — Smoke, Probe, drp, MutualSmoke, CyclistComparison. |

## Comparison with Cyclist (Brotherston-Gorogiannis-Petersen 2012)

`Examples/CyclistComparison.lean` ports cases from cyclist's first-order benchmark `benchmarks/fo/`:

| # | Cyclist sequent | Cyclist | CyclicTactic |
|---|-----------------|---------|--------------|
| 01 | `O(x) ⊢ N(x)` (mutual) | ✓ | ✓ (`cyclic_mutual`) |
| 07 | `N(x) ⊢ ADD(x,0,x)` | ✓ | ✓ |
| 09 | `ADD(x,y,z) ⊢ ADD(x,s y,s z)` | ✓ | ✓ |
| 10 | associativity of `ADD` | ✗ | ✓ |
| 11 | commutativity of `ADD` | ✗ | ✓ |

Cyclist fails on 10/11 because its first-order proof search applies sequent rules without equational reasoning. Our system, hosted on Lean, decouples the cyclic structure (validated by SCT) from the per-arm reasoning (closed by Lean tactics), so `congrArg Nat.succ` + `rw` discharges the algebraic step.

## Honest limitations

- **DAG-shaped proofs.** The paper allows arbitrary cycles in the proof graph; ours is tree-shaped (back-edges target ancestors).
- **Sequent rules that reindex occurrences** (weakening, contraction, exchange) break position-based occurrence matching. We work at Lean's term-goal level. Cut is expressible via `have`.
- **Pattern syntax.** DSL patterns are restricted to `[]`, numeric literals, `x :: xs`, and `<ctor> <var> …`. No nested patterns.
- **Per-call descent witnesses** are delegated to Lean's structural-recursion / mutual-termination check. The §6 annotation surfaces *which* position should descend (in `[cyclic_thm]` diagnostics), but the proof of decrease is reconstructed by Lean.
- **Reorganisation** handles uniform 2-level swaps. Non-uniform branches need to be written in the right order by hand.
- **`cyclic_mutual` within-entry cycles.** The §6 mutual emitter assumes all buds are cross-theorem (the bud's `ancestor` resolves to a sibling entry's companion, not a node in the same tree). Within-entry back-edges aren't yet supported — `computeAug` calls `annotateTree`'s Lemma 5.9 unfolding, which doesn't terminate on cross-theorem ancestors, so mutual blocks skip §6 augmentation. The omitted aug is unused for cross-theorem-only proofs (Lean's mutual-recursion check provides termination), but a mutual block with within-tree cycles would need the augmentation re-enabled with a cross-theorem guard.
- **SCT across `cyclic_mutual` blocks** isn't wired up yet — the MVP relies on Lean's mutual-recursion termination check. Adding it is local follow-up work (per-entry tree construction → `(entry-id, position)`-vertex multi-graph SCT).
- **Multi-companion within one theorem** (multiple `cyclic R1` / `cyclic R2` declarations in a single `cyclic_thm` body, with buds picking which) isn't supported. The §6 data model bakes in companion = root.
- **The unraveller itself is not formally verified.** Soundness comes from Lean's kernel rechecking every emitted declaration; the worst case of an unraveller bug is a broken build, not an unsound theorem.

## Building

```
lake build           # library + Main executable
lake exe cyclic      # runs Main.lean
```

Toolchain: `leanprover/lean4:v4.29.0`.

## References

The honest algorithmic ancestry, per component:

- **SCT validation** (`SizeChange.checkMultiSCT`) — Lee, Jones, Ben-Amram, *POPL 2001*. Composition closure + idempotent strict-self-loop check.
- **Cyclic-proof structure with per-occurrence traces** (`ProofTree`, `Extract`) — Brotherston, *PhD 2006*. Practical implementation precedent: Cyclist (Brotherston-Gorogiannis-Petersen, *PLPR 2012*).
- **Measure synthesis** (`Measure`) — in the spirit of Thiemann-Giesl (RTA 2003), characterised by Lee (TOPLAS 2009). We implement the easy quadrant (lex / lex-subset / sum / greedy-closure); Lee's full characterisation (max/min over lex tuples, polynomial measures) is not.
- **Stack/Name/Reset annotation** (`PaperAnnotation`) — Grotenhuis-Otten / Leigh-Wehr Definition 5.1 (per-node Stack/Name/Reset step), Lemma 5.4 (`2^m + m` alphabet bound), Lemma 5.9 (key-based unfolding fixpoint), and Theorem 5.2 verification. Per-back-edge progressing-name selection follows the paper's `Reset ∩ preserved` rule.
- **Paper-faithful emission** (`Theorem6.Emit.translate` / `translateMutual`) — Grotenhuis-Otten Lemmas 6.2–6.4 + Theorem 6.1. Sprout-driven `induction` placement (Lemma 6.3's rule selection: `induction` at sprouts, `cases` otherwise), σ from Lemma 6.4 for IH applications, per-bud `RelAnc / Ineq / Hyp / cov` data, mutual-block emission with cross-theorem buds. Replaces the earlier Sprenger-Dam-flavoured `Unravel.translate` we shipped before §6.
- **Tree reorganisation** (`Reorganize.swapAdjacent`, `reorder`) — Sprenger-Dam Theorem 5 / Wehr Fact 3.4.1, restricted to uniform 2-level swaps (no sub-proof duplication).
- **Heuristic annotation pass** (`Annotation`) — coarse SCT-closure reduction of Wehr's stack-controlled / reset-proof annotations (§§3.3–3.4). *Not* Wehr's Theorem 3.2.4 algorithm. Carried alongside the paper-faithful `PaperAnnotation` for diagnostic comparison.

What we *don't* implement despite reading the papers: Wehr Theorem 3.2.4 (bud-companion SCC algorithm), Sprenger-Dam Theorem 5 in full (general unfolding with sub-proof duplication), Grotenhuis-Otten Proposition 5.8 (true paper-faithful induction-order verification — we delegate to Lean's structural-recursion / mutual-termination check), Lee 2009's full ranking-function characterisation, and Berardi-Tatsuta 2017 / Simpson 2017's HA-internal well-foundedness construction.

PDFs in [`papers/`](papers/):

- [`Wehr-2025-cyclic-proof-theory-phd-thesis.pdf`](papers/Wehr-2025-cyclic-proof-theory-phd-thesis.pdf) — Dominik Wehr, *Cyclic Proof Theory*, PhD thesis 2025.
- [`Grotenhuis-Otten-2026-unravelling-abstract-cyclic-proofs.pdf`](papers/Grotenhuis-Otten-2026-unravelling-abstract-cyclic-proofs.pdf) — Lide Grotenhuis & Daniël Otten, *Unravelling Abstract Cyclic Proofs into Proofs by Induction*, arXiv 2602.12054.
- [`Brotherston-Gorogiannis-Petersen-2012-cyclist-aplas.pdf`](papers/Brotherston-Gorogiannis-Petersen-2012-cyclist-aplas.pdf) — *Cyclist*, APLAS 2012.
- [`Lee-2009-size-change-toplas.pdf`](papers/Lee-2009-size-change-toplas.pdf) — Lee, TOPLAS 2009 — full size-change ranking-function characterisation.
- [`Berardi-Tatsuta-2017-intuitionistic-cyclic-proofs.pdf`](papers/Berardi-Tatsuta-2017-intuitionistic-cyclic-proofs.pdf) — Berardi & Tatsuta on the Brotherston-Simpson conjecture for intuitionistic logic.
- [`Brotherston-Distefano-Petersen-2011-automated-cyclic-entailment-cade.pdf`](papers/Brotherston-Distefano-Petersen-2011-automated-cyclic-entailment-cade.pdf) — *Automated cyclic entailment proofs in separation logic*, CADE 2011.
