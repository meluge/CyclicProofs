# cyclic

A Lean 4 implementation of cyclic-proof unravelling. Cyclic proofs (Brotherston 2006) are validated for termination via the size-change principle (Lee, Jones, Ben-Amram 2001) and translated into kernel-checked Lean theorems — either as nested `induction` (Sprenger-Dam FoSSaCS 2003 tradition) or as `WellFounded.fix` over a synthesised lex/sum measure (Lee TOPLAS 2009 / Thiemann-Giesl 2003 family). Soundness lives in Lean's kernel: every emitted declaration is rechecked, so an unraveller bug breaks the build, not the theorem.

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

`cyclic_mutual` desugars to a `mutual def … end` block. Each entry registers its own companion; `back R_E` from inside one entry resolves to the *other* entry's recursive call via a pre-registered companion-target table. Soundness comes from Lean's mutual-recursion termination check.

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
        ▼  Annotation
  per-back-edge progressing name + global induction order
        │
        ▼  dispatcher: try structural, else reorganise, else WF
  Unravel.translate                 Unravel.translateWF
  nested `induction generalizing`   def + termination_by
  back-edges → auto-IH              WellFounded.fix on measure
        │
        ▼  Lean.elabCommand
  kernel-checked theorem
```

The dispatcher first checks `canStructural` on the user's tree. If the user's case-split nesting doesn't match the synthesised induction order, `Reorganize` bubble-sorts case-splits (Sprenger-Dam Theorem 5 / Wehr Fact 3.4.1, restricted to uniform 2-level swaps with descending-variable back-edge retargeting). If reorganisation can't help, the WF emitter takes over.

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
| `Unravel.lean` | `translate` (structural) + `translateWF` (well-founded). |
| `Tactic.lean` | The `cyclic`, `cyc_cases`, `back` tactics; `cyclic_thm`, `cyclic_mutual` commands. |
| `Build.lean` | Event recorder + `ProofTree` builder + `Expr → SubjectTerm`. |
| `Examples/` | Worked examples — Smoke, Probe, drp, CyclistComparison. |

`PIPELINE.md` walks the flow end-to-end on a multi-recursive example.

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
- **Per-call descent witnesses** are delegated to Lean's `decreasing_by`. The reset annotation surfaces *which* position should descend (in diagnostics and in `-- prog = aN` comments in WF emission), but the proof of decrease is reconstructed by Lean.
- **Reorganisation** handles uniform 2-level swaps. Non-uniform branches fall through to WF.
- **WF emission of `have` / `exists`** isn't implemented (those steps emit `sorry` on the WF path). In practice this isn't a real limitation because such proofs route through structural emission.
- **SCT across `cyclic_mutual` blocks** isn't wired up yet — the MVP relies on Lean's mutual-recursion termination check. Adding it is local follow-up work (per-entry tree construction → `(entry-id, position)`-vertex multi-graph SCT).
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
- **Structural translation** (`Unravel.translate`, nested `induction generalizing`) — Sprenger, Dam, *FoSSaCS 2003*. The same pattern reappears in Wehr (*PhD 2025*) and the Grotenhuis-Otten / Leigh-Wehr generalisation to abstract CPS.
- **Tree reorganisation** (`Reorganize.swapAdjacent`, `reorder`) — Sprenger-Dam Theorem 5 / Wehr Fact 3.4.1, restricted to uniform 2-level swaps (no sub-proof duplication).
- **Annotation pass** (`Annotation`) — coarse SCT-closure reduction of Wehr's stack-controlled / reset-proof annotations (§§3.3–3.4). *Not* Wehr's Theorem 3.2.4 algorithm.

What we *don't* implement despite reading the papers: Wehr Theorem 3.2.4 (bud-companion SCC algorithm), Sprenger-Dam Theorem 5 in full (general unfolding with sub-proof duplication), Grotenhuis-Otten / Leigh-Wehr's abstract-CPS framework, Lee 2009's full ranking-function characterisation, and Berardi-Tatsuta 2017 / Simpson 2017's HA-internal well-foundedness construction. PDFs in repo root: `cyclicprooftheory.pdf` (Wehr 2025), `2602.12054v1.pdf` (Grotenhuis-Otten / Leigh-Wehr), `cyclist.pdf` (Brotherston et al. 2012), `1498926.1498928.pdf` (Lee 2009).
