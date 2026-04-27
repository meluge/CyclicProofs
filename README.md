# cyclic

A Lean 4 implementation of cyclic-proof unravelling. The structural
translation (`Cyclic.Unravel.translate` emits nested `induction`) is in
the Sprenger-Dam (FoSSaCS 2003) tradition; the measure-synthesis
fallback (`Cyclic.Unravel.translateWF` emits `WellFounded.fix`) is in
the Lee-2009 / Thiemann-Giesl tradition. SCT validation is direct
Lee-Jones-Ben-Amram (POPL 2001). Cyclic-proof structure is generic
Brotherston (2006). We *gesture at* the Sprenger-Dam → Wehr →
Grotenhuis-Otten structural-translation lineage but don't implement
their specific algorithms — see *References* for the precise per-component
ancestry. Soundness lives in Lean's kernel: every emitted declaration
is rechecked, so an unraveller bug breaks the build, not the theorem.

Two libraries:

- **`Cyclic/`** — the **data-DSL** approach. The user writes the
  cyclic proof as parsed syntax that builds a `ProofTree` value, which
  gets validated and translated. Two commands:
  - **`cyclic_def`** — pattern-matching recursive definitions whose
    termination is justified by the size-change principle. Validates
    SCT, synthesises a `termination_by` measure, emits a plain Lean
    `def`.
  - **`cyclic_thm`** — cyclic proofs of inductive theorems. Three
    surface forms (legacy explicit-tree, predicate + `by_cyclic` DSL,
    inline-goal + `by_cyclic` DSL). Validates SCT, computes a
    paper-style reset annotation (per-back-edge progressing name +
    global induction order), reorganises the proof tree if the
    user-written case-split nesting doesn't match the induction order,
    then dispatches to either the structural emitter (paper-faithful
    nested `induction`) or the WF emitter (`WellFounded.fix` over a
    synthesised measure) depending on whether structural emission is
    feasible. The DSL also supports `have` (Cut / intermediate lemmas),
    `exists` (∃R), and `branch` for multi-recursive constructors.

- **`CyclicTactic/`** — the **tactic-mode** approach (sister library).
  The user writes the cyclic proof as real Lean tactics, gets the real
  Lean InfoView during writing, and the system records events to build
  a first-class `ProofTree` *as a side-channel*. After elaboration the
  tree is SCT-validated + Wehr 3.2.4 finds the lex induction order +
  `Unravel.translate` emits a structural-induction proof, which becomes
  the user-facing kernel-checked theorem. One command:
  - **`cyclic_thm name (binders) : type by tactics`** with three
    primitive tactics: `cyclic <label>` (mark companion), `cyc_cases x
    with | …` (case-split + record), `back R [{σ}]` (back-edge +
    recursive call). See `CyclicTactic/PIPELINE.md` for the full
    end-to-end pipeline.

## Quick taste

```lean
-- Cyclic recursive def: SCT termination, lex measure synthesised
cyclic_def ack2 : Nat → Nat → Nat
  | 0, y             => .succ y
  | .succ x, 0       => ack2 x (.succ .zero)
  | .succ x, .succ y => ack2 x (ack2 (.succ x) y)
-- info: [cyclic_def ack2] multi-SCT PASS; measure = lex (a0, a1)

-- Cyclic theorem in inline-goal DSL: write the goal directly,
-- with Lean's standard grouped binders
cyclic_thm myAddR0 (n : Nat) : myAdd n 0 = n by_cyclic
  cases n with
    | 0       => done by simp [myAdd]
    | succ n' => back {n := n'} by
        simp [myAdd]
        recurse                    -- back-edge as semantic primitive

-- Existential goal (∃R) — no separate predicate `def` needed.
-- The cyclic proof of Ackermann *totality* (Wehr Fig. 4-style):
cyclic_thm ackTotal_all (m n : Nat) : ∃ z, ack m n = z by_cyclic
  R: cases m with
    | 0 =>
      exists n + 1
      done by simp [ack]
    | succ m' =>
      cases n with
        | 0 =>
          back R {m := m', n := 1} by
            simp only [ack]; recurse
        | succ n' =>
          back R {m := m', n := ack (succ m') n'} by
            simp only [ack]; recurse

-- Sum measure (swap-style, no per-arg structural decrease)
cyclic_thm swapP_all (x y : Nat) : swapP x y by_cyclic
  cases x with
    | 0       => done by simp [swapP]
    | succ x' => back {x := y, y := x'} by
        simp [swapP]
        recurse
-- info: measure = a0 + a1; emission = WF (`termination_by`)

-- Multi-recursive (BinTree) with branching back-edges
cyclic_thm myT_all : myT t by_cyclic
  cases t with
    | leaf      => done
    | node l r  =>
        branch
          · back {t := l}
          · back {t := r}

-- Wrong-order case-split — auto-reorganised:
-- user wrote `cases y` outer, but SCT requires lex (x, y);
-- the dispatcher reorders to put `cases x` outer, retargets back-edges
-- by descending variable, and emits structurally.
cyclic_thm reorderP_all (x y : Nat) : reorderP x y by_cyclic
  R: cases y with
    | 0 =>
      cases x with
        | 0       => done by trivial
        | succ x' => back R {x := x'} by recurse
    | succ y' =>
      cases x with
        | 0       => done by trivial
        | succ x' => back R {x := succ x', y := y'} by recurse
-- info: emission = structural (nested `induction`, after reorganisation)
```

## Tactic-mode quick taste (`CyclicTactic/`)

The sister library lets you write cyclic proofs as **real Lean
tactics** — InfoView shows real goals at every cursor position, and
the user-facing theorem is the kernel-checked Wehr structural-
induction proof.

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

Three primitive tactics: `cyclic <label>` (mark companion), `cyc_cases
x with | …` (record-aware case-split), `back R [{σ}]` (back-edge to
companion R with substitution σ). Standard Lean tactics (`rw`, `simp`,
`apply`, `omega`, `have`, `refine`, etc.) work as normal *inside* arms
and are captured verbatim by `Syntax.reprint` for the eventual emission.

What happens behind the scenes: `cyclic_thm` snapshots the env →
elaborates the recursive form (so the InfoView works + cyclic events
get recorded) → builds a `ProofTree` from the events using source-
position-based per-arm attribution → runs `extractTraceSCGsLabeled` +
`multiSCT` + `findInductionOrder` (Wehr 3.2.4) → calls
`Unravel.translate` to emit a structural-induction script → rolls back
the env and elaborates the script as the canonical `<name>`. If
Unravel can't handle the shape (sorry-laden), restores the recursive
form as the fallback. Either way the user sees one declaration.

Worked example file: `CyclicTactic/Examples/drp.lean` (addComm and
Ackermann totality, both standard Lean and cyclic versions, with talk-
ready commentary). End-to-end pipeline doc:
`CyclicTactic/PIPELINE.md`.

## Pipeline

```
  user surface (def equations | proof tree | by_cyclic DSL)
        │
        ▼  parse / walk → abstract data
  ProofTree (case-splits + back-edges + σ + have + exists + branch)
        │
        ▼  extractTraceSCGsLabeled (per-occurrence, σ-substituted)
  size-change graphs, one per back-edge (labelled)
        │
        ▼  SCGraph.checkMultiSCT (composition closure + idempotent check)
     pass / fail   ──► reject if SCT fails
        │
        ▼  Cyclic.Annotation.annotate
  per back-edge: progressing name + cycle witness
  global: induction order on positions
        │
        ▼  Cyclic.Annotation.canStructural
  feasible? = SCG lex-validates AND tree's case-split order matches
        │
   ┌────┴────┐
   ▼         ▼ (not feasible: try reorganisation)
   │   Cyclic.Reorganize.reorder       (bubble-sort case-splits, à la Sprenger-Dam Th 5)
   │   Cyclic.Reorganize.retargetBacks (rewire back-edges by descending var)
   │   re-extract SCGs, re-check
   │   ┌────┴────┐
   │   ▼         ▼
   │   ok        still no?
   │             │
   ▼ (structural) ▼ (WF fallback)
  Cyclic.Unravel.translate          Cyclic.Unravel.translateWF
  nested `induction var generalizing rest` def + termination_by
  + back-edges discharged via auto-IH      + WellFounded.fix on measure
        │
        ▼  Lean.elabCommand
  kernel-checked theorem (or def) — soundness lives in Lean's kernel
```

Two emission paths, dispatched per theorem:

- **Structural** (preferred): nested `induction` mirroring the case-split
  tree — same family as Sprenger-Dam's μFOL-to-induction translation
  (FoSSaCS 2003) and Wehr §7's CHA<-to-HA translation. Reads like an
  ordinary Lean inductive proof.
- **WF (fallback)**: `def + termination_by + WellFounded.fix` over a
  synthesised lex/sum measure. Used for sum/swap-style cases where the
  per-call descent shows up only in the SCT *closure*, not the per-call
  input graph.

The dispatcher first checks `canStructural` on the user's tree; if it
fails (typically because the user wrote case-splits in an order that
doesn't match the synthesised induction order), it tries reorganisation
before falling through to WF.

## `cyclic_thm` surface forms

```lean
-- Form 1 (legacy): explicit ProofTree value
cyclic_thm myL_all : myL := lProof

-- Form 2: predicate + DSL — references a separately-defined predicate.
cyclic_thm myL_all : myL xs by_cyclic
  cases xs with
    | []         => done
    | cons x xs' => back {xs := xs'}

-- Form 3: inline goal + DSL — reads like a normal Lean theorem.
-- Supports Lean's grouped binders `(m n : Nat)` and arbitrary goal types
-- including existentials, conjunctions, equalities, etc.
cyclic_thm addAssoc_cyc (a b c : Nat) : (a + b) + c = a + (b + c) by_cyclic
  cases c with
    | 0       => done by rfl
    | succ c' => back {c := c'} by
        show Nat.succ ((a + b) + c') = Nat.succ (a + (b + c'))
        apply congrArg Nat.succ
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
| `have <name> : <type> := by <tac> <step>` | Cut / intermediate lemma. Binds `<name> : <type>` in scope for `<step>`; emits Lean's `have` tactic. (Wehr Ch. 2/3 Cut rule analogue.) |
| `exists <term> <step>` | ∃R: provide existential witness, then prove the residual goal in `<step>`. Emits `refine ⟨<term>, ?_⟩`. |

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

Five files in `Cyclic/Examples/`:

| File | Contents |
| --- | --- |
| `Cyclic/Examples/Foundations.lean` | Smallest cyclic proof (`∀ x : Nat, simpleP x`) built in the explicit-`ProofTree` form so the data structure is visible. Step-by-step: formulas → sequents → tree → trace extraction → SCT → `cyclic_thm`. Includes a negative example where SCT correctly rejects a non-strict trace. Read this to understand what's underneath the DSL. |
| `Cyclic/Examples/DSL.lean` | Tour of the `by_cyclic` DSL surface forms via four progressively-richer examples: (1) predicate form on Nat, (2) non-Nat inductive (`List Nat`) via auto-introspection, (3) lex descent across two variables with nested case-splits and labelled ancestors, (4) inline-goal form proving a real inductive theorem (`myAdd n 0 = n`) using `recurse`. |
| `Cyclic/Examples/Advanced.lean` | Cases that exercise paper-faithful machinery: (1) **sum measure** via swap-style recursion (forces the WF fallback), (2) **multi-recursive constructor** (`BinTree.node l r`) with branching back-edges via `branch · … · …`, (3) **Ackermann positivity** (Grotenhuis-Otten Example 4.2) — compound substitution RHS, two back-edges, lex measure synthesised from closure witnesses, (4) **three-position lex** with three back-edges descending on three distinct positions — exercises the per-back-edge attribution of the reset annotation (prog = a0, a1, a2 respectively). |
| `Cyclic/Examples/Arithmetic.lean` | Real arithmetic theorems proved cyclically: `0 + n = n`, `n + m = m + n` (commutativity), `(a + b) + c = a + (b + c)` (associativity), and a `have`-using version of `0 + n = n` showing the Cut step. Plus a small `exists`-using example (`∃ m, m = n`). |
| `Cyclic/Examples/Reorder.lean` | Reorganisation tests: a single-recursive `reorderP_all` written with `cases y` outer (wrong order — SCT requires lex `(x, y)`), and a multi-recursive `btPred_wrong` over `BTr × Nat` that exercises `swapAdjacent` on a multi-rec branch arm. Both reorganise structurally. |
| `Cyclic/Examples/Ackermann.lean` | Ackermann *totality* (`∀ m n, ∃ z, ack m n = z`) in the inline-goal form — uses `exists` for the base witness, `back` with non-trivial `{n := ack (succ m') n'}` substitution for the recursive case, and grouped binders `(m n : Nat)`. The canonical Wehr Fig. 4 demo. |

## Module layout

| File | Purpose |
| --- | --- |
| `Cyclic/SizeChange.lean` | `SCGraph`, composition, canonicalisation, `checkMultiSCT` (Lee-Jones-Ben-Amram POPL 2001). |
| `Cyclic/Extract.lean` | `Pattern` / `Term` / `Equation` AST; `extractAllSCGs`. |
| `Cyclic/Measure.lean` | Measure synthesis cascade: `synthLexOrder` → `synthLexSubset` → `sumMeasureWorks` → `synthLexGreedy`. Closure-witness extraction. (Lee TOPLAS 2009 / Thiemann-Giesl 2003 family.) |
| `Cyclic/Annotation.lean` | Paper-style reset annotation: per-back-edge progressing name from the closure idempotent + global induction order; `treeMatchesOrder` and `canStructural` for the dispatcher. |
| `Cyclic/Reorganize.lean` | Proposition 5.8 (Wehr §3.4 / Sprenger-Dam Th 5): `swapAdjacent`, `bubbleUp`, `reorder` — bubble-sort case-splits to match the induction order, with multi-recursive (`branch`) arms supported via `InnerStructure.{single,branch}`. `retargetBacks` rewires back-edge `anc` labels by descending variable. |
| `Cyclic/Syntax.lean` | The `cyclic_def` command. |
| `Cyclic/ProofTree.lean` | `SubjectTerm` / `Formula` / two-sided `Sequent` / `ProofTree` (with `.haveStep`, `.existsStep`, `.caseSplit`, `.back`, `.node "branch"`); per-occurrence trace extraction (`extractTraceSCGs`, `extractTraceSCGsLabeled`). |
| `Cyclic/Unravel.lean` | Two emitters: `translate` (structural — nested `induction var generalizing rest with`) and `translateWF` (`def + termination_by + WellFounded.fix`). The dispatcher in `ThmCmd` picks per theorem. |
| `Cyclic/ThmCmd.lean` | The `cyclic_thm` command + the shared `runCyclicThmCore` backend with the structural-vs-WF dispatcher (try original tree → reorganise → fall back to WF). |
| `Cyclic/Tactic.lean` | The `by_cyclic` DSL: syntax (`done` / `back` / `cases` / `branch` / `have` / `exists` / labels / `by tac`), walker, elab rules for forms 2 and 3, the `recurse` placeholder tactic. |
| `Cyclic/Example.lean` | `cyclic_def` demos: `swapAdd`, `ack2`, a non-terminating swap rejected at elaboration. |
| `Cyclic/Examples/{Foundations,DSL,Advanced,Arithmetic,Reorder,Ackermann}.lean` | `cyclic_thm` demos, organised by depth (see *Worked examples* above). |
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

Step (4) is loosely modelled on the closure-witness intuition that
recurs in stack-controlled / reset-proof representations of cyclic
proofs (Wehr §3.3–3.4): each idempotent of the SCT closure is a
"cycle witness," and the strict-self-loop positions in that idempotent
are the candidate progressing names. Our greedy synthesis picks among
them. This is *not* Wehr's Theorem 3.2.4 algorithm (which iterates over
SCCs of the bud-companion graph); see *Reset annotation + reorganisation*
below for what we actually compute. Closure witnesses and the synthesised
measure are both surfaced in the `cyclic_thm` info message.

## Reset annotation + reorganisation

After SCT validates, `Cyclic.Annotation` computes a reset-style
annotation: for each back-edge, walk to its closure idempotent, extract
the strict-self-loop positions (the cycle's candidate progressing
names), and choose one consistent with a global induction order built
from the same closure. This is **not** Wehr Theorem 3.2.4 (bud-companion
SCC iteration) — it's a coarser SCT-closure-based heuristic that
coincides with the paper algorithm on stratifiable inputs (everything
we've tested) and may diverge on contrived non-stratifiable cases.

The annotation is surfaced in the diagnostic and threaded into the WF
emitter as a per-back-edge prog map (each recursive call in the WF
output gets a `-- back-edge <lbl>: prog = aN` comment). Example
diagnostic for a three-position lex proof:

```text
induction order: a0 ≻ a1 ≻ a2
back-edges:
  _B1: prog = a0; candidates = {0}; cycle = SCGraph(3 → 3): [0 ->→ 0, 2 -≥→ 2]
  _B3: prog = a1; candidates = {1}; cycle = SCGraph(3 → 3): [0 -≥→ 0, 1 ->→ 1]
  _B4: prog = a2; candidates = {2}; cycle = SCGraph(3 → 3): [0 -≥→ 0, 1 -≥→ 1, 2 ->→ 2]
```

When the user's case-split nesting doesn't match the annotation's
induction order, `Cyclic.Reorganize` performs a *restricted* version of
Sprenger-Dam-style unfolding (FoSSaCS 2003 Theorem 5; Wehr Fact 3.4.1):

1. `bubbleUp v` — recursively swap adjacent levels via `swapAdjacent`
   to bring `v` to the top.
2. `swapAdjacent` extracts each outer arm's `InnerStructure` —
   `.single` (direct case-split on the inner var) or `.branch`
   (multi-recursive `branch` whose every child is a case-split on the
   shared inner var) — and transposes the bodies into a new tree
   where the inner var becomes outer.
3. `retargetBacks` walks the reorganised tree and rewires each
   back-edge's `anc` field to the case-split on its descending variable
   (computed from the annotation's `progPos`). A naive label-remap
   is unsound: a back-edge descending on `x` that originally targeted
   the outer `cases y` must, after the swap, target the new outer
   `cases x`, not the new inner `cases y`. The descending-variable
   retargeting handles this.

Diagnostic when reorganisation kicks in:

```text
emission = structural (nested `induction`, after reorganisation)
```

Bubble-sort handles arbitrary depth; multi-recursive `BinTree.node l r`
arms are reorganised via the `.branch` `InnerStructure`. Trees the
reorganiser can't handle (non-uniform branches, branch children that
aren't case-splits, etc.) fall through to the WF fallback. The full
Sprenger-Dam unfolding allows arbitrary sub-proof duplication; ours
doesn't, hence the "non-uniform → fall through to WF" gap.

## Pretty-print / introspection

`cyclic_thm` introspects the predicate's signature (or each binder's
type for the inline-goal form) via `forallTelescope` +
`Lean.Environment` lookup, then walks each inductive's constructor list
to discover names and recursive-arg positions. No per-type registration:
any inductive already in the environment works.

## Honest limitations

- **Mutual / cross-predicate cycles** aren't supported. The paper
  handles systems of mutually-defined predicates with cycles spanning
  them; we're single-predicate per `cyclic_thm`. (Biggest remaining
  theoretical gap.)
- **Tree-shaped proofs only.** Our `ProofTree` is literally a tree —
  back-edges target ancestors. The paper allows arbitrary DAG cycles
  in the proof graph.
- **Sequent rules that reindex occurrences** (weakening, contraction,
  exchange) break position-based occurrence matching. We work at
  Lean's term-goal level, not in two-sided sequent calculus. (Cut is
  expressible via the `have` step.)
- **`identity`** is currently `assumption` — no real `Γ ∩ Δ ≠ ∅` check.
- **Pattern syntax** in the DSL is restricted: `[]`, `<num>`,
  `x :: xs`, and `<ctor> <var> …`. No nested patterns.
- **Per-call descent witnesses** are delegated to Lean's
  `decreasing_by` machinery rather than emitted explicitly. The paper's
  `avail(a)` witnesses are constructed as proof terms; ours are
  reconstructed by Lean's WF prover. The reset annotation pass
  surfaces *which* position should descend per back-edge (in the
  diagnostic and in `-- prog = aN` comments in WF emission) but the
  Lean-side proof of decrease is still produced by `decreasing_tactic`,
  not constructed from the SCT closure witness directly.
- **Reorganisation** handles uniform 2-level swaps (single- or
  multi-recursive arms) and bubble-sort composition. Non-uniform
  branches — e.g. one arm is a leaf and another is a case-split on a
  different inner variable — fall through to the WF fallback.
- **Sequential back-edges in a single arm** (e.g. Wehr Fig. 4's
  *relational* Ackermann totality, where one back-edge's `∃z'` result
  feeds another back-edge's σ) aren't expressible: the DSL has at most
  one `back` per cyclic_step. Doable via raw Lean tactics inside `by`
  clauses but loses cyclic-proof bookkeeping. A future `useback ⟨pat⟩
  from <σ>` step would close this gap.
- **Richer-than-lex/sum measures** (multiset orderings, polynomial
  measures à la Lee TOPLAS 2009 §5) for SCT-passing graphs that the
  synthesis cascade can't capture. Rare in practice but theoretically
  possible.
- **WF emission of `have` / `exists`** isn't implemented — those steps
  emit a `sorry` placeholder in the WF path. In practice this isn't a
  real limitation because proofs that use `have` / `exists` route
  through structural emission anyway.

The unraveller itself is **not** formally verified. Soundness comes
from Lean's kernel rechecking every emitted declaration; the worst
case of an unraveller bug is a broken build, not an unsound theorem.

## Building

```
lake build           # library + #eval demos + Main executable
lake exe cyclic      # runs Main.lean
```

Uses `leanprover/lean4:v4.29.0`.

## References

The honest algorithmic ancestry:

- **SCT validation** (`SCGraph.checkMultiSCT`): Lee, Jones, Ben-Amram (POPL 2001),
  "The size-change principle for program termination". DOI: `10.1145/360204.360210`.
  Composition closure + idempotent strict-self-loop check.
- **Cyclic proof structure with per-occurrence traces** (`ProofTree`,
  `extractTraceSCGs`): Brotherston (PhD 2006), "Sequent calculus proof systems
  for inductive definitions". Practical implementation precedent: Cyclist
  (Brotherston, Gorogiannis, Petersen 2012, *PLPR*).
- **Measure synthesis from SCT graphs** (`synthLexOrder`, `synthLexSubset`,
  `synthLexGreedy`): in the spirit of Thiemann, Giesl (RTA 2003); fully
  characterised by Lee (TOPLAS 2009), "Ranking functions for size-change
  termination". Our cascade implements the easy quadrant (lex + sum); Lee's
  full characterisation (max/min over lex tuples, polynomial measures) is
  not.
- **Structural translation** (`translate`, nested `induction generalizing`):
  Sprenger, Dam (FoSSaCS 2003), "On the Structure of Inductive Reasoning:
  Circular and Tree-Shaped Proofs in the μ-Calculus". The same pattern
  reappears (with extensions) in Wehr (2025 PhD) ch. 7 (CHA< → HA) and
  in the Grotenhuis-Otten / Leigh-Wehr generalisation to abstract CPS.
- **Tree reorganisation** (`Reorganize.swapAdjacent`, `reorder`):
  Sprenger-Dam Theorem 5 / Wehr Fact 3.4.1, restricted to uniform
  2-level swaps (no sub-proof duplication).
- **Annotation pass** (`Annotation`): a coarse, flat-arity SCT-closure
  reduction of Wehr's stack-controlled / reset-proof annotations
  (§§3.3–3.4). Not Wehr's Theorem 3.2.4 algorithm.
- **Back-edge retargeting by descending variable** (`Reorganize.retargetBacks`):
  not from any paper I've found. Picks each back-edge's new ancestor
  from the annotation's `progPos` after the tree has been reorganised.

**What we *don't* implement** despite reading the paper:

- **Wehr Theorem 3.2.4** (bud-companion SCC algorithm for finding
  induction orders). Our greedy is on SCT closure idempotents instead.
- **Sprenger-Dam Theorem 5 in full** (general unfolding with sub-proof
  duplication). Ours is restricted to uniform 2-level swaps.
- **Grotenhuis-Otten / Leigh-Wehr's abstract-CPS framework**. We work
  directly on a Lean-specific cyclic-proof model, not on their abstract
  Stack/Name/var-annotated representation.
- **Lee 2009's full ranking-function characterisation** (max/min over
  lex tuples; polynomial measures with constants). We only do the easy
  stratifiable quadrant: lex permutations, lex subsets, sum.
- **Berardi-Tatsuta 2017 / Simpson 2017's HA-internal construction** of
  the well-foundedness proof. Lean's kernel handles WF externally; we
  don't reprove it in the object theory.

PDFs in repo root: `cyclicprooftheory.pdf` (Wehr 2025), `2602.12054v1.pdf`
(Grotenhuis-Otten 2026 / Leigh-Wehr 2025), `cyclist.pdf` (Brotherston-
Gorogiannis-Petersen 2012), `1498926.1498928.pdf` (Lee 2009),
`1712.03502v1.pdf` (Berardi-Tatsuta 2017 — measure-based equivalence
result, separate tradition we don't implement).
