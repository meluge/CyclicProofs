/-!
# Design document: the tactic-mode cyclic-proof API

This file is a SPEC, not an implementation. None of the tactics referenced
here exist yet — we'll build them. The point is to pin down what we want
the surface to look like before committing to plumbing.

Iterate on this file. Once we agree on the API, we build to match it.

## Design goals (in priority order)

1. **Real Lean InfoView between every step.** When the cursor is between
   two tactics in a cyclic proof, the user sees Lean's actual goal —
   the same kind of `⊢ ...` they see in any other tactic proof. No
   second-class "compile-time info" stand-in.

2. **Cyclic structure stays visible in source.** Back-edges are explicit
   (`back R …`), companions have user-supplied labels. Reading a cyclic
   proof should reveal the proof's cyclic structure, not hide it inside
   `WellFounded.fix` boilerplate.

3. **No IH-binding gymnastics.** The user never writes `ih_n'` or
   `ih_x'`. They write `back R {n := n'}` and the system figures out
   which IH to apply.

4. **SCT validation is automatic.** No `decreasing_by`, no `termination_by`.
   The cyclic system extracts the trace from the back-edges + path and
   runs Wehr 3.2.4 internally.

5. **Standard Lean tactics in between.** `cases`, `simp`, `apply`,
   `rfl`, `show`, `have`, `refine` — all work as normal. The only
   cyclic-specific tactics are `cyclic` (start a cyclic proof) and
   `back` (close a goal via the IH).

## The API surface (proposed)

Two new tactics:

```
cyclic <label>
  -- Mark the current goal as a cyclic-proof companion under `<label>`.
  -- Idiomatic to call this once at the start of the proof. Multiple
  -- `cyclic` calls are allowed for nested companions (mutual cycles)
  -- but most proofs use one.
  --
  -- Internally: snapshots the current sequent and binds an IH
  -- placeholder `ih_<label>` in the local context (visible to the
  -- system, not exposed to the user). The goal itself is unchanged.

back <label> [{ var := term, ... }]
  -- Close the current goal by appealing to companion `<label>`'s IH
  -- under the supplied substitution.
  --
  -- The substitution gives non-default values for companion args.
  -- Args not mentioned in the substitution are inferred from the
  -- current path (whatever `cases`/`simp`/etc. has narrowed them to).
  --
  -- Internally: applies the IH placeholder, records the back-edge
  -- (label, current-sequent, substitution) in the cyclic-proof state.
```

End-of-proof:
- When the theorem is fully discharged, the cyclic system runs
  `extractTraceSCGs` on the recorded back-edges + companions, runs
  multi-SCT, runs Wehr 3.2.4 to find the induction order, and finally
  closes the placeholder `WellFounded.fix` skeleton with the synthesized
  measure.
- If SCT fails: error at the offending `back` (or at `cyclic` if no
  measure exists at all).

---

## Worked examples (the spec)

### Example 1 — `0 + n = n` (simplest single back-edge)

```lean
theorem zeroAddT (n : Nat) : 0 + n = n := by
  cyclic R
  cyc.cases n with
  | zero => rfl
  | succ n' =>
    show Nat.succ (0 + n') = Nat.succ n'
    apply congrArg Nat.succ
    back R {n := n'}
```

Notes:
* `cyclic R` runs at the root sequent `⊢ 0 + n = n`, marks it as the
  companion R. No goal change visible.
* `cyc.cases n with` is the structural-tracking variant of Lean's
  `cases`. Same semantics; additionally records into the cyclic state
  so the finaliser can emit nested `induction` at end-of-proof. v1
  uses `cyc.cases`; v1.5 may intercept plain `cases` transparently.
* In the `zero` arm, goal is `⊢ 0 + 0 = 0`, closed by `rfl`. No back-edge.
* In the `succ n'` arm, goal is `⊢ 0 + Nat.succ n' = Nat.succ n'`.
  After `show ...; apply congrArg Nat.succ`, goal is `⊢ 0 + n' = n'`.
* `back R {n := n'}` closes via R's IH at `n := n'`. Records the
  back-edge: companion R's args were `[n]`, this back-edge's args are
  `[n']`. SCT sees strict descent on position 0.

InfoView at each cursor position shows the actual Lean goal — same as
any other proof.

### Example 2 — Ackermann totality (lex on (m, n))

```lean
theorem ackTotalT (m n : Nat) : ∃ z, ack m n = z := by
  cyclic R
  cyc.cases m with
  | zero =>
    exact ⟨n + 1, by simp [ack]⟩
  | succ m' =>
    cyc.cases n with
    | zero =>
      simp only [ack]
      back R {m := m', n := 1}
    | succ n' =>
      simp only [ack]
      back R {m := m', n := ack (succ m') n'}
```

Notes:
* Two back-edges, both targeting R.
* Wehr 3.2.4 (post-hoc): both back-edges descend on m strictly →
  induction order is just `[m]`. The inner `cases n` is fine — nothing
  about it gets passed to `induction n`; SCT sees through it.
* Substitution syntax `{m := m', n := 1}` matches our existing DSL —
  partial assignments are also OK (`back R {n := 1}` would infer m
  from the `succ m'` cases narrowing).

### Example 3 — multi-recursive constructor (BinTree)

```lean
inductive BTr where | leaf | node : BTr → BTr → BTr

def btPred : BTr → Nat → Prop
  | .leaf, _ => True
  | .node l r, n => btPred l n ∧ btPred r n

theorem btPredT (t : BTr) (n : Nat) : btPred t n := by
  cyclic R
  cyc.cases t with
  | leaf => trivial
  | node l r =>
    refine ⟨?_, ?_⟩
    · back R {t := l}
    · back R {t := r}
```

Notes:
* User wrote `cases t` first (the structurally-recursive var). The
  reorganisation pass we implemented in the data-DSL is *unnecessary*
  here — we let the user write the case-split order they want.
* `refine ⟨?_, ?_⟩` to split the conjunction into two goals — standard
  Lean. Each subgoal closed by `back R` at the appropriate subtree.
* Wehr 3.2.4 picks `t` as induction variable (both back-edges descend
  on it strictly). `n` is preserved (not mentioned in σ, so inherited
  unchanged).

### Example 4 — the `have` (Cut) form

```lean
theorem zeroAddHaveT (n : Nat) : 0 + n = n := by
  cyclic R
  cyc.cases n with
  | zero => rfl
  | succ n' =>
    have hUnfold : 0 + Nat.succ n' = Nat.succ (0 + n') := by rfl
    rw [hUnfold]
    apply congrArg Nat.succ
    back R {n := n'}
```

Notes:
* `have` is *standard Lean*. No special handling — the cyclic system
  doesn't care that you introduced an intermediate hypothesis. It only
  looks at the back-edge's sequent + path.
* This is strictly simpler than our data-DSL where `have` is a
  ProofTree node. Tactic-mode gets it for free.

### Example 5 — `exists` is just `refine ⟨…, ?_⟩` or `exact ⟨…, …⟩`

```lean
theorem existsEqT (n : Nat) : ∃ m, m = n := by
  cyclic R
  cyc.cases n with
  | zero => exact ⟨0, rfl⟩
  | succ n' => exact ⟨Nat.succ n', rfl⟩
```

Notes:
* No `exists` tactic needed. Standard Lean `exact ⟨w, …⟩` handles ∃R.
  Same for `refine ⟨w, ?_⟩` if you want to defer the body.
* This shrinks the surface area: the data-DSL needed dedicated
  `cycExists` syntax; tactic mode gets it from Lean's existing tools.

### Example 6 — companion at a non-root position (nested cyclic)

```lean
-- DEFERRED to v2.
theorem nested (m n : Nat) : someP m n := by
  cyclic R
  cyc.cases m with
  | zero => trivial
  | succ m' =>
    cyclic S            -- inner companion at this point
    cyc.cases n with
    | zero => back R {m := m'}
    | succ n' => back S {n := n'}
```

Question to settle: do we allow nested `cyclic` for distinct
companions, or restrict to one companion per theorem? The data-DSL
allows multiple via labeled case-splits (`R: cases m with ...`); the
tactic version could too via nested `cyclic` calls.

Trade-off:
* Nested companions: more expressive but more bookkeeping.
* Single companion: simpler, covers everything our examples need so far.

Recommendation for v1: single companion. Add nested in v2 if needed.

---

## Implementation outline

### Tactics

`cyclic <label>` (the entry point):
1. Snapshot the current goal as the companion sequent for `<label>`.
2. Initialise side-channel cyclic state: `companions := [(label, sequent)]`,
   `currentPath := []`, `tree := <root pending>`.
3. *Interactive layer*: rewrite the goal as `WellFounded.fix ?measure ?wf
   (fun args ih => ?proof) <bound args>` with mvars for measure and
   well-foundedness. Set the goal to `?proof`, with `ih` in scope under
   a hidden binding name; record `<label> → ih_name`.

`cyc.cases <var> with | <pat> => <tac> | …` (structural case-split):
1. Standard `cases <var>` semantics for the interactive layer.
2. *Recording*: push a `.caseSplit` node into the tree at the current
   path; for each arm, recurse into the sub-tactic with the path
   extended.

   We use `cyc.cases` (and not standard `cases`) for v1 because
   intercepting standard `cases` reliably needs us to walk Lean's
   `TacticInfo` post-hoc — doable but more code. v1.5 can add the
   intercept and rename `cyc.cases` away.

`back <label> [{σ}]`:
1. Look up companion's sequent + `ih` binding.
2. Reconstruct path-inferred σ by reading the current goal's predicate
   args against the companion's; merge with user-supplied σ.
3. *Interactive layer*: `apply ih @σ` (or equivalent) to close the goal.
4. *Recording*: push a `.back` node into the tree at the current path.

`have`, `simp`, `apply`, `rfl`, `refine`, `show`, etc. — all standard
Lean. They're not recorded at all. Their effect is captured implicitly
via the goal state at the next recorded tactic (`cyc.cases` or `back`).

### End-of-proof finalisation

When the cyclic block exits (or the theorem is fully discharged), the
finalizer runs:

1. **Validate the recorded tree.** Run `extractTraceSCGs` (existing
   code in `CyclicTactic.ProofTree`). Run `checkMultiSCT`. Run
   `findInductionOrder` (Wehr 3.2.4).
2. **Decide emission path.** If the case-split tree's variable
   ordering matches the discovered induction order (or can be
   reorganised via `Reorganize.reorder` to match), emit *structurally*.
   Otherwise emit via `WellFounded.fix`.
3. **Emit the actual proof.**
   * **Structural path**: discard the interactive proof entirely.
     Replace with `Cyclic.Unravel.translate` output. The user wrote
     a tactic-mode proof, but the kernel sees a normal nested-
     `induction` proof.
   * **WF path**: keep the interactive `WellFounded.fix` proof.
     Resolve `?measure` with the synthesized lex/sum measure;
     discharge `?wf` automatically.
4. **Surface diagnostics** via `logInfoAt` at the `cyclic R` position
   (same content as today's `cyclic_thm` info block).

### Why "discard the interactive proof" works

The interactive proof and the re-emitted structural proof prove the
same theorem (modulo well-foundedness, which both ultimately appeal
to). It's safe to discard one in favour of the other at the end.

This is similar to how some Lean tactics elaborate to a placeholder
during execution and replace with the real proof at completion.

### Architectural note

Almost all of the "build to" code already exists in `CyclicTactic.*`:
* `ProofTree.lean` — proof tree data + trace extraction
* `SizeChange.lean`, `Measure.lean`, `InductionOrder.lean` — SCT + Wehr
* `Annotation.lean` — reset annotation
* `Reorganize.lean` — structural-shape adjustment
* `Unravel.lean` — structural emission + WF emission

The new code is just the *tactic frontend* that builds the proof tree
from interactive use rather than parsing it from a DSL. Roughly
~300-500 lines of tactic plumbing + finalizer.

---

## Resolved questions (from design review)

1. **Goal-shape capture at `back` time.** Capture the entire goal
   expression. Single-predicate is the easy case; richer goals (∃, ∧,
   etc.) are stored as-is and the SCT trace analysis works on whatever
   structure they have. Iterate on the analysis after we have a working
   v1.

2. **Path-inferred args.** Read the local context at the back-edge:
   compare the predicate's arg slots to the current goal expression vs.
   the companion's; whatever differs and isn't in the user-supplied σ
   is path-inferred from the case-split narrowings.

3. **Structural emission stays.** End of proof should re-emit as
   nested `induction` when possible (i.e. when Wehr 3.2.4 finds a lex
   order *and* the case-split nesting can be lined up via reorganisation).
   Falls back to `WellFounded.fix` only when structural is impossible
   (sum/swap measures, non-uniform tree shapes). This preserves the
   "reads like a Lean inductive proof" property of the data-DSL.

   **Architecturally**, this means the implementation has *two* layers:

     * **Interactive layer** — the user's tactics close the goal in
       real time via a `WellFounded.fix` skeleton (so the InfoView
       shows real goals). This proof is *throwaway*.
     * **Recorded layer** — every cyclic-relevant tactic (`cyclic`,
       `back`, structural `cases`) records into a side-channel
       `ProofTree`-like structure as it fires.
     * **End-of-proof finalisation** — discards the interactive
       proof, runs SCT + Wehr + reorganisation on the recorded
       structure, and re-emits via the existing `Unravel.translate`
       (structural) or `Unravel.translateWF` (WF fallback).

   The user sees: real goals during writing + a structural-induction
   final form. Cost: every cyclic-aware tactic does double duty
   (close-the-goal AND record-into-tree).

4. **Single companion (`cyclic R`) for v1.** Nested companions deferred
   to v2 if needed.

5. **SCT diagnostic placement: not worrying about it yet.** Default
   for v1: same `logInfoAt` block we emit today, fired at the
   `cyclic R` position. Trivial to move later.

---

## What stays from the data-DSL theory

Per decision #3 (structural emission stays), almost the entire existing
machinery is reused as-is:

* `SizeChange.lean` — SCT machinery
* `Measure.lean` — measure synthesis
* `InductionOrder.lean` — Wehr 3.2.4
* `Annotation.lean` — reset annotation
* `Reorganize.lean` — proof-tree restructuring (still needed because
  the user's case-split order may not match the discovered induction
  order; the finaliser reorganises before structural emission)
* `Unravel.lean` — both structural and WF emission paths
* `ProofTree.lean` — the data type the tactics build into

What's NEW (the v1 build):

* `Tactic.lean` (~300-500 lines) — the three new tactics (`cyclic`,
  `cyc.cases`, `back`), cyclic-state monad, finalizer.

That's it. No changes to the theoretical layer. The existing modules
were always agnostic to *how* the ProofTree was constructed — the data-
DSL parsed it, the tactic-mode will build it interactively.

---

## Status

### v0.1 (DONE)

Initial scaffold in `CyclicTactic/Tactic.lean` + smoke test in
`CyclicTactic/Examples/Smoke.lean`.

Surface tactics declared:
  * `cyclic <label>` — records current goal as companion in IO.Ref.
  * `back <label>` — looks up companion, records back-edge, closes
    the goal with `sorry`.
  * `cyc_state` — debug tactic, dumps recorded state.

What works:
  * Tactics elaborate. The smoke-test `theorem zeroAddT` builds (with
    a `sorry` warning).
  * **Real Lean InfoView between tactics** — the whole point. Hover
    on any line of the proof; the InfoView shows actual `⊢ 0 + n = n`,
    `⊢ Nat.succ (0 + n') = Nat.succ n'`, etc. Same as any normal Lean
    proof.
  * `[cyclic]` and `[back]` diagnostic messages fire at the right
    positions.

Known v0.1 limitations (all addressed in v0.2):
  * **Proofs are sorry-laden.** `back` closes via `sorry`; no real
    proof is produced.
  * **No σ syntax.** `back R` doesn't accept `{n := n'}` yet.
  * **No `cyc.cases`.** Standard Lean `cases` works for the
    interactive layer but doesn't get recorded for the finalizer.
  * **State management via global IO.Ref.** Survives within a
    declaration but doesn't survive Lean's incremental-elaboration
    boundaries. LSP diagnostics show partial state visible from
    later declarations. Needs to move to a `TacticM` state extension
    (or a custom `MonadState`-extending wrapper).
  * **No finalizer.** No SCT validation runs. No structural emission.

### v0.2 plan

1. **State-extension refactor.** Replace `IO.Ref` with a proper
   `TacticM` state extension. The state lives for the duration of
   the `by_cyclic do` block (which we'll add) and is cleared at
   block exit.

2. **`by_cyclic do <tactics>` block.** This is the boundary where:
   * State gets initialised at entry.
   * Finalizer runs at exit.
   * The `WellFounded.fix` skeleton is set up so `back` can use a
     real IH instead of sorry.

3. **`back R {σ}` syntax.** Add the substitution argument; integrate
   path-inferred values from local context; have `back` apply the
   actual IH (no more sorry).

4. **`cyc.cases x with …` tactic.** Wrap Lean's `Cases` tactic; record
   `.caseSplit` into the proof tree. Probably ~50 lines.

5. **Finalizer.** At end of `by_cyclic do` block:
   * Build a `ProofTree` from the recorded back-edges + case-splits.
   * Run `extractTraceSCGs` → `checkMultiSCT` → `findInductionOrder`.
   * If structural emission feasible: discard the WF.fix interactive
     proof, replace with `Cyclic.Unravel.translate` output.
   * Else: keep WF.fix; resolve the measure mvar; discharge wf mvar.
   * Surface diagnostics via `logInfoAt` at the `by_cyclic` position.

6. **Port the rest of the smoke tests:** Ackermann, btPred, have,
   exists.

Estimated effort: v0.2 is ~1 week of careful tactic-plumbing work.
-/
