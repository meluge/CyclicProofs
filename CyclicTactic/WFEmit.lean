import CyclicTactic.ProofTree
import CyclicTactic.EmitCommon
import CyclicTactic.Measure

/-!
# Well-founded (WF) emission backend

The §6 structural emitter (`CyclicTactic.Theorem6.Emit`) emits proofs as
`theorem … := by induction …`, which only captures recursion that
descends on a SINGLE fixed argument position. Some cyclic proofs are
sound by a *lexicographic* / *sum* termination order that no single
position witnesses — the motivating example is merge-sort's `merge`,
which descends on `xs` when `x ≤ y` and on `ys` otherwise, so neither
argument decreases across both `by_cases` arms.

For those proofs this module emits a kernel-checked

    def <name> <binders> : <goal> := by <body>
    termination_by <binders> => <measure>
    decreasing_by all_goals simp_wf; all_goals omega

where `<measure>` is synthesised from the per-back-edge size-change
graphs via `SCGraph.synthMeasure` (`Measure.lean`). The body walker
mirrors `Theorem6.Emit.emitMutualTree`: case-splits emit as plain
`cases` / `by_cases` (NO sprout-driven `induction` — termination is
delegated to `termination_by`), and each bud emits a genuine recursive
call `<name> <σ-applied args>`. Lean's well-founded recursion check then
verifies the measure decreases on every recursive call.

This is the WF analogue of `Theorem6.Emit.translate`; the dispatcher in
`CyclicTactic.Tactic` chooses between the two based on whether a single
structural induction order exists (`CyclicTactic.canStructural`).
-/

namespace CyclicTactic.WFEmit

open CyclicTactic.Proof
open CyclicTactic.EmitCommon  -- pad, reindent, defaultSimp, termToLean, SortInfo

/-! ### Measure rendering

`SCGraph.synthMeasure` returns a `Measure` over argument *positions*
(`Nat`). For `termination_by` we render it over the actual binder names,
mapping each position to a well-founded component:

  * a `List …` binder at position `i` contributes `<binderᵢ>.length`;
  * a `Nat` binder contributes `<binderᵢ>` directly;
  * any other sort falls back to `<binderᵢ>` (best-effort; `simp_wf`
    + `omega` in `decreasing_by` handle the arithmetic).

`Measure.lex order` renders as a tuple `(c₀, c₁, …)` (Lean reads tuples
lexicographically in `termination_by`); a singleton renders bare.
`Measure.sum n` renders as `c₀ + c₁ + … + c_{n-1}`. -/

/-- A per-position phase-rank map: `pos ↦ (ctorName ↦ rank)`, produced by the
    phase-order solver (`Phase.phaseAugment`). A position present here is a
    finite-domain "phase" argument whose measure component is the RANK of its
    current constructor, not the binder itself. -/
abbrev PhaseRanks := List (Nat × List (String × Nat))

/-- The well-founded component for the binder at position `i`.

    A `phaseRanks` entry at `i` overrides the default: the component becomes a
    `match` on the binder mapping each constructor to its solved rank — turning
    a finite-domain (Bool/enum) phase argument into a `Nat` that strictly
    decreases as the cycle drives the phase down its order. This is the GAP-2
    rendering; positions absent from `phaseRanks` behave exactly as before. -/
def componentFor (binders : List (String × SortInfo)) (phaseRanks : PhaseRanks)
    (i : Nat) : String :=
  match phaseRanks.find? (·.1 == i) with
  | some (_, ranks) =>
    match binders[i]? with
    | none         => "0"
    | some (v, si)  =>
      -- Rank every constructor of the binder's finite type: solved ctors get
      -- their phase rank; the rest get 0 (they never occur on a back-edge, so
      -- the rank is irrelevant for the decrease). Enumerating ALL ctors keeps
      -- the `match` total WITHOUT a `| _ => 0` catch-all — Lean 4.29 rejects a
      -- redundant catch-all on a complete match (e.g. both `Bool` cases given).
      -- Patterns use the FULLY-QUALIFIED ctor name (`Tri.a`, not `a`): a bare
      -- lowercase ctor name parses as a variable (catch-all) pattern, which
      -- silently swallows the match and makes the later arms "redundant".
      -- Ranks are keyed by short name (how the phase solver records them).
      let rankOf := fun c => (ranks.find? (·.1 == c)).map (·.2) |>.getD 0
      if si.ctors.isEmpty then
        let arms := ranks.map (fun (c, r) => s!"| {c} => {r}")
        "(match " ++ v ++ " with " ++ String.intercalate " " arms ++ " | _ => 0)"
      else
        let arms := si.ctors.map (fun ci => s!"| {ci.fullName} => {rankOf ci.shortName}")
        "(match " ++ v ++ " with " ++ String.intercalate " " arms ++ ")"
  | none =>
    match binders[i]? with
    | none          => "0"
    | some (v, si)  =>
      let ty := si.typeStr
      if ty.startsWith "List" || ty.startsWith "Array" then s!"{v}.length"
      else v

/-- Render a synthesised `Measure` as the right-hand side of
    `termination_by <binders> => <here>`. `phaseRanks` (default empty) overrides
    finite-domain positions with their solved phase rank — see `componentFor`. -/
def measureToTerminationRHS (binders : List (String × SortInfo))
    (m : Measure) (phaseRanks : PhaseRanks := []) : String :=
  match m with
  | .lex order =>
    let comps := order.map (componentFor binders phaseRanks)
    match comps with
    | []     => "0"
    | [c]    => c
    | _      => "(" ++ String.intercalate ", " comps ++ ")"
  | .sum n =>
    let comps := (List.range n).map (componentFor binders phaseRanks)
    match comps with
    | []  => "0"
    | _   => String.intercalate " + " comps

/-! ### Body walker

Mirrors `Theorem6.Emit.emitMutualTree`: no sprout/IH machinery, all
case-splits emit as `cases`, and `.back` emits a recursive self-call. -/

structure WFCtx where
  thmName : String
  varSorts : List (String × SortInfo)
  defaultSimpPred : Option String

/-- Header for a `cases` arm (constructor + bound vars, no IH binders). -/
def patToCasesHeader (sortInfo : SortInfo) (pat : SubjectTerm) : Option String :=
  match pat with
  | .ctor cname patArgs =>
    match sortInfo.ctors.find? (·.shortName == cname) with
    | none => none
    | some ci =>
      let argVars := patArgs.filterMap fun
        | .var n => some n
        | _      => none
      if argVars.length != patArgs.length || argVars.length != ci.totalArgs then none
      else
        let argsStr :=
          if argVars.isEmpty then ""
          else " " ++ String.intercalate " " argVars
        some (ci.shortName ++ argsStr)
  | _ => none

/-- The recursive self-call expression `<thmName> <σ-applied args>` for a
    bud, read positionally from the bud sequent. -/
def backCallExpr (ctx : WFCtx) (bSeq : Sequent) : String :=
  let sorts := ctx.varSorts.map (·.2)
  let argTerms := bSeq.succedents.flatMap (·.args)
  let argsStr := argTerms.map (termToLean sorts)
  ctx.thmName ++ (if argsStr.isEmpty then "" else " " ++ String.intercalate " " argsStr)

/-- The closing tactic block for a bud: bind the IH via the recursive
    call, then normalise both IH and goal and discharge the residual
    `+1`/length arithmetic with `omega` — exactly the gap the hand proof
    never closed. Returned as a list of lines (the caller indents them). -/
def backCloseLines (ctx : WFCtx) (bSeq : Sequent) : List String :=
  let call := backCallExpr ctx bSeq
  -- `simp_all` often closes the goal outright (it rewrites the goal by the
  -- IH and the arithmetic falls out); `omega` would then error "no goals".
  -- `<;> omega` discharges any residual `+1`/length arithmetic when goals
  -- remain and is a no-op when none do — so the close is robust either way.
  [ "have ih := " ++ call,
    "simp_all [Nat.add_comm, Nat.add_left_comm] <;> omega" ]

/-- Indent each line of a list to `depth`, joining with newlines. -/
def linesAt (depth : Nat) (ls : List String) : String :=
  String.intercalate "\n" (ls.map fun l => pad depth ++ l)

/-- Whether a (trimmed) source line is the bud's recursive marker — the
    user's `back R {…}` or the internal `recurse` placeholder — which the
    WF emitter replaces with a genuine recursive call. -/
def isBackLine (l : String) : Bool :=
  let t := l.trimAscii.toString
  t.startsWith "back " || t == "back" || t == "recurse"

partial def emitTree (ctx : WFCtx) (depth : Nat) : ProofTree → String
  | .leaf _ _ _ closeTac =>
    let body := closeTac.getD (defaultSimp ctx.defaultSimpPred)
    pad depth ++ reindent depth body
  | .identity _ _ =>
    pad depth ++ "assumption"
  | .node _ _ rule children =>
    if rule == "branch" then
      let prelude := defaultSimp ctx.defaultSimpPred
      let qmarks := String.intercalate ", " (children.map (fun _ => "?_"))
      let bodies := children.map fun child =>
        let inner := emitTree ctx (depth + 1) child
        pad depth ++ "·\n" ++ inner
      pad depth ++ prelude ++ "\n"
        ++ pad depth ++ "refine ⟨" ++ qmarks ++ "⟩\n"
        ++ String.intercalate "\n" bodies
    else
      pad depth ++ defaultSimp ctx.defaultSimpPred ++ "\n"
        ++ String.intercalate "\n" (children.map (emitTree ctx depth))
  | .caseSplit _ _ var arms =>
    let sortInfo? := ctx.varSorts.lookup var
    let armsBody : List String := arms.filterMap fun (pat, sub) =>
      match sortInfo? with
      | none => some (pad depth ++ "| _ => sorry /- no sort info for '"
                       ++ var ++ "' -/")
      | some sortInfo =>
        match patToCasesHeader sortInfo pat with
        | none => none
        | some header =>
          let body := emitTree ctx (depth + 1) sub
          some (pad depth ++ "| " ++ header ++ " =>\n" ++ body)
    pad depth ++ "cases " ++ var ++ " with\n"
      ++ String.intercalate "\n" armsBody
  | .dCaseSplit _ _ hyp prop pos neg =>
    -- Decidable split → well-formed `by_cases h : P` with `·` bullets,
    -- each arm body indented at `depth + 1` (fixes the baseline dedent).
    let posBody := emitTree ctx (depth + 1) pos
    let negBody := emitTree ctx (depth + 1) neg
    pad depth ++ "by_cases " ++ hyp ++ " : " ++ prop ++ "\n"
      ++ pad depth ++ "·\n" ++ posBody ++ "\n"
      ++ pad depth ++ "·\n" ++ negBody
  | .back _ bSeq _ _ closeTac =>
    -- Prelude = the user's arm body (e.g. `simp [merge, hle]`) with the
    -- `back R {…}` / `recurse` marker line dropped; then the recursive
    -- call + arithmetic close. Each line is reindented to `depth` so the
    -- emitted bullet body is well-formed (the §6 path's `reindent` flattens
    -- multi-line bodies, which broke `by_cases` arms — we keep per-line
    -- indentation here).
    let preludeLines : List String :=
      match closeTac with
      | none     => []
      | some tac =>
        (tac.splitOn "\n").filterMap fun l =>
          let t := l.trimAscii.toString
          if t == "" || isBackLine l then none else some t
    linesAt depth (preludeLines ++ backCloseLines ctx bSeq)
  | .haveStep _ _ haveName haveTypeStr haveProofStr cont =>
    pad depth ++ "have " ++ haveName ++ " : " ++ haveTypeStr ++ " := by\n"
      ++ pad (depth + 1) ++ reindent (depth + 1) haveProofStr ++ "\n"
      ++ emitTree ctx depth cont
  | .existsStep _ _ witnessStr cont =>
    pad depth ++ "refine ⟨" ++ witnessStr ++ ", ?_⟩\n"
      ++ emitTree ctx depth cont

/-- The `decreasing_by` tactic for a synthesised measure, chosen by the
    measure's SHAPE rather than a fixed string.

    `simp_wf` first unfolds the `WellFounded`/`invImage` wrapper to expose the
    raw order goal. Then the goal's shape depends on the measure:

      * `.sum n`  → the goal is linear `Nat` arithmetic (`a + b < c + d`), which
        `omega` discharges directly.
      * `.lex order` (rendered as a tuple) → the goal is `Prod.Lex … (…) (…)`.
        `omega` does NOT understand `Prod.Lex`; `simp [Prod.lex_def]` rewrites it
        to the disjunction `a < a' ∨ (a = a' ∧ …)` and closes the trivially-true
        disjuncts, with `omega` mopping up any residual arithmetic. (Observed:
        for a size-preserving lex step the goal reduces to `n < n ∨ True ∧ 0 < 1`,
        which `omega` alone rejects but `simp [Prod.lex_def]` proves.)

    We wrap both in `first | … | …` so a single emitted block is robust whether
    the measure is sum-like or lex-like, and so a lex goal that happens to be
    closable by `omega` alone (singleton lex = bare `Nat`) still goes through.
    This replaces the previous fixed `simp_wf; omega`, which silently failed on
    `Prod.Lex` goals and forced those proofs into the recursive fallback.

    When the measure has PHASE components (rendered as `match <binder> with …`),
    the order goal contains those matches; `omega` can't evaluate a `match`, so
    we add `simp` (which reduces the `match` on a constructor literal after the
    relevant `cases`/`by_cases` has fixed the binder) before the arithmetic.
    `hasPhase` toggles that in. -/
def decreasingByFor (measure : Measure) (hasPhase : Bool := false) : String :=
  let phaseSimp := if hasPhase then "  all_goals (try simp_all)\n" else ""
  let arith :=
    match measure with
    | .sum _   => "  all_goals (first | omega | simp_all [Prod.lex_def] <;> omega)"
    | .lex _   => "  all_goals (first | simp_all [Prod.lex_def] <;> omega | omega)"
  "decreasing_by\n  all_goals simp_wf\n" ++ phaseSimp ++ arith

/-- Top-level WF emission. Produces a `def` (not `theorem` — the body
    makes recursive calls) carrying `termination_by` + `decreasing_by`,
    with the measure synthesised by the caller via `SCGraph.synthMeasure`.
    The `decreasing_by` block is chosen by the measure's shape — see
    `decreasingByFor`. -/
def translate (defaultSimpPred : Option String) (goalType thmName : String)
    (varSorts : List (String × SortInfo)) (measure : Measure)
    (t : ProofTree) (phaseRanks : PhaseRanks := []) : String :=
  let ctx : WFCtx :=
    { thmName := thmName
      varSorts := varSorts
      defaultSimpPred := defaultSimpPred }
  let bindings := varSorts.map fun (v, si) => "(" ++ v ++ " : " ++ si.typeStr ++ ")"
  let binderNames := String.intercalate " " (varSorts.map (·.1))
  let header := "def " ++ thmName ++ " " ++ String.intercalate " " bindings
                  ++ " : " ++ goalType ++ " := by"
  let body := emitTree ctx 1 t
  let measRHS := measureToTerminationRHS varSorts measure phaseRanks
  -- NB: emit `termination_by <measure>` WITHOUT rebinding the parameters.
  -- For a tactic-style (`:= by`) recursive def, the `xs ys => …` rebind form
  -- raises "N parameters bound in `termination_by`, but the body only binds 0
  -- parameters"; the measure expression uses the signature's binder names
  -- directly, so no rebind is needed. (`binderNames` retained for clarity.)
  let _ := binderNames
  header ++ "\n" ++ body ++ "\n"
    ++ "termination_by " ++ measRHS ++ "\n"
    ++ decreasingByFor measure (hasPhase := !phaseRanks.isEmpty)

/-- Emit the SAME `def` body but with NO `termination_by` / `decreasing_by`,
    letting Lean's own structural / `GuessLex` termination inference find a
    measure. Used as an additive fallback rung: when our synthesised-measure
    emission fails to commit, this catches the cases Lean can infer on its own
    (verified: `merge_length` terminates with no clause at all — Lean infers
    the lexicographic measure and discharges it). It never HIDES synthesis:
    the dispatcher tries the explicit-measure script first (so the synthesised
    measure stays the visible artifact when it works) and only falls here when
    that fails — strictly more proofs go through, none regress. -/
def translateNoMeasure (defaultSimpPred : Option String) (goalType thmName : String)
    (varSorts : List (String × SortInfo)) (t : ProofTree) : String :=
  let ctx : WFCtx :=
    { thmName := thmName
      varSorts := varSorts
      defaultSimpPred := defaultSimpPred }
  let bindings := varSorts.map fun (v, si) => "(" ++ v ++ " : " ++ si.typeStr ++ ")"
  let header := "def " ++ thmName ++ " " ++ String.intercalate " " bindings
                  ++ " : " ++ goalType ++ " := by"
  let body := emitTree ctx 1 t
  header ++ "\n" ++ body

end CyclicTactic.WFEmit
