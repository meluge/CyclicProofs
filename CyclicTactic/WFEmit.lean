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

/-- The well-founded component for the binder at position `i`. -/
def componentFor (binders : List (String × SortInfo)) (i : Nat) : String :=
  match binders[i]? with
  | none          => "0"
  | some (v, si)  =>
    let ty := si.typeStr
    if ty.startsWith "List" || ty.startsWith "Array" then s!"{v}.length"
    else v

/-- Render a synthesised `Measure` as the right-hand side of
    `termination_by <binders> => <here>`. -/
def measureToTerminationRHS (binders : List (String × SortInfo))
    (m : Measure) : String :=
  match m with
  | .lex order =>
    let comps := order.map (componentFor binders)
    match comps with
    | []     => "0"
    | [c]    => c
    | _      => "(" ++ String.intercalate ", " comps ++ ")"
  | .sum n =>
    let comps := (List.range n).map (componentFor binders)
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

/-- Top-level WF emission. Produces a `def` (not `theorem` — the body
    makes recursive calls) carrying `termination_by` + `decreasing_by`,
    with the measure synthesised by the caller via `SCGraph.synthMeasure`. -/
def translate (defaultSimpPred : Option String) (goalType thmName : String)
    (varSorts : List (String × SortInfo)) (measure : Measure)
    (t : ProofTree) : String :=
  let ctx : WFCtx :=
    { thmName := thmName
      varSorts := varSorts
      defaultSimpPred := defaultSimpPred }
  let bindings := varSorts.map fun (v, si) => "(" ++ v ++ " : " ++ si.typeStr ++ ")"
  let binderNames := String.intercalate " " (varSorts.map (·.1))
  let header := "def " ++ thmName ++ " " ++ String.intercalate " " bindings
                  ++ " : " ++ goalType ++ " := by"
  let body := emitTree ctx 1 t
  let measRHS := measureToTerminationRHS varSorts measure
  -- NB: emit `termination_by <measure>` WITHOUT rebinding the parameters.
  -- For a tactic-style (`:= by`) recursive def, the `xs ys => …` rebind form
  -- raises "N parameters bound in `termination_by`, but the body only binds 0
  -- parameters"; the measure expression uses the signature's binder names
  -- directly, so no rebind is needed. (`binderNames` retained for clarity.)
  let _ := binderNames
  header ++ "\n" ++ body ++ "\n"
    ++ "termination_by " ++ measRHS ++ "\n"
    ++ "decreasing_by\n"
    ++ "  all_goals simp_wf\n"
    ++ "  all_goals omega"

end CyclicTactic.WFEmit
