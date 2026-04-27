import CyclicTactic.ProofTree
import CyclicTactic.Measure

/-!
# Stage 3: unravelling a validated cyclic proof into a Lean tactic script

Two emission paths, both producing standalone Lean 4 theorems:

  * **Structural emission** (`translate`, below): nested `induction`
    blocks, one per ordered case-split variable. Follows the
    Sprenger-Dam structural-translation tradition (Sprenger & Dam,
    "On the Structure of Inductive Reasoning: Circular and Tree-Shaped
    Proofs in the μ-Calculus", FoSSaCS 2003 — Theorem 5: every cyclic
    μ-calculus proof can be unfolded into a tree-shaped proof using
    well-founded induction on the trace's progressing position). Our
    setting is restricted (sequent calculus over a single inductive
    predicate, no μ-binders), so the unfolding is concrete syntax
    emission rather than a meta-theorem.
  * **WF emission** (`translateWF`, below): produces a `def … :=`
    plus `termination_by <measure>`, deferring to Lean's
    `WellFounded.fix`. This is the unravelling Wehr 2025 PhD thesis
    Ch. 6 describes for CHA into HA: the cyclic proof becomes a
    recursive function whose termination is justified by the SCT-
    derived measure.

Surface form details below.

Consumes a `ProofTree` (plus per-argument sort info introspected from the
Lean side) and emits a Lean 4 theorem (as a `String`) that proves the
sequent by well-founded induction on the case-split variables.

Handled in this stage:

  * Root and nested `.caseSplit` over arbitrary single-recursive inductive
    types (Nat.zero/succ, List.nil/cons, etc.). Each case-split emits an
    `induction v with …` block keyed on the constructors of v's sort.
  * `.leaf` → `simp [<leanPred>]`.
  * `.node` with a single child → `simp [<leanPred>]` then recurse into
    the child (typical shape: unfold + back-edge).
  * `.back` → `exact ih_<v> <σ args>`, with the IH looked up by ancestor
    label in the `IHInfo` context.
  * `.identity` → `assumption`.

Out of scope (Phase 4+): multi-recursive constructors (e.g. `Tree.node l r`
which yields two IHs), weakening/contraction, cross-predicate back-edges.

## Sort info

Sort info is *introspected* from the Lean environment by `CyclicTactic.ThmCmd`
and passed in as `List SortInfo` (one per root-sequent variable, in
positional order matching the predicate's argument list). The translator
itself doesn't know about Lean's environment — it just consumes the
pre-computed sort table.

## Lex descent via nested induction

A back-edge whose trace graph encodes lex descent is discharged by
nesting a second `induction` inside the outer `succ`/`cons`/… arm. This
gives lex-style termination for free — Lean's kernel re-checks the nested
inductions and the SCT condition (Lee-Jones-Ben-Amram POPL 2001) plus
the lex-order witness from `CyclicTactic.Annotation` guarantee they're
well-founded. The Sprenger-Dam Theorem 5 unfolding is what justifies
that this nested-`induction` *exists* for any SCT-validated cyclic proof
with a lex measure; emitting it as concrete syntax and the IH-binding
plumbing (`IHInfo`, `ihCall`, `pathSubst`) below are original.
-/

namespace CyclicTactic.Unravel

open CyclicTactic.Proof

/-! ### Sort info (populated by `CyclicTactic.ThmCmd` at elaboration time) -/

/-- Info about one constructor of an inductive type used by the proof. -/
structure CtorInfo where
  /-- Last name component, e.g. "zero", "succ", "nil", "cons". -/
  shortName : String
  /-- Fully qualified name for emission, e.g. "Nat.zero", "List.cons". -/
  fullName : String
  /-- Positions (0-based) of the recursive arguments. Each recursive
      argument generates one induction hypothesis. -/
  recArgs : List Nat
  /-- Total number of value arguments (recursive + non-recursive). -/
  totalArgs : Nat
  deriving Repr, Inhabited

/-- Info about an inductive type that's the sort of one predicate arg. -/
structure SortInfo where
  /-- Pretty-printed type for emission in `(x : T)` annotations,
      e.g. "Nat", "List Nat". -/
  typeStr : String
  /-- Constructors, in declaration order. -/
  ctors : List CtorInfo
  deriving Repr, Inhabited

/-! ### Subject-term rendering -/

/-- Look up a constructor in a list of sorts by short name (first match wins). -/
def findCtor (sorts : List SortInfo) (name : String) : Option CtorInfo :=
  (sorts.flatMap (·.ctors)).find? (·.shortName == name)

/-- Render a `SubjectTerm` as Lean 4 surface syntax. Special-cases Nat
    literals for readability; otherwise uses `CtorInfo.fullName`. -/
partial def termToLean (sorts : List SortInfo) : SubjectTerm → String
  | .var n                  => n
  | .ctor "zero" []         => "0"
  | .ctor "succ" [t]        => "(Nat.succ " ++ termToLean sorts t ++ ")"
  | .ctor name args         =>
    let renderedArgs := args.map (termToLean sorts)
    let head :=
      match findCtor sorts name with
      | some ci => ci.fullName
      | none    => name  -- best-effort fallback
    if renderedArgs.isEmpty then head
    else "(" ++ head ++ " " ++ String.intercalate " " renderedArgs ++ ")"

partial def termVars : SubjectTerm → List String
  | .var n       => [n]
  | .ctor _ args => args.flatMap termVars

partial def dedupVars : List String → List String
  | []      => []
  | x :: xs => x :: dedupVars (xs.filter (· != x))

def sequentVars (s : Sequent) : List String :=
  let a := s.antecedents.flatMap (·.args.flatMap termVars)
  let b := s.succedents.flatMap (·.args.flatMap termVars)
  dedupVars (a ++ b)

/-! ### Induction-case header generation

For a SubjectTerm pattern like `.ctor "succ" [.var "x'"]`, look up the
constructor in the case-split var's sort and produce:

  * the case header string (e.g. `"succ x'"` for non-recursive ctors,
    `"succ x' ih_x'"` for single-rec, `"node l r ih_l ih_r"` for
    multi-rec),
  * the list of `(recArgVar, ihName)` pairs the case binds.

Each recursive constructor arg generates one IH, named after the
subterm variable: `ih_<recArgVarName>`. So for `cases t with | node l r => …`,
we bind `ih_l : P l` and `ih_r : P r`. Back-edges select the correct
IH based on which subterm `σ` targets.
-/
def patToInductionCase (sortInfo : SortInfo) (pat : SubjectTerm)
    : Option (String × List (String × String)) :=
  match pat with
  | .ctor name patArgs =>
    match sortInfo.ctors.find? (·.shortName == name) with
    | none => none
    | some ci =>
      -- Each pattern arg must be a bare variable (no nested patterns).
      let argVars := patArgs.filterMap fun
        | .var n => some n
        | _      => none
      if argVars.length != patArgs.length || argVars.length != ci.totalArgs then none
      else
        -- Build (recArgVar, ihName) for each recursive constructor arg.
        let ihEntries : List (String × String) :=
          ci.recArgs.filterMap fun i =>
            argVars[i]?.map fun v => (v, "ih_" ++ v)
        let argsStr :=
          if argVars.isEmpty then ""
          else " " ++ String.intercalate " " argVars
        let ihStr :=
          if ihEntries.isEmpty then ""
          else " " ++ String.intercalate " " (ihEntries.map (·.2))
        let header := ci.shortName ++ argsStr ++ ihStr
        some (header, ihEntries)
  | _ => none

/-! ### IH context

Each in-scope case-split's induction hypotheses. A multi-recursive
constructor (e.g. `Tree.node l r`) binds two IHs (`ih_l`, `ih_r`); a
single-recursive constructor (e.g. `Nat.succ x'`) binds one (`ih_x'`).
A back-edge picks the right IH by looking at `σ`'s image of the
case-split's induction variable and matching it against the recursive
subterm vars. -/
structure IHInfo where
  /-- Label of the case-split this IH set comes from. -/
  anc : String
  /-- The variable the case-split inducts on (e.g. `t` for `cases t with`).
      Back-edges look up `σ(caseSplitVar)` to pick which IH to apply. -/
  caseSplitVar : String
  /-- One entry per recursive subterm var: (subtermVarName, ihBindingName). -/
  ihs : List (String × String)
  /-- The vars the IH was generalised over, in order — back-edges supply
      σ-images for them. -/
  genVars : List String
  deriving Inhabited

/-- `n` levels of two-space indentation. -/
def pad (n : Nat) : String := String.ofList (List.replicate (n * 2) ' ')

/-- Re-indent a multi-line tactic block to `depth`. Strips each line's
    leading whitespace and re-prepends `pad depth`. Necessary because
    user-supplied tactic source carries the indentation it had at the
    `cyclic_thm` call site, which generally doesn't match the indent
    of its target slot in the emitted script. -/
def reindent (depth : Nat) (s : String) : String :=
  let lines := (s.splitOn "\n").map String.trimLeft
  -- Drop trailing empty lines that come from raw `reprint`.
  let nonEmpty := lines.filter (· != "")
  String.intercalate ("\n" ++ pad depth) nonEmpty

/-- Build the `ih_? args…` expression for a back-edge. Selects the right
    IH from the multi-IH set bound at the ancestor case-split, by looking
    at `σ`'s image of the case-split's induction variable.

    `pathSubst` is the path-substitution from the root to the back-edge:
    each enclosing `caseSplit` adds `(var, pat)`. We use it to render
    each generalised IH arg whose value isn't pinned by `σ` itself —
    nested `induction` consumes `y` (etc.) from the local context, so at
    the back-edge `y` is no longer an identifier; we have to emit its
    case-split-narrowed value (e.g. `0` in the `| 0 =>` arm). For an
    untouched genVar (no enclosing case-split has bound it), pathSubst
    has no entry and we emit the variable name unchanged. -/
def ihCall (sorts : List SortInfo) (ctx : List IHInfo)
    (pathSubst : Subst) (anc : String) (σ : Subst)
    : String :=
  match ctx.find? (fun info => info.anc == anc) with
  | none =>
    "sorry /- no IH for ancestor '" ++ anc ++ "' in scope -/"
  | some info =>
    -- Pick the IH whose recursive-subterm var matches `σ(caseSplitVar)`.
    -- For single-recursive case-splits this is the only option; for
    -- multi-recursive, we route to the matching subtree's IH.
    let chosenIh : Option String :=
      match σ.lookup info.caseSplitVar with
      | some (.var v) =>
        info.ihs.find? (·.1 == v) |>.map (·.2)
      | _ =>
        -- Fall back to the lone IH if there's only one (handles
        -- back-edges that don't explicitly specify a subterm but the
        -- case-split is single-recursive).
        if info.ihs.length == 1 then info.ihs.head?.map (·.2)
        else none
    match chosenIh with
    | none =>
      "sorry /- no matching IH at ancestor '" ++ anc
        ++ "' for σ on '" ++ info.caseSplitVar ++ "' -/"
    | some ihName =>
      if info.genVars.isEmpty then ihName
      else
        let args := info.genVars.map fun v =>
          match σ.lookup v with
          | some t => termToLean sorts t
          | none =>
            match pathSubst.lookup v with
            | some t => termToLean sorts t
            | none   => v
        ihName ++ " " ++ String.intercalate " " args

/-! ### Recursive translator

`translateTree` carries:

  * `depth`     — indentation level
  * `ctx`       — currently-bound IHs (innermost first)
  * `ambient`   — root-vars still available to `generalizing` (a case-split
    consumes its induction var from this pool and passes the rest down)
  * `varSorts`  — variable→sort map; consulted at each case-split to decide
    constructors and build IH info. Extended when a case-split's recursive
    arg introduces a fresh variable of the same sort.
-/
/-- Build the default `simp [<pred>]` tactic, or bare `simp` if no
    predicate name is associated with the goal (the inline-goal form). -/
def defaultSimp (defaultSimpPred : Option String) : String :=
  match defaultSimpPred with
  | some p => "simp [" ++ p ++ "]"
  | none   => "simp"

mutual

partial def translateTree (defaultSimpPred : Option String) (sorts : List SortInfo)
    (depth : Nat) (ctx : List IHInfo) (ambient : List String)
    (varSorts : List (String × SortInfo)) (pathSubst : Subst)
    : ProofTree → String
  | .leaf _ _ _ closeTac =>
    -- Default closes the goal by unfolding the predicate; user can
    -- override (e.g. `decide`, `rfl`, `simp [extras]; …`).
    let body := closeTac.getD (defaultSimp defaultSimpPred)
    pad depth ++ reindent depth body
  | .identity _ _ =>
    pad depth ++ "assumption"
  | .back _ _ anc σ closeTac =>
    -- Default just applies the IH at σ-arguments — the user never has
    -- to know the auto-derived `ih_<…>` binding name. Callers needing
    -- an unfold step wrap the back-edge in a `.node` whose translation
    -- prepends `simp [<pred>]`.
    --
    -- A custom `closeTac` lets the user prepare the goal before the
    -- back-edge fires. The token `recurse` inside the user's tactic is
    -- substituted by `exact ih_<auto-derived>` — so the user can write
    -- e.g. `simp [myAdd]; congr 1; recurse` without ever naming the IH
    -- (preserving the cyclic-proof feel where back-edges, not IHs, are
    -- the primitive).
    let ihExact := "exact " ++ ihCall sorts ctx pathSubst anc σ
    let body := match closeTac with
      | none     => ihExact
      | some tac => tac.replace "recurse" ihExact
    pad depth ++ reindent depth body
  | .node _ _ _ [] =>
    pad depth ++ defaultSimp defaultSimpPred
  | .node _ _ "branch" children =>
    -- Multi-branch node: unfold the predicate, split the goal into N
    -- subgoals via `refine ⟨?_, …, ?_⟩`, then prove each subgoal with
    -- the corresponding child sub-proof. Produced by the DSL's `branch`
    -- step for cyclic proofs over multi-recursive constructors. Each
    -- child is emitted as `· <body>` with the bullet on its own line and
    -- the body indented one level deeper, so Lean's layout rules accept it
    -- regardless of how complex the body is.
    let n := children.length
    let placeholders := String.intercalate ", " (List.replicate n "?_")
    let prelude :=
      pad depth ++ defaultSimp defaultSimpPred ++ "\n"
        ++ pad depth ++ "refine ⟨" ++ placeholders ++ "⟩"
    let bodies := children.map fun child =>
      let inner := translateTree defaultSimpPred sorts (depth + 1) ctx ambient varSorts pathSubst child
      pad depth ++ "·\n" ++ inner
    prelude ++ "\n" ++ String.intercalate "\n" bodies
  | .node _ _ _ [child] =>
    pad depth ++ defaultSimp defaultSimpPred ++ "\n"
      ++ translateTree defaultSimpPred sorts depth ctx ambient varSorts pathSubst child
  | .node lbl _ _ _ =>
    pad depth ++ "sorry /- multi-child node '" ++ lbl ++ "' NYI -/"
  | .haveStep _ _ haveName haveTypeStr haveProofStr cont =>
    -- `have <name> : <type> := by <proof>; <continuation>`. The proof
    -- block is reindented to the right depth; the continuation is then
    -- emitted at the same outer depth so the new hypothesis is in scope
    -- for everything that follows.
    pad depth ++ "have " ++ haveName ++ " : " ++ haveTypeStr ++ " := by\n"
      ++ pad (depth + 1) ++ reindent (depth + 1) haveProofStr ++ "\n"
      ++ translateTree defaultSimpPred sorts depth ctx ambient varSorts pathSubst cont
  | .existsStep _ _ witnessStr cont =>
    -- `exists <witness>` step (∃R). Emits `refine ⟨<witness>, ?_⟩`;
    -- the continuation proves the residual goal `φ[<witness>/x]`.
    pad depth ++ "refine ⟨" ++ witnessStr ++ ", ?_⟩\n"
      ++ translateTree defaultSimpPred sorts depth ctx ambient varSorts pathSubst cont
  | .caseSplit lbl _ var cases =>
    translateCaseSplit defaultSimpPred sorts depth ctx ambient varSorts pathSubst lbl var cases

partial def translateCaseSplit (defaultSimpPred : Option String) (sorts : List SortInfo)
    (depth : Nat) (ctx : List IHInfo) (ambient : List String)
    (varSorts : List (String × SortInfo)) (pathSubst : Subst) (lbl var : String)
    (cases : List (SubjectTerm × ProofTree)) : String :=
  let genVars := ambient.filter (· != var)
  let ambient' := genVars
  let genClause :=
    if genVars.isEmpty then ""
    else " generalizing " ++ String.intercalate " " genVars
  let sortOpt := varSorts.lookup var
  let arms := cases.filterMap fun (patT, sub) =>
    match sortOpt with
    | none => some (pad depth ++ "| _ => sorry /- no sort info for '" ++ var ++ "' -/")
    | some sortInfo =>
      match patToInductionCase sortInfo patT with
      | none => none
      | some (header, ihEntries) =>
        -- IH entries are bound iff the constructor has at least one
        -- recursive arg. The arm's IH context inherits the parent ctx
        -- plus this case-split's IHInfo (with multi-IH list).
        let ctxForArm :=
          if ihEntries.isEmpty then ctx
          else
            let info : IHInfo :=
              { anc := lbl
                caseSplitVar := var
                ihs := ihEntries
                genVars := genVars }
            info :: ctx
        -- All recursive subterm vars get the parent's sort info.
        let varSorts' := ihEntries.foldl (fun acc (v, _) => (v, sortInfo) :: acc) varSorts
        -- Extend path subst with this arm's narrowing (var ↦ pat).
        let pathSubst' : Subst := (var, patT) :: pathSubst
        let body := translateTree defaultSimpPred sorts (depth + 1) ctxForArm ambient' varSorts' pathSubst' sub
        some (pad depth ++ "| " ++ header ++ " =>\n" ++ body)
  pad depth ++ "induction " ++ var ++ genClause ++ " with\n"
    ++ String.intercalate "\n" arms

end

/-! ### Top-level entry -/

/-- Emit a full Lean theorem from a proof tree. Generic over the goal
    surface form:

      * `goalType` is the *string* used as the theorem's conclusion type.
        For the predicate form (`cyclic_thm name : pred args …`), the
        caller passes `pred ++ " " ++ argList`. For the inline-goal
        form (`cyclic_thm name (binders) : <goal> …`), the caller passes
        the original goal expression's source text verbatim.
      * `defaultSimpPred` controls the default `simp [<pred>]` emitted
        on unannotated leaves / unfold nodes. `some s` for the predicate
        form, `none` for the inline-goal form (where the user is
        responsible for providing simp lemmas via `done by simp […]`).

    The root must be a `.caseSplit`; non-case-split roots emit a
    placeholder comment.

    `varSorts` must list the root sequent's free vars in positional
    order, paired with their sort info. -/
def translate (defaultSimpPred : Option String) (goalType thmName : String)
    (varSorts : List (String × SortInfo)) : ProofTree → String
  | t@(.caseSplit _ _ _ _) =>
    let sorts := varSorts.map (·.2)
    let bindings := varSorts.map fun (v, si) => "(" ++ v ++ " : " ++ si.typeStr ++ ")"
    let header := "theorem " ++ thmName ++ " " ++ String.intercalate " " bindings
                    ++ " : " ++ goalType ++ " := by"
    let rootVars := varSorts.map (·.1)
    header ++ "\n" ++ translateTree defaultSimpPred sorts 1 [] rootVars varSorts [] t
  | t =>
    "-- unsupported root (expected .caseSplit); got: " ++ t.label

/-! ### Well-founded recursion emission (paper-style)

Paper-style: this is the cyclic-proof-as-recursive-function reading
emphasised in Wehr 2025 PhD thesis Ch. 6 (CHA → HA via Heyting-arithmetic
recursion) and, more abstractly, in Brotherston 2006 (cyclic proofs as
fixed-point unfoldings). Back-edges become recursive calls of the proven
function; the soundness of the cyclic structure is discharged by emitting
`termination_by <measure>` with the measure synthesised from the SCT
graphs. The synthesised measure feeds Lean's `WellFounded.fix`, which
plays the role of the paper's induction-on-trace appeal.

Where the `induction`-based emission relied on the case-split tree
*coincidentally* aligning with what Lean's structural induction
accepts, this emission carries the cyclic-proof's measure into the
output explicitly. The actual Lean syntax generation (term layout,
recursive-call rendering, `recurse` token substitution) is original.
-/

/-- Render a synthesised `Measure` as a Lean term suitable for the
    `termination_by` clause. Variables of type `Nat` are used directly;
    anything else is wrapped in `sizeOf` to convert to `Nat`. -/
def measureToString (varSorts : List (String × SortInfo)) (m : Measure) : String :=
  let renderVar (i : Nat) : String :=
    match varSorts[i]? with
    | some (v, si) =>
      if si.typeStr == "Nat" then v else "(sizeOf " ++ v ++ ")"
    | none => "_"
  let rec mkTuple : List String → String
    | []  => "0"
    | [x] => x
    | x :: xs => "(" ++ x ++ ", " ++ mkTuple xs ++ ")"
  match m with
  | .lex []   => "0"
  | .lex [i]  => renderVar i
  | .lex idxs => mkTuple (idxs.map renderVar)
  | .sum 0    => "0"
  | .sum n    =>
    String.intercalate " + " ((List.range n).map renderVar)

/-- Extract the back-edge's argument list from its sequent (assumes a
    single-formula succedent — our standard sequent shape). -/
def backArgsOf (seq : Sequent) : List SubjectTerm :=
  match seq.succedents with
  | f :: _ => f.args
  | []     => match seq.antecedents with
    | f :: _ => f.args
    | []     => []

/-- Build a `-- back-edge <lbl>: prog = aN` comment line (with trailing
    indent for the next body line) when the back-edge has an annotation
    in `progMap`; empty string otherwise. Inserted at the top of each
    back-edge's `by`-block so the emitted def documents which argument
    position discharges the SCT cycle through that back-edge. -/
def progCommentFor (progMap : List (String × Nat)) (lbl : String) (depth : Nat)
    : String :=
  match progMap.lookup lbl with
  | some pos =>
    "-- back-edge " ++ lbl ++ ": prog = a" ++ toString pos ++ "\n" ++ pad depth
  | none => ""

mutual

/-- Emit the body of one node in the proof tree as a Lean *term* (or
    a `by`-wrapped tactic block when the node closes a goal). For a
    `cyclic_thm` translation, this term is the body of the recursive
    `def`. -/
partial def walkWFBody (sorts : List SortInfo) (defaultSimpPred : Option String)
    (thmName : String) (progMap : List (String × Nat)) (depth : Nat)
    : ProofTree → String
  | .leaf _ _ _ closeTac =>
    let body := match closeTac with
      | none     => defaultSimp defaultSimpPred
      | some tac => tac
    -- `by\n  <tactics>` form: avoids the parsing fragility of inline
    -- `by tac1\n  tac2` where Lean's tactic parser sometimes treats
    -- the second line as a separate term rather than continuing the
    -- tactic block.
    pad depth ++ "by\n" ++ pad (depth + 1) ++ reindent (depth + 1) body
  | .identity _ _ =>
    pad depth ++ "by assumption"
  | .back lbl seq _ _ closeTac =>
    -- The recursive call: helper applied to the back-edge's args.
    let bArgs := backArgsOf seq
    let argsStr := String.intercalate " " (bArgs.map (termToLean sorts))
    let recCall := thmName ++ " " ++ argsStr
    let body := match closeTac with
      | none     => defaultSimp defaultSimpPred ++ "\n" ++ "exact " ++ recCall
      | some tac => tac.replace "recurse" ("exact " ++ recCall)
    let comment := progCommentFor progMap lbl (depth + 1)
    pad depth ++ "by\n" ++ pad (depth + 1) ++ comment
      ++ reindent (depth + 1) body
  | .node _ _ "branch" children =>
    -- Multi-branch: unfold then exact ⟨...⟩ with each child as a term.
    -- Branch children are emitted as terms, where line comments don't
    -- compose cleanly with tuples; we surface their progs via the
    -- annotation diagnostic instead.
    let childTerms := children.map fun child =>
      match child with
      | .back _ seq _ _ closeTac =>
        let bArgs := backArgsOf seq
        let argsStr := String.intercalate " " (bArgs.map (termToLean sorts))
        let recCall := "(" ++ thmName ++ " " ++ argsStr ++ ")"
        match closeTac with
        | none     => recCall
        | some tac => "(by " ++ (tac.replace "recurse" ("exact " ++ recCall)) ++ ")"
      | .leaf _ _ _ closeTac =>
        let body := match closeTac with
          | none     => defaultSimp defaultSimpPred
          | some tac => tac
        "(by " ++ body ++ ")"
      | _ => "(sorry /- complex branch child NYI -/)"
    let preludeBody := defaultSimp defaultSimpPred ++ "\n"
      ++ pad (depth + 1) ++ "exact ⟨" ++ String.intercalate ", " childTerms ++ "⟩"
    pad depth ++ "by\n" ++ pad (depth + 1) ++ preludeBody
  | .node _ _ _ [] =>
    pad depth ++ "by " ++ defaultSimp defaultSimpPred
  | .node _ _ _ [child] =>
    -- "unfold" wrapper: the simp prefix is rolled into the back's body
    -- if the child is a back-edge; for general children, recurse.
    walkWFBody sorts defaultSimpPred thmName progMap depth child
  | .node lbl _ _ _ =>
    pad depth ++ "(sorry /- multi-child node '" ++ lbl ++ "' not branch -/)"
  | .caseSplit _ _ var cases =>
    walkWFCaseSplit sorts defaultSimpPred thmName progMap depth var cases
  | .haveStep _ _ haveName haveTypeStr haveProofStr cont =>
    -- WF emission would need to wrap the surrounding term in `by` to
    -- introduce a local hypothesis. For now, emit a sorry with a
    -- diagnostic; `have` is supported by the structural emitter, which
    -- handles the typical case (cyclic_thm whose dispatcher routes
    -- through structural anyway).
    let _ := (haveName, haveTypeStr, haveProofStr, cont)
    pad depth ++ "(sorry /- `have` step not supported in WF emission; "
      ++ "use the structural path -/)"
  | .existsStep _ _ witnessStr cont =>
    let _ := (witnessStr, cont)
    pad depth ++ "(sorry /- `exists` step not supported in WF emission; "
      ++ "use the structural path -/)"

partial def walkWFCaseSplit (sorts : List SortInfo) (defaultSimpPred : Option String)
    (thmName : String) (progMap : List (String × Nat)) (depth : Nat) (var : String)
    (cases : List (SubjectTerm × ProofTree)) : String :=
  let arms := cases.map fun (pat, sub) =>
    let patStr := termToLean sorts pat
    let body := walkWFBody sorts defaultSimpPred thmName progMap (depth + 1) sub
    pad depth ++ "| " ++ patStr ++ " =>\n" ++ body
  pad depth ++ "match " ++ var ++ " with\n" ++ String.intercalate "\n" arms

end

/-- Top-level WF emitter. Produces:
    ```
    def <thmName> : ∀ <binders>, <goalType> := fun <args> =>
      <body>
    termination_by <args> => <measure>
    ```
    Falls back to a `def … := sorry` placeholder if root isn't a caseSplit.

    `progMap` is an optional per-back-edge progressing-position map
    (label → position index). When supplied — typically from
    `CyclicTactic.Annotation.annotate` — the emitter prepends a
    `-- back-edge <lbl>: prog = aN` comment to each recursive call's
    `by`-block, surfacing the SCT cycle's witness in the emitted code. -/
def translateWF (defaultSimpPred : Option String) (goalType thmName : String)
    (varSorts : List (String × SortInfo)) (measure : Option Measure)
    (progMap : List (String × Nat) := [])
    : ProofTree → String
  | t@(.caseSplit _ _ _ _) =>
    let sorts := varSorts.map (·.2)
    let bindings := varSorts.map fun (v, si) => "(" ++ v ++ " : " ++ si.typeStr ++ ")"
    let argList := String.intercalate " " (varSorts.map (·.1))
    let header := "def " ++ thmName ++ " : ∀ " ++ String.intercalate " " bindings
                    ++ ", " ++ goalType ++ " := fun " ++ argList ++ " =>\n"
    let body := walkWFBody sorts defaultSimpPred thmName progMap 1 t
    let termClause := match measure with
      | some m =>
        let measureStr := measureToString varSorts m
        "termination_by " ++ argList ++ " => " ++ measureStr
      | none => ""
    let trailer :=
      if termClause.isEmpty then "" else "\n" ++ termClause
    header ++ body ++ trailer
  | t =>
    "-- unsupported root (expected .caseSplit); got: " ++ t.label

end CyclicTactic.Unravel
