import Cyclic.ProofTree
import Cyclic.Measure

/-!
# Stage 3: unravelling a validated cyclic proof into a Lean tactic script

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

Sort info is *introspected* from the Lean environment by `Cyclic.ThmCmd`
and passed in as `List SortInfo` (one per root-sequent variable, in
positional order matching the predicate's argument list). The translator
itself doesn't know about Lean's environment — it just consumes the
pre-computed sort table.

## Lex descent via nested induction

A back-edge whose trace graph encodes lex descent is discharged by
nesting a second `induction` inside the outer `succ`/`cons`/… arm. This
gives lex-style termination for free — Lean's kernel re-checks the nested
inductions and the SCT condition guarantees they're well-founded.
-/

namespace Cyclic.Unravel

open Cyclic.Proof

/-! ### Sort info (populated by `Cyclic.ThmCmd` at elaboration time) -/

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

  * the case header string (e.g. `"succ x'"`),
  * `some <recVarName>` if the constructor has exactly one recursive arg
    (so a single IH gets bound), `none` otherwise.

Multi-recursive constructors return `none` and force a fallback to a
`sorry` stub — handling them is Phase 4 work.
-/
def patToInductionCase (sortInfo : SortInfo) (pat : SubjectTerm)
    : Option (String × Option String) :=
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
        let argsStr :=
          if argVars.isEmpty then ""
          else " " ++ String.intercalate " " argVars
        let header := ci.shortName ++ argsStr
        match ci.recArgs with
        | []   => some (header, none)
        | [i]  => some (header, argVars[i]?)
        | _    => none  -- multi-recursive: defer
  | _ => none

/-! ### IH context

Each in-scope induction hypothesis. `genVars` lists the vars the IH was
generalised over, in order — back-edges supply σ-images for them. -/
structure IHInfo where
  anc : String
  ihName : String
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

/-- Build the `ih_? args…` expression for a back-edge. -/
def ihCall (sorts : List SortInfo) (ctx : List IHInfo) (anc : String) (σ : Subst)
    : String :=
  match ctx.find? (fun info => info.anc == anc) with
  | none =>
    "sorry /- no IH for ancestor '" ++ anc ++ "' in scope -/"
  | some info =>
    if info.genVars.isEmpty then info.ihName
    else
      let args := info.genVars.map fun v =>
        match σ.lookup v with
        | some t => termToLean sorts t
        | none   => v
      info.ihName ++ " " ++ String.intercalate " " args

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
    (varSorts : List (String × SortInfo))
    : ProofTree → String
  | .leaf _ _ _ closeTac =>
    -- Default closes the goal by unfolding the predicate; user can
    -- override (e.g. `decide`, `rfl`, `simp [extras]; …`).
    let body := closeTac.getD (defaultSimp defaultSimpPred)
    pad depth ++ reindent depth body
  | .identity _ _ =>
    pad depth ++ "assumption"
  | .back _ _ anc σ closeTac =>
    -- Default just applies the IH at σ-arguments. Callers needing an
    -- unfold step (the typical case) wrap the back-edge in a `.node`
    -- whose translation prepends `simp [<pred>]`. Custom `closeTac`
    -- overrides the default, giving full control for non-trivial
    -- inductive steps where the IH applies to a sub-position.
    let body := closeTac.getD ("exact " ++ ihCall sorts ctx anc σ)
    pad depth ++ reindent depth body
  | .node _ _ _ [] =>
    pad depth ++ defaultSimp defaultSimpPred
  | .node _ _ _ [child] =>
    pad depth ++ defaultSimp defaultSimpPred ++ "\n"
      ++ translateTree defaultSimpPred sorts depth ctx ambient varSorts child
  | .node lbl _ _ _ =>
    pad depth ++ "sorry /- multi-child node '" ++ lbl ++ "' NYI -/"
  | .caseSplit lbl _ var cases =>
    translateCaseSplit defaultSimpPred sorts depth ctx ambient varSorts lbl var cases

partial def translateCaseSplit (defaultSimpPred : Option String) (sorts : List SortInfo)
    (depth : Nat) (ctx : List IHInfo) (ambient : List String)
    (varSorts : List (String × SortInfo)) (lbl var : String)
    (cases : List (SubjectTerm × ProofTree)) : String :=
  let ihName := "ih_" ++ var
  let genVars := ambient.filter (· != var)
  let info : IHInfo := { anc := lbl, ihName := ihName, genVars := genVars }
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
      | some (header, recArgVar?) =>
        let hasIh := recArgVar?.isSome
        let ihSuffix := if hasIh then " " ++ ihName else ""
        let ctxForArm := if hasIh then info :: ctx else ctx
        let varSorts' :=
          match recArgVar? with
          | some v => (v, sortInfo) :: varSorts
          | none   => varSorts
        let body := translateTree defaultSimpPred sorts (depth + 1) ctxForArm ambient' varSorts' sub
        some (pad depth ++ "| " ++ header ++ ihSuffix ++ " =>\n" ++ body)
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
    header ++ "\n" ++ translateTree defaultSimpPred sorts 1 [] rootVars varSorts t
  | t =>
    "-- unsupported root (expected .caseSplit); got: " ++ t.label

end Cyclic.Unravel
