import CyclicTactic.ProofTree
import CyclicTactic.Measure

/-!
# Shared script-emission utilities

Type metadata and string-building helpers used by both:

  * `CyclicTactic.Build` — introspects sort/constructor info from the
    Lean environment when elaborating a `cyclic_thm`.
  * `CyclicTactic.Theorem6.Emit` — the Grotenhuis-Otten Theorem 6.1
    emitter that turns an annotated `ProofTree` into a Lean tactic
    script.

Was previously `CyclicTactic.Unravel` (the legacy structural emitter);
that emitter has been retired in favour of `Theorem6.Emit`, and only
the shared infrastructure remains.

## Sort info

Populated by `CyclicTactic.Build.buildSortInfo` at elaboration time and
passed in as `List SortInfo` (one per root-sequent variable, in
positional order matching the predicate's argument list). The emitter
itself doesn't know about Lean's environment — it just consumes the
pre-computed sort table.
-/

namespace CyclicTactic.EmitCommon

open CyclicTactic.Proof

/-! ### Sort info -/

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

For a `SubjectTerm` pattern like `.ctor "succ" [.var "x'"]`, look up the
constructor in the case-split var's sort and produce:

  * the case header string (e.g. `"succ x'"` for non-recursive ctors,
    `"succ x' ih_x'"` for single-rec, `"node l r ih_l ih_r"` for
    multi-rec) — suitable for an `induction … with` arm,
  * the list of `(recArgVar, ihName)` pairs the case binds.

Each recursive constructor arg generates one IH, named after the
subterm variable: `ih_<recArgVarName>`. Back-edges select the correct
IH based on which subterm `σ` targets.

For `cases` arms (no IH binding), use `Theorem6.Emit.patToCasesHeader`
which mirrors this without the trailing IH names. -/
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

/-! ### Indentation + simp helpers -/

/-- `n` levels of two-space indentation. -/
def pad (n : Nat) : String := String.ofList (List.replicate (n * 2) ' ')

/-- Re-indent a multi-line tactic block to `depth`. Strips each line's
    leading whitespace and re-prepends `pad depth`. Necessary because
    user-supplied tactic source carries the indentation it had at the
    `cyclic_thm` call site, which generally doesn't match the indent
    of its target slot in the emitted script. -/
def reindent (depth : Nat) (s : String) : String :=
  let lines := (s.splitOn "\n").map fun ln => (String.trimAsciiStart ln).toString
  let nonEmpty := lines.filter (· != "")
  String.intercalate ("\n" ++ pad depth) nonEmpty

/-- Build the default `simp [<pred>]` tactic, or bare `simp` if no
    predicate name is associated with the goal (the inline-goal form). -/
def defaultSimp (defaultSimpPred : Option String) : String :=
  match defaultSimpPred with
  | some p => "simp [" ++ p ++ "]"
  | none   => "simp"

end CyclicTactic.EmitCommon
