import Lean
import Cyclic.Extract
import Cyclic.SizeChange
import Cyclic.Measure

/-!
# The `cyclic_def` command

A command macro that lets users write pattern-matching recursive definitions
in natural Lean syntax. The macro:

  1. Parses each equation into our `Equation` AST at elaboration time.
  2. Runs `extractAllSCGs` + `checkMultiSCT` to verify termination by
     size-change. If the check fails, the command is rejected with an
     error pointing at the offending function name.
  3. Runs `synthMeasure` to pick a termination measure (lex on a
     permutation of parameters, or sum-of-args). The measure is emitted
     as the `termination_by` clause of a standard Lean `def`.

## Supported shape

```
cyclic_def swapAdd : Nat → Nat → Nat
  | 0, y        => y
  | .succ x', y => .succ (swapAdd y x')
```

## Scope

- Patterns: numeric literals, identifiers, `.succ p`, `Nat.succ p`,
  `Nat.zero`, parenthesized patterns.
- Bodies: arbitrary Lean terms; applications with head = the function
  name are recognized as recursive calls.
-/

open Lean Elab Command

namespace Cyclic

/-! ### Syntactic pattern → Pattern value -/

partial def patSynToValue (stx : Syntax) : CommandElabM _root_.Pattern := do
  match stx with
  | `($n:num) =>
    let rec go : Nat → Pattern
      | 0 => .ctor "zero" []
      | k + 1 => .ctor "succ" [go k]
    return go n.getNat
  | `($i:ident) =>
    return .var i.getId.toString
  | `(.$i:ident $args*) => do
    let vs ← args.toList.mapM fun a => patSynToValue a.raw
    return .ctor i.getId.toString vs
  | `(Nat.succ $p) => do
    return .ctor "succ" [← patSynToValue p.raw]
  | `(Nat.zero) => return .ctor "zero" []
  | `(($p)) => patSynToValue p.raw
  | _ => return .var "?"

/-! ### Syntactic body → Term value -/

partial def bodySynToValue (funName : Name) (stx : Syntax) : CommandElabM _root_.Term := do
  match stx with
  | `($n:num) =>
    let rec go : Nat → _root_.Term
      | 0 => .ctor "zero" []
      | k + 1 => .ctor "succ" [go k]
    return go n.getNat
  | `($i:ident) =>
    if i.getId == funName then return .recCall []
    else return .var i.getId.toString
  | `(.$i:ident $args*) => do
    let vs ← args.toList.mapM fun a => bodySynToValue funName a.raw
    return .ctor i.getId.toString vs
  | `($f $args*) => do
    let vs ← args.toList.mapM fun a => bodySynToValue funName a.raw
    match f with
    | `($i:ident) =>
      if i.getId == funName then return .recCall vs
      else return .ctor i.getId.toString vs
    | _ => return .ctor "?" vs
  | `(($e)) => bodySynToValue funName e.raw
  | _ => return .ctor "?" []

/-! ### Synthesized measure → Lean syntax -/

/-- Build a tuple term from a non-empty list, right-nested:
    `[a]    ↦ a`
    `[a,b]  ↦ (a, b)`
    `[a,b,c]↦ (a, (b, c))`
    which matches Lean's native lex order on nested products. -/
partial def mkTuple : List (TSyntax `term) → CommandElabM (TSyntax `term)
  | []      => `((0 : Nat))
  | [x]     => pure x
  | x :: xs => do
    let rest ← mkTuple xs
    `(($x, $rest))

/-- Emit a Lean `term` for a synthesized `Measure`, using `idents[i]` for
    parameter `aᵢ`. -/
def measureToSyntax (m : Measure) (idents : Array (TSyntax `ident))
    : CommandElabM (TSyntax `term) := do
  let termIdents : Array (TSyntax `term) := idents.map fun id => ⟨id.raw⟩
  match m with
  | .lex [] => `((0 : Nat))
  | .lex [i] => return termIdents[i]!
  | .lex is =>
    mkTuple (is.map fun i => termIdents[i]!)
  | .sum 0 => `((0 : Nat))
  | .sum n => do
    let mut acc : TSyntax `term := termIdents[0]!
    for i in [1:n] do
      acc ← `($acc + $(termIdents[i]!))
    pure acc

end Cyclic

/-! ### The command itself. -/

/-- Declare the `cyclic_def` command syntax. -/
syntax (name := cyclicDef)
  "cyclic_def " ident " : " term (" | " term,+ " => " term)* : command

open Cyclic in
elab_rules : command
  | `(cyclic_def $name:ident : $type:term $[| $pats,* => $body]*) => do
    let funName := name.getId

    -- Parse equations into ASTs (VALUES, not syntax) so we can run the
    -- size-change analysis at elaboration time.
    let mut eqValues : List Equation := []
    let mut firstArity : Nat := 0
    for h : idx in [0:pats.size] do
      let ps := pats[idx]
      let b  := body[idx]!
      if idx == 0 then firstArity := ps.getElems.size
      let patVs ← ps.getElems.toList.mapM fun p => patSynToValue p.raw
      let bodyV ← bodySynToValue funName b.raw
      eqValues := eqValues ++ [{ patterns := patVs, body := bodyV }]

    let graphs := extractAllSCGs eqValues

    -- Multi-graph SCT check. If it fails, reject the definition.
    unless SCGraph.checkMultiSCT graphs do
      let graphLines := graphs.map fun g => "  " ++ toString g
      throwErrorAt name
        ("cyclic_def '" ++ toString funName ++ "': multi-SCT check FAILED.\n"
         ++ "Extracted graphs:\n"
         ++ String.intercalate "\n" graphLines
         ++ "\nSome idempotent in the composition-closure has no strict self-loop, "
         ++ "so no SCT-based measure exists.")

    -- Synthesize a termination measure (lex, then sum).
    let some measure := synthMeasure graphs firstArity
      | throwErrorAt name
          ("cyclic_def '" ++ toString funName ++ "': multi-SCT passes but neither "
           ++ "lex nor sum-of-args measure works; a more sophisticated measure is required.")

    -- Fresh binder names a₀, a₁, ... for termination_by.
    let freshIdents : Array (TSyntax `ident) :=
      (Array.range firstArity).map fun i => mkIdent (Name.mkSimple s!"a{i}")

    let measureSyn ← measureToSyntax measure freshIdents

    -- Emit the def with the synthesized measure.
    let defCmd ← `(command|
      def $name : $type
        $[| $pats,* => $body]*
      termination_by $freshIdents* => $measureSyn)
    elabCommand defCmd

    -- Diagnostic report.
    let graphLines := graphs.map fun g => "  " ++ toString g
    logInfoAt name
      ("[cyclic_def " ++ toString funName ++ "] multi-SCT PASS; measure = "
       ++ toString measure ++ "; graphs:\n"
       ++ String.intercalate "\n" graphLines)
