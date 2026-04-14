import Cyclic.SizeChange

/-!
# Termination measure synthesis from size-change graphs

Given a list of size-change graphs (as produced by `extractAllSCGs`),
try to synthesize a syntactic termination measure that Lean's well-founded
recursion machinery can verify.

Two candidate schemas are tried, in order:

1. **Lex measure** — a permutation `π` of the parameter indices such that
   every graph has a "≥*-strict" self-loop chain along `π`. Captures
   lexicographic termination (e.g. Ackermann).

2. **Sum measure** — `a₀ + a₁ + … + a_{n-1}` is a valid measure iff every
   graph admits a bijection between callee args and caller params where
   every edge is ≥ and at least one is strict (e.g. swapAdd — parameters
   permute, but the sum still strictly decreases).

Both synthesizers only use the original per-call graphs, not the closure,
because Lean needs the measure to decrease on **every** recursive call.
-/

namespace SCGraph

/-- Does `g` have a strict self-loop at parameter `i`? -/
def selfLoopStrict (g : SCGraph) (i : Nat) : Bool :=
  g.edges.any fun e => e.src == i && e.tgt == i && e.label == .strict

/-- Does `g` have any self-loop at parameter `i` (strict or nonstrict)? -/
def selfLoopAny (g : SCGraph) (i : Nat) : Bool :=
  g.edges.any fun e => e.src == i && e.tgt == i

end SCGraph

/-! ### Permutation enumeration -/

/-- Enumerate all permutations of a list of distinct naturals. -/
partial def allPerms : List Nat → List (List Nat)
  | [] => [[]]
  | xs =>
    xs.flatMap fun x =>
      (allPerms (xs.filter (· != x))).map (x :: ·)

/-! ### Lex synthesis -/

/-- Along permutation `perm`, graph `g` strictly decreases iff we find some
    position with a strict self-loop, with all earlier positions having at
    least a nonstrict self-loop. -/
partial def lexValidates (perm : List Nat) (g : SCGraph) : Bool :=
  match perm with
  | [] => false
  | i :: rest =>
    if g.selfLoopStrict i then true
    else if g.selfLoopAny i then lexValidates rest g
    else false

/-- Find a parameter-index permutation that validates every graph, if one exists. -/
def synthLexOrder (gs : List SCGraph) (arity : Nat) : Option (List Nat) :=
  (allPerms (List.range arity)).find? fun perm => gs.all (lexValidates perm)

/-! ### Sum synthesis -/

/-- Does the sum `a₀ + … + a_{n-1}` strictly decrease on this graph?
    Needs a bijection callee→caller with each edge ≥ and at least one strict. -/
partial def sumDecreasesIn (g : SCGraph) : Bool :=
  if g.dom != g.codom then false
  else
    let arity := g.dom
    (allPerms (List.range arity)).any fun perm =>
      let matched := (List.range arity).all fun j =>
        g.edges.any fun e => e.src == perm[j]! && e.tgt == j
      let hasStrict := (List.range arity).any fun j =>
        g.edges.any fun e => e.src == perm[j]! && e.tgt == j && e.label == .strict
      matched && hasStrict

/-- Is the sum-of-args a valid termination measure for this graph set? -/
def sumMeasureWorks (gs : List SCGraph) : Bool :=
  gs.all sumDecreasesIn

/-! ### Unified synthesis -/

/-- A synthesized termination measure. -/
inductive Measure where
  /-- Lex order on the parameter indices (outermost first). -/
  | lex (order : List Nat)
  /-- Sum of the first `arity` parameters. -/
  | sum (arity : Nat)
  deriving Repr

instance : ToString Measure where
  toString
    | .lex order =>
      let elems := order.map (fun i => s!"a{i}")
      s!"lex ({String.intercalate ", " elems})"
    | .sum n =>
      if n == 0 then "0"
      else String.intercalate " + " ((List.range n).map (fun i => s!"a{i}"))

/-- Try lex first, then sum. Returns `none` if neither schema works. -/
def synthMeasure (gs : List SCGraph) (arity : Nat) : Option Measure :=
  match synthLexOrder gs arity with
  | some order => some (.lex order)
  | none => if sumMeasureWorks gs then some (.sum arity) else none
