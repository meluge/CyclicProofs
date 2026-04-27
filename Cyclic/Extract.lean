import Cyclic.SizeChange

/-!
# Extracting Size-Change Graphs from Recursive Definitions

Given a syntactic representation of a pattern-matching recursive function,
automatically compute the size-change graph for each recursive call.

## Extraction rule (Lee-Jones-Ben-Amram POPL 2001, §4 / Definition 3)

For each recursive call `f(a₀, ..., aₘ₋₁)` in the body of an equation with
caller patterns `(p₀, ..., pₙ₋₁)`, produce an edge from i to j when:
  • `aⱼ` is a variable `v` equal to the pattern `pᵢ`  → edge (i →≥ j)
  • `aⱼ` is a variable `v` strictly inside `pᵢ`     → edge (i →> j)
  • otherwise                                        → no edge

This is the direct syntactic analog of LJBA's size-change analysis:
matching on a constructor makes the pattern variables strictly smaller,
passing an unchanged variable preserves size.
-/

/-! ### Abstract syntax for equations -/

/-- A pattern in a recursive equation. -/
inductive Pattern where
  | var (name : String)
  | ctor (name : String) (args : List Pattern)
  deriving Repr, BEq, Inhabited

/-- A term in the body of a recursive equation.
    `recCall` marks a call to the function being defined. -/
inductive Term where
  | var (name : String)
  | ctor (name : String) (args : List Term)
  | recCall (args : List Term)
  deriving Repr, BEq, Inhabited

/-- A single equation of a recursive definition. -/
structure Equation where
  patterns : List Pattern
  body : Term
  deriving Repr

/-! ### Analysis primitives -/

namespace Pattern

/-- Depth at which variable `v` appears in a pattern.
    `some 0` means the pattern IS exactly `v` (no decrease).
    `some k` for `k > 0` means `v` is a strict subterm (strict decrease).
    `none` means `v` does not appear in this pattern. -/
partial def depthOf (v : String) : Pattern → Option Nat
  | .var n => if n == v then some 0 else none
  | .ctor _ args =>
    args.foldl (init := none) fun acc p =>
      match acc with
      | some d => some d
      | none => (depthOf v p).map (· + 1)

end Pattern

namespace Term

/-- Return the variable name if this term is a variable, else `none`. -/
def asVar : Term → Option String
  | .var n => some n
  | _ => none

/-- Collect every recursive call appearing in a term
    (returning each call's argument list). -/
partial def recCalls : Term → List (List Term)
  | .var _ => []
  | .ctor _ args => args.flatMap recCalls
  | .recCall args => args :: args.flatMap recCalls

end Term

/-! ### Structural comparison between terms and patterns -/

/-- Is the term structurally equal to the pattern?
    Variables match by name, constructors by name + arity + component-wise
    equality. Recursive calls never match. -/
partial def Term.structEqPattern : Term → Pattern → Bool
  | .var a, .var b => a == b
  | .ctor tn targs, .ctor pn pargs =>
    tn == pn && targs.length == pargs.length
      && (targs.zip pargs).all (fun (t, p) => Term.structEqPattern t p)
  | _, _ => false

/-- Is the term a strict subterm of the pattern?
    (strictly smaller in the subterm ordering). -/
partial def Pattern.hasStrictSub (pat : Pattern) (t : Term) : Bool :=
  match pat with
  | .var _ => false
  | .ctor _ args => args.any fun p => t.structEqPattern p || p.hasStrictSub t

/-- Descent of callee argument `a` relative to caller pattern `p`:
    • `some .nonstrict` if `a` is structurally equal to `p`
    • `some .strict` if `a` is a strict subterm of `p`
    • `none` otherwise.
    Prefers the strongest descent available. -/
def descentOf (p : Pattern) (a : Term) : Option Descent :=
  if a.structEqPattern p then some .nonstrict
  else if p.hasStrictSub a then some .strict
  else none

/-! ### Size-change graph extraction -/

/-- Build the size-change graph for a single recursive call
    with the caller's patterns and the callee's arguments. -/
def buildSCG (patterns : List Pattern) (callArgs : List Term) : SCGraph :=
  let dom := patterns.length
  let codom := callArgs.length
  let edges := (List.range dom).flatMap fun i =>
    (List.range codom).filterMap fun j =>
      let p := patterns[i]!
      let a := callArgs[j]!
      (descentOf p a).map (fun d => ⟨i, j, d⟩)
  { dom, codom, edges }

/-- Extract every size-change graph from a list of equations:
    one graph per recursive call in each equation's body. -/
def extractAllSCGs (eqs : List Equation) : List SCGraph :=
  eqs.flatMap fun eq =>
    eq.body.recCalls.map (buildSCG eq.patterns)
