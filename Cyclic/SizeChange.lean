/-!
# Size-Change Graphs

Size-change graphs track how arguments change across recursive calls.
The size-change termination principle (Lee, Jones, Ben-Amram 2001) states
that a set of mutually recursive functions terminates if every infinite
call sequence would force an infinite descent in a well-founded domain.

This is the mechanism underlying the soundness of cyclic proofs:
the size-change condition ensures that every cyclic proof can be
unravelled into a standard proof by well-founded induction.
-/

/-- A descent label on a size-change edge. -/
inductive Descent where
  /-- ≥ : the target is at most the source (preserving) -/
  | nonstrict
  /-- > : the target is strictly less than the source (progressing) -/
  | strict
  deriving Repr, DecidableEq, BEq

namespace Descent

/-- Composing descents along a call chain: strict absorbs nonstrict. -/
def comp : Descent → Descent → Descent
  | .strict, _ => .strict
  | _, .strict => .strict
  | .nonstrict, .nonstrict => .nonstrict

instance : ToString Descent where
  toString
    | .nonstrict => "≥"
    | .strict => ">"

end Descent

/-- An edge in a size-change graph from parameter `src` to parameter `tgt`. -/
structure SCEdge where
  src : Nat
  tgt : Nat
  label : Descent
  deriving Repr, DecidableEq, BEq

instance : ToString SCEdge where
  toString e := s!"{e.src} -{e.label}→ {e.tgt}"

/-- A size-change graph from a caller with `dom` parameters
    to a callee with `codom` parameters. -/
structure SCGraph where
  dom : Nat
  codom : Nat
  edges : List SCEdge
  deriving Repr

namespace SCGraph

/-- Compose two size-change graphs by chaining edges through the
    intermediate function. If g₁ has edge (i -l₁→ j) and g₂ has
    edge (j -l₂→ k), the result has edge (i -(l₁ ∘ l₂)→ k). -/
def comp (g₁ g₂ : SCGraph) : SCGraph where
  dom := g₁.dom
  codom := g₂.codom
  edges := g₁.edges.flatMap fun e₁ =>
    g₂.edges.filterMap fun e₂ =>
      if e₁.tgt == e₂.src then
        some ⟨e₁.src, e₂.tgt, e₁.label.comp e₂.label⟩
      else
        none

/-- Does this graph have a strict descent on the diagonal
    (some parameter i maps to itself with strict decrease)? -/
def hasStrictDiag (g : SCGraph) : Bool :=
  g.edges.any fun e => e.src == e.tgt && e.label == .strict

/-- Alias for `hasStrictDiag`: a strict self-loop. -/
def hasStrictSelfLoop (g : SCGraph) : Bool := g.hasStrictDiag

/-- Check size-change termination for a single self-recursive function.
    Computes successive powers G, G², G³, ... and checks if any has
    a strict diagonal descent. Terminates after `fuel` iterations. -/
def checkSCT (g : SCGraph) (fuel : Nat := 100) : Bool :=
  go g fuel
where
  go (current : SCGraph) : Nat → Bool
    | 0 => false
    | n + 1 =>
      if current.hasStrictDiag then true
      else go (current.comp g) n

instance : ToString SCGraph where
  toString g :=
    let edges := g.edges.map fun e => s!"{e}"
    s!"SCGraph({g.dom} → {g.codom}): [{String.intercalate ", " edges}]"

/-! ### Multi-graph SCT: closure + idempotent check

The size-change principle in its full generality (Lee, Jones, Ben-Amram 2001):
given a set G of size-change graphs describing the recursive calls of a
(mutually recursive) function system, termination holds iff every
**idempotent** graph in the composition-closure of G has a strict self-loop.

This subsumes the single-graph power-iteration check above, and handles
cases like Ackermann where termination is lexicographic rather than single
strict-diagonal.
-/

/-- Combine two descents on the same (src,tgt) pair: strict absorbs nonstrict. -/
def Descent.join : Descent → Descent → Descent
  | .strict, _ => .strict
  | _, .strict => .strict
  | _, _ => .nonstrict

/-- Keep at most one edge per (src,tgt), joining labels (strict wins). -/
def canonEdges : List SCEdge → List SCEdge
  | [] => []
  | e :: rest =>
    let rest' := canonEdges rest
    if rest'.any (fun x => x.src == e.src && x.tgt == e.tgt) then
      rest'.map fun x =>
        if x.src == e.src && x.tgt == e.tgt then
          { x with label := Descent.join x.label e.label }
        else x
    else
      e :: rest'

/-- Canonical form: deduplicated edges. -/
def canon (g : SCGraph) : SCGraph := { g with edges := canonEdges g.edges }

/-- Structural equivalence: same dom/codom and same canonical edge set. -/
def equiv (g₁ g₂ : SCGraph) : Bool :=
  let c₁ := g₁.canon
  let c₂ := g₂.canon
  c₁.dom == c₂.dom && c₁.codom == c₂.codom
    && c₁.edges.length == c₂.edges.length
    && c₁.edges.all (fun e => c₂.edges.elem e)

/-- A graph is idempotent if `g.comp g ≡ g` (and dom = codom). -/
def isIdempotent (g : SCGraph) : Bool :=
  g.dom == g.codom && equiv (g.comp g) g

/-- Close a list of graphs under pairwise composition, up to `fuel` rounds.
    Returns the canonical closure (modulo `equiv`). -/
partial def closure (gs : List SCGraph) (fuel : Nat := 100) : List SCGraph :=
  let init := gs.foldl (init := ([] : List SCGraph)) fun acc g =>
    let cg := g.canon
    if acc.any (equiv · cg) then acc else acc ++ [cg]
  loop init fuel
where
  loop (cur : List SCGraph) : Nat → List SCGraph
    | 0 => cur
    | n + 1 =>
      let candidates := cur.flatMap fun g₁ =>
        cur.filterMap fun g₂ =>
          if g₁.codom == g₂.dom then some (g₁.comp g₂).canon else none
      let novel := candidates.foldl (init := ([] : List SCGraph)) fun acc c =>
        if cur.any (equiv · c) || acc.any (equiv · c) then acc else acc ++ [c]
      if novel.isEmpty then cur
      else loop (cur ++ novel) n

/-- Multi-graph SCT check: every idempotent in the closure must have a strict self-loop. -/
def checkMultiSCT (gs : List SCGraph) (fuel : Nat := 100) : Bool :=
  let closed := closure gs fuel
  closed.filter isIdempotent |>.all hasStrictSelfLoop

end SCGraph
