import Cyclic.SizeChange

/-!
# Cyclic proof trees

Data types for cyclic proofs of sequents, with back-edges to ancestor
nodes. The design mirrors the function side (`Cyclic.Extract`) but for
propositions rather than definitions.

## Scope (stage 2)

- Subject terms: variables and named constructors (no recursive calls,
  unlike `Cyclic.Extract.Term` which models function bodies).
- Formulas: single-predicate applications `P(t₁, …, tₙ)`.
- Sequents: two-sided `Γ ⊢ Δ`, where each side is a list of formulas.
- Proof trees: leaves, identity axioms, generic rule applications
  with child subtrees, case-splits, and back-edges to labelled
  ancestors carrying a substitution.

## Per-occurrence traces

The trace condition for cyclic proofs comes from Brotherston, "Sequent
Calculus Proof Systems for Inductive Definitions" (PhD thesis, 2006,
Ch. 5) and Sprenger-Dam (FoSSaCS 2003): a cyclic proof is sound iff
every infinite branch carries an infinitely-progressing trace.

The implementation below — flattening sequent positions to integer
indices and building one `SCGraph` per back-edge — is the standard
encoding of Brotherston's trace condition into LJBA's size-change
framework. The vertex flattening, occurrence-pair matching, and edge
emission rules are original choices; the ideas they encode are not.

For each back-edge `B → A` we emit one `SCGraph` whose vertices are
`(side, formula-occurrence, arg-position)` triples flattened to a single
integer index. Edges encode descent between ancestor arg-slots and
back-edge arg-slots within **matched** formula occurrences (same side,
same index, same predicate, same arity).

Matching by sequent position assumes the rules along the path preserve
the formula-structure of the sequent (which is true for `.caseSplit`
and for `.node` rules that don't add or remove formulas — the fragment
modelled here). Rules like weakening, contraction, or cut would need
occurrence-reindexing info on the edge; that's outside this stage.

Unfolds don't need a dedicated rule: the unfolded form is already
carried by the child node's `.sequent`, and the back-edge comparison
compares A's args under path-substitution to B's args directly, which
implicitly sees every intervening unfold.
-/

namespace Cyclic.Proof

/-! ### Subject terms -/

/-- A term that occurs inside a formula — variables and constructors.
    Distinct from `Cyclic.Extract.Term` because proof terms do not have
    "recursive calls". -/
inductive SubjectTerm where
  | var (name : String)
  | ctor (name : String) (args : List SubjectTerm)
  deriving Repr, BEq, Inhabited

namespace SubjectTerm

/-- Structural equality (variables by name). -/
partial def structEq : SubjectTerm → SubjectTerm → Bool
  | .var a, .var b => a == b
  | .ctor n args, .ctor n' args' =>
    n == n' && args.length == args'.length
      && (args.zip args').all (fun (a, b) => structEq a b)
  | _, _ => false

/-- Is `u` a strict subterm of `t`? -/
partial def strictSubterm (u t : SubjectTerm) : Bool :=
  match t with
  | .var _ => false
  | .ctor _ args => args.any fun a => structEq u a || strictSubterm u a

/-- Apply a substitution (var-name ↦ replacement) to a subject term.
    Iterates on variables so chained bindings like `[("x", x'), ("x'", x'')]`
    resolve transitively (var "x" ↦ var "x''"). Assumes the substitution
    is acyclic — a reasonable invariant when it's built from case-splits,
    which always introduce fresh variables. -/
partial def subst (σ : List (String × SubjectTerm)) : SubjectTerm → SubjectTerm
  | .var n =>
    match σ.lookup n with
    | none => .var n
    | some t => subst σ t
  | .ctor n args => .ctor n (args.map (subst σ))

partial def toString : SubjectTerm → String
  | .var n => n
  | .ctor n [] => n
  | .ctor n args =>
    n ++ "(" ++ String.intercalate ", " (args.map toString) ++ ")"

instance : ToString SubjectTerm := ⟨SubjectTerm.toString⟩

end SubjectTerm

/-! ### Formulas and sequents -/

/-- An atomic formula: a predicate applied to subject terms. -/
structure Formula where
  pred : String
  args : List SubjectTerm
  deriving Repr, BEq, Inhabited

namespace Formula

def toString (φ : Formula) : String :=
  if φ.args.isEmpty then φ.pred
  else φ.pred ++ "(" ++ String.intercalate ", " (φ.args.map SubjectTerm.toString) ++ ")"

instance : ToString Formula := ⟨Formula.toString⟩

/-- Apply a substitution to every arg. -/
def subst (σ : List (String × SubjectTerm)) (φ : Formula) : Formula :=
  { φ with args := φ.args.map (SubjectTerm.subst σ) }

end Formula

/-- A two-sided sequent `Γ ⊢ Δ`. -/
structure Sequent where
  antecedents : List Formula := []
  succedents : List Formula := []
  deriving Repr, Inhabited

namespace Sequent

def toString (s : Sequent) : String :=
  let lhs := String.intercalate ", " (s.antecedents.map Formula.toString)
  let rhs := String.intercalate ", " (s.succedents.map Formula.toString)
  if s.antecedents.isEmpty then "⊢ " ++ rhs
  else if s.succedents.isEmpty then lhs ++ " ⊢"
  else lhs ++ " ⊢ " ++ rhs

instance : ToString Sequent := ⟨Sequent.toString⟩

/-- Singleton-succedent sequent `⊢ φ`. -/
def succ1 (φ : Formula) : Sequent := { succedents := [φ] }

/-- Singleton-antecedent sequent `φ ⊢`. -/
def ant1 (φ : Formula) : Sequent := { antecedents := [φ] }

end Sequent

/-- A substitution used on back-edges. -/
abbrev Subst := List (String × SubjectTerm)

/-! ### Proof trees -/

/-- A cyclic proof tree. Each node carries a label so back-edges can
    reference ancestors by name.

    `.leaf` and `.back` carry an optional `closeTactic` — the literal
    Lean tactic the unraveller should emit to close the goal. When `none`,
    the unraveller uses sensible defaults (`simp [<pred>]` for leaves,
    `simp [<pred>]; exact ih_<…>` for back-edges). When `some s`, the
    unraveller emits `s` verbatim — letting the user override with e.g.
    `congr; exact ih_n` for non-trivial inductive proofs where the IH
    applies to a sub-position of the goal. -/
inductive ProofTree where
  /-- A generic leaf: the sequent is closed by some external justification
      (informational string). Trace through a leaf is nil. -/
  | leaf (label : String) (seq : Sequent) (justification : String)
         (closeTactic : Option String := none)
  /-- The identity axiom `Γ, φ ⊢ φ, Δ`. No children, no continuation. -/
  | identity (label : String) (seq : Sequent)
  /-- An inner node: application of a named rule to children subtrees.
      Does not bind any variables; callers whose rule is a case split
      should use `caseSplit` instead so trace extraction can see the
      induced substitution. Generic unfolds fit here too — the child
      node's `.sequent` carries the unfolded form, which the trace
      extractor compares against the ancestor directly. -/
  | node (label : String) (seq : Sequent) (rule : String) (children : List ProofTree)
  /-- A case split on variable `var`. Each case gives a constructor-pattern
      SubjectTerm `pat` (typically `.ctor c [.var x', …]`) and a subproof
      for the specialised sequent where `var` has been replaced by `pat`.
      Distinct from `node` because trace extraction walks into each branch
      with the extra binding `var ↦ pat` composed into the path substitution. -/
  | caseSplit (label : String) (seq : Sequent) (var : String)
              (cases : List (SubjectTerm × ProofTree))
  /-- A back-edge: the current sequent is an instance of the ancestor's
      sequent under `σ` (which instantiates the ancestor's free variables). -/
  | back (label : String) (seq : Sequent) (ancestor : String) (σ : Subst)
         (closeTactic : Option String := none)
  /-- An intermediate-lemma step: introduce `haveName : haveTypeStr` proved
      by `haveProofStr`, then continue with `continuation`. The Lean
      analogue is `have h : T := by tac; <rest>` in tactic mode.

      `haveTypeStr` and `haveProofStr` are stored as raw Lean source
      strings rather than `SubjectTerm` / structured tactics: a `have`
      in a cyclic proof typically introduces facts that are *outside*
      the cyclic-proof model (arithmetic identities, instances of side
      lemmas, etc.) — pretending to model them structurally would force
      a much richer term language without buying anything. The
      translator pastes these strings into the emitted Lean. Soundness
      of the cut is checked when the kernel rechecks the emitted def.

      Trace extraction passes through `.haveStep` (a have doesn't
      case-split, doesn't substitute root variables, and isn't a target
      for back-edges); the SCT analysis sees only the continuation. -/
  | haveStep (label : String) (seq : Sequent) (haveName : String)
             (haveTypeStr : String) (haveProofStr : String)
             (continuation : ProofTree)
  /-- An existential-witness step (∃R): for a goal `∃x, φ`, provide
      `witnessStr` and continue proving `φ[witnessStr/x]`. The Lean
      emission is `refine ⟨<witness>, ?_⟩` followed by the continuation's
      translation. Like `.haveStep`, this is a *logical* step — it
      doesn't case-split, doesn't substitute root variables, and isn't a
      target for back-edges. Trace extraction passes through. -/
  | existsStep (label : String) (seq : Sequent) (witnessStr : String)
               (continuation : ProofTree)
  deriving Inhabited

namespace ProofTree

def label : ProofTree → String
  | .leaf lbl _ _ _ => lbl
  | .identity lbl _ => lbl
  | .node lbl _ _ _ => lbl
  | .caseSplit lbl _ _ _ => lbl
  | .back lbl _ _ _ _ => lbl
  | .haveStep lbl _ _ _ _ _ => lbl
  | .existsStep lbl _ _ _ => lbl

def sequent : ProofTree → Sequent
  | .leaf _ s _ _ => s
  | .identity _ s => s
  | .node _ s _ _ => s
  | .caseSplit _ s _ _ => s
  | .back _ s _ _ _ => s
  | .haveStep _ s _ _ _ _ => s
  | .existsStep _ s _ _ => s

/-- Collect every `(backLabel, ancestorLabel)` pair in the tree. -/
partial def backEdges : ProofTree → List (String × String)
  | .leaf _ _ _ _ => []
  | .identity _ _ => []
  | .node _ _ _ cs => cs.flatMap backEdges
  | .caseSplit _ _ _ cases => cases.flatMap fun (_, t) => backEdges t
  | .back lbl _ anc _ _ => [(lbl, anc)]
  | .haveStep _ _ _ _ _ cont => backEdges cont
  | .existsStep _ _ _ cont => backEdges cont

end ProofTree

/-! ### Stage 2: automatic trace extraction

Implements Brotherston's trace condition (PhD thesis 2006, §5.3) by
recording, for each back-edge `B → A`, how A's argument positions
relate to B's after the path's case-split substitutions. The structural-
subterm comparison (`SubjectTerm.strictSubterm` for strict edges,
`SubjectTerm.structEq` for non-strict) is the trace-progress relation;
LJBA's size-change framework then decides whether the resulting graphs
satisfy the global trace condition.

For each back-edge `B → A`, walk the path from the root, accumulating
every case-split binding into a path substitution `σ_path`. At the
back-edge, instantiate the ancestor's sequent under `σ_path` and
compare it occurrence-by-occurrence to the back-edge's sequent.

### Vertex flattening

A vertex in the emitted `SCGraph` corresponds to one arg-position of one
formula in a sequent. Flat indices are assigned in the order
`antecedent formulas first (in sequent order), then succedent formulas`
and within each formula by arg position. The SCGraph's `dom` is the
total arg-slot count of A's sequent, `codom` the total for B's.

### Edge emission

Edges are emitted only between **matched** occurrence pairs: same side,
same formula index, same predicate, same arity. Within a matched pair,
for every ancestor arg-slot `i` and back arg-slot `j`:

  * if B's arg `j` is structurally equal to A's arg `i` (after σ_path),
    emit `i -≥→ j`;
  * if B's arg `j` is a strict subterm of A's arg `i` (after σ_path),
    emit `i -→ j`;
  * otherwise no edge.

Cross-occurrence matches are deliberately suppressed so spurious strict
edges between unrelated formulas don't make the multi-SCT check pass
vacuously.
-/

/-- Emit per-arg edges for a single matched occurrence pair, offset into
    the flat vertex space by `(aOff, bOff)`. -/
def occEdges (aArgs bArgs : List SubjectTerm) (aOff bOff : Nat) : List SCEdge :=
  (List.range aArgs.length).flatMap fun i =>
    (List.range bArgs.length).filterMap fun j =>
      match aArgs[i]?, bArgs[j]? with
      | some ai, some bj =>
        if SubjectTerm.structEq bj ai then some ⟨aOff + i, bOff + j, .nonstrict⟩
        else if SubjectTerm.strictSubterm bj ai then some ⟨aOff + i, bOff + j, .strict⟩
        else none
      | _, _ => none

/-- Walk two parallel formula lists, emitting edges for matched occurrences
    and accumulating arg-slot offsets along the way. -/
partial def occPairsLoop :
    List Formula → List Formula → Nat → Nat → List SCEdge
  | [], _, _, _ => []
  | _, [], _, _ => []
  | af :: aRest, bf :: bRest, aOff, bOff =>
    let here :=
      if af.pred == bf.pred && af.args.length == bf.args.length then
        occEdges af.args bf.args aOff bOff
      else []
    here ++ occPairsLoop aRest bRest (aOff + af.args.length) (bOff + bf.args.length)

/-- Sum arg-counts of a list of formulas. -/
def formulasArity (fs : List Formula) : Nat :=
  (fs.map (·.args.length)).foldl (· + ·) 0

/-- Build the trace graph comparing an instantiated ancestor sequent to
    a back-edge sequent, occurrence-by-occurrence, arg-by-arg. -/
def buildTraceGraph (aSeq bSeq : Sequent) (pathSubst : Subst) : SCGraph :=
  let aAnt := aSeq.antecedents.map (Formula.subst pathSubst)
  let aSuc := aSeq.succedents.map (Formula.subst pathSubst)
  let aAntTotal := formulasArity aAnt
  let bAntTotal := formulasArity bSeq.antecedents
  let aTotal := aAntTotal + formulasArity aSuc
  let bTotal := bAntTotal + formulasArity bSeq.succedents
  let antEdges := occPairsLoop aAnt bSeq.antecedents 0 0
  let sucEdges := occPairsLoop aSuc bSeq.succedents aAntTotal bAntTotal
  { dom := aTotal, codom := bTotal, edges := antEdges ++ sucEdges }

/-- Walk `t` while tracking the chain of enclosing ancestors (each with
    the substitution built up on the path from that ancestor to here),
    and produce one `SCGraph` per back-edge. -/
partial def extractTraceSCGsAux
    (ancestors : List (String × Sequent × Subst)) :
    ProofTree → List SCGraph
  | .leaf _ _ _ _ => []
  | .identity _ _ => []
  | .node lbl seq _ children =>
    let ancestors' := (lbl, seq, []) :: ancestors
    children.flatMap (extractTraceSCGsAux ancestors')
  | .caseSplit lbl seq var cases =>
    let ancestors' := (lbl, seq, []) :: ancestors
    cases.flatMap fun (pat, sub) =>
      -- Extend every ancestor's path substitution with `var ↦ pat`.
      let extended := ancestors'.map fun (l, s, σ) => (l, s, (var, pat) :: σ)
      extractTraceSCGsAux extended sub
  | .back _ bSeq anc _ _ =>
    match ancestors.find? (fun (l, _, _) => l == anc) with
    | none => []  -- dangling back-edge; ignore
    | some (_, aSeq, pathSubst) =>
      [buildTraceGraph aSeq bSeq pathSubst]
  | .haveStep _ _ _ _ _ cont =>
    -- A `have` doesn't contribute to traces (it's not a case-split,
    -- doesn't substitute root vars, isn't a back-edge target). Trace
    -- extraction looks straight through to the continuation.
    extractTraceSCGsAux ancestors cont
  | .existsStep _ _ _ cont =>
    -- Likewise for `exists`: the existential witness is a logical step,
    -- not a case-split or back-edge. Trace extraction descends to the
    -- continuation unchanged.
    extractTraceSCGsAux ancestors cont

/-- Entry point: one `SCGraph` per back-edge in the tree. -/
def extractTraceSCGs (t : ProofTree) : List SCGraph :=
  extractTraceSCGsAux [] t

/-! ### Labeled trace extraction

Pairs each emitted trace SCG with the back-edge's label. Used by the
annotation pass (`Cyclic.Annotation`) to attribute progressing-name
choices back to specific back-edges in diagnostics and emitted code. -/

partial def extractTraceSCGsLabeledAux
    (ancestors : List (String × Sequent × Subst)) :
    ProofTree → List (String × SCGraph)
  | .leaf _ _ _ _ => []
  | .identity _ _ => []
  | .node lbl seq _ children =>
    let ancestors' := (lbl, seq, []) :: ancestors
    children.flatMap (extractTraceSCGsLabeledAux ancestors')
  | .caseSplit lbl seq var cases =>
    let ancestors' := (lbl, seq, []) :: ancestors
    cases.flatMap fun (pat, sub) =>
      let extended := ancestors'.map fun (l, s, σ) => (l, s, (var, pat) :: σ)
      extractTraceSCGsLabeledAux extended sub
  | .back lbl bSeq anc _ _ =>
    match ancestors.find? (fun (l, _, _) => l == anc) with
    | none => []
    | some (_, aSeq, pathSubst) =>
      [(lbl, buildTraceGraph aSeq bSeq pathSubst)]
  | .haveStep _ _ _ _ _ cont =>
    extractTraceSCGsLabeledAux ancestors cont
  | .existsStep _ _ _ cont =>
    extractTraceSCGsLabeledAux ancestors cont

def extractTraceSCGsLabeled (t : ProofTree) : List (String × SCGraph) :=
  extractTraceSCGsLabeledAux [] t

end Cyclic.Proof
