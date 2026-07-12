import CyclicTactic.ProofTree
import CyclicTactic.SizeChange

/-!
# Phase-aware size-change extraction (GAP 2)

The size-change extractor in `ProofTree.lean` only sees descent that shows up
as a structural sub-term relation between an ancestor arg and a bud arg
(`structEq` / `strictSubterm`). A **finite-domain** argument — one whose value
is a nullary constructor of a finite type (`Bool`, an enum, …) — carries
*well-founded progress* when the cycle drives it through a fixed constructor
order, but the structural comparison sees only "two distinct nullary ctors",
emits no edge, and the position looks like stagnation. This is exactly why a
Sprenger–Dam two-step proof (progress in a `Bool` phase, e.g. `f_total`) fails
the SCT gate before emission (see wf-notes/GAP1-FINDINGS.md, tier T2).

This module recovers that progress. The phase order is **derived, not
guessed**: a back-edge whose `SCGraph` has *no* structural strict self-loop is
"stalled" — to be sound it MUST make progress in a phase, so its finite-domain
constructor transition `c_from ⟶ c_to` is *required* to be strictly decreasing
(`c_from > c_to`). Collect those requirements across all back-edges; if they
admit a consistent strict order on the constructors (i.e. the requirement graph
is acyclic — a genuinely non-terminating phase cycle like `false→true→false`
with progress nowhere else is correctly REJECTED here), we patch a strict
self-loop into each stalled graph at the phase position and hand a per-position
constructor→rank map to the emitter.

Soundness is not at stake: the patch only PROPOSES a measure; Lean's kernel
re-checks the emitted `termination_by`/`decreasing_by`, so an over-eager patch
can at worst be rejected (→ recursive fallback), never produce a wrong proof.

The whole downstream — `checkMultiSCT`, `synthMeasure`, WFEmit — already works
on phase-augmented graphs (verified by `#eval` probe); this module only fills
the extraction hole.
-/

namespace CyclicTactic.Proof

/-- A recorded finite-domain transition on one back-edge: the flat arg
    position, the ancestor's constructor, and the bud's constructor. Both are
    nullary constructors and distinct. -/
structure PhaseTransition where
  pos  : Nat
  src : String
  dst : String
  deriving Repr, BEq, Inhabited

/-- A subject term that is a nullary constructor (`Bool.true`, an enum case…). -/
def SubjectTerm.asNullaryCtor : SubjectTerm → Option String
  | .ctor n [] => some n
  | _          => none

/-- Diagonal finite-domain transitions for one matched formula list pair.
    Mirrors `occPairsLoop`'s offset accounting but only the DIAGONAL (arg `k`
    of the ancestor vs arg `k` of the bud) — a strict self-loop lives at a
    single flat position `p`, so only diagonal transitions can patch one. We
    emit a transition only when the ancestor and bud offsets coincide
    (`aOff == bOff`, true when preceding antecedent arities match), keeping the
    flat position unambiguous; mismatches are skipped (conservative, sound). -/
partial def phaseTransPairsLoop :
    List Formula → List Formula → Nat → Nat → List PhaseTransition
  | [], _, _, _ => []
  | _, [], _, _ => []
  | af :: aRest, bf :: bRest, aOff, bOff =>
    let here : List PhaseTransition :=
      if af.pred == bf.pred && af.args.length == bf.args.length && aOff == bOff then
        (List.range af.args.length).filterMap fun k =>
          match af.args[k]?, bf.args[k]? with
          | some a, some b =>
            match a.asNullaryCtor, b.asNullaryCtor with
            | some ca, some cb => if ca == cb then none else some { pos := aOff + k, src := ca, dst := cb }
            | _, _ => none
          | _, _ => none
      else []
    here ++ phaseTransPairsLoop aRest bRest (aOff + af.args.length) (bOff + bf.args.length)

/-- Phase transitions for a back-edge, comparing the instantiated ancestor
    sequent to the bud sequent. Parallels `buildTraceGraph`. -/
def buildPhaseTransitions (aSeq bSeq : Sequent) (pathSubst : Subst) : List PhaseTransition :=
  let aAnt := aSeq.antecedents.map (Formula.subst pathSubst)
  let aSuc := aSeq.succedents.map (Formula.subst pathSubst)
  let aAntTotal := formulasArity aAnt
  let bAntTotal := formulasArity bSeq.antecedents
  phaseTransPairsLoop aAnt bSeq.antecedents 0 0
    ++ phaseTransPairsLoop aSuc bSeq.succedents aAntTotal bAntTotal

/-- Labeled phase-transition extraction, paralleling
    `extractTraceSCGsLabeledAux` so positions line up with the labeled SCGs. -/
partial def extractPhaseTransAux
    (ancestors : List (String × Sequent × Subst)) :
    ProofTree → List (String × List PhaseTransition)
  | .leaf _ _ _ _ => []
  | .identity _ _ => []
  | .node lbl seq _ children =>
    let ancestors' := (lbl, seq, []) :: ancestors
    children.flatMap (extractPhaseTransAux ancestors')
  | .caseSplit lbl seq var cases =>
    let ancestors' := (lbl, seq, []) :: ancestors
    cases.flatMap fun (pat, sub) =>
      let extended := ancestors'.map fun (l, s, σ) => (l, s, (var, pat) :: σ)
      extractPhaseTransAux extended sub
  | .dCaseSplit lbl seq _ _ pos neg =>
    let ancestors' := (lbl, seq, []) :: ancestors
    extractPhaseTransAux ancestors' pos ++ extractPhaseTransAux ancestors' neg
  | .back lbl bSeq anc _ _ =>
    match ancestors.find? (fun (l, _, _) => l == anc) with
    | none => []
    | some (_, aSeq, pathSubst) => [(lbl, buildPhaseTransitions aSeq bSeq pathSubst)]
  | .haveStep _ _ _ _ _ cont => extractPhaseTransAux ancestors cont
  | .existsStep _ _ _ cont   => extractPhaseTransAux ancestors cont

def extractPhaseTrans (t : ProofTree) : List (String × List PhaseTransition) :=
  extractPhaseTransAux [] t

/-! ### Phase-order solver -/

/-- Topologically rank constructor names from a set of strict requirements
    `c_from > c_to` (each pair means `from` must outrank `to`). Returns a
    `name → rank` map with `rank from > rank to` for every requirement, or
    `none` if the requirements are cyclic (no consistent strict order — a
    genuinely non-well-founded phase cycle). Ranks are arbitrary naturals
    respecting the order; the measure only needs relative comparison.

    Implementation: repeatedly peel a "sink" (a ctor that is never a `from`,
    i.e. nothing is required to be below... — we peel MINIMA: a ctor that is
    never a `to`, assign it the highest remaining rank). Fuel-bounded by the
    number of distinct names. -/
partial def rankConstructors (reqs : List (String × String)) : Option (List (String × Nat)) :=
  let names := (reqs.flatMap (fun (a, b) => [a, b])).eraseDups
  go names reqs names.length []
where
  go (remaining : List String) (reqs : List (String × String)) (fuel : Nat)
     (acc : List (String × Nat)) : Option (List (String × Nat)) :=
    match remaining with
    | [] => some acc
    | _  =>
      match fuel with
      | 0 => none  -- cyclic: couldn't peel everything
      | f + 1 =>
        -- A maximum: a name that is never a `to` among remaining requirements.
        let liveReqs := reqs.filter (fun (a, b) => remaining.contains a && remaining.contains b)
        let maxima := remaining.filter fun n => ¬ liveReqs.any (fun (_, b) => b == n)
        match maxima with
        | [] => none  -- every remaining name is dominated ⇒ cycle
        | _  =>
          -- Assign the current (high) rank to all maxima, then peel them.
          let rank := remaining.length  -- strictly decreasing as we peel
          let acc' := acc ++ maxima.map (fun n => (n, rank))
          let remaining' := remaining.filter (fun n => ¬ maxima.contains n)
          go remaining' reqs f acc'

/-- The result of phase analysis: SCGs patched with phase self-loops, plus a
    per-position constructor→rank map (for the emitter to render the phase
    component as a `match`). -/
structure PhaseResult where
  graphs : List SCGraph
  /-- `pos ↦ (ctorName ↦ rank)`. A position appears iff its phase order was
      solved; the emitter renders that position's measure component as a
      `match` on the binder using these ranks. -/
  ranks  : List (Nat × List (String × Nat))
  deriving Inhabited

/-- Phase-augment a labeled set of back-edge SCGs.

    1. A back-edge is *stalled* if its SCG has no strict self-loop — it needs a
       phase to make progress. For each stalled edge, every diagonal phase
       transition it has becomes a *required* strict decrease `from > to` at
       that position.
    2. Per position, rank the constructors from the required transitions
       (`rankConstructors`); skip the position if cyclic.
    3. Patch: for every back-edge (stalled or not) with a transition `(from,to)`
       at a solved position `p`, add a strict self-loop `p→p` iff
       `rank from > rank to` (the phase strictly decreases); an increasing
       transition contributes nothing (the structural descent must carry it).

    Returns the patched graphs (in the input order, labels dropped) and the
    solved per-position rank maps. If no position solves, the graphs are
    returned unchanged and `ranks = []` (so behaviour is identical to the
    non-phase pipeline — no regression). -/
def phaseAugment (labeled : List (String × SCGraph))
    (phases : List (String × List PhaseTransition)) : PhaseResult :=
  let phaseOf := fun lbl => (phases.find? (·.1 == lbl)).map (·.2) |>.getD []
  -- (1) required constraints, grouped by position.
  let stalled := labeled.filter fun (_, g) => ¬ g.hasStrictSelfLoop
  let reqs : List (Nat × (String × String)) :=
    stalled.flatMap fun (lbl, _) =>
      (phaseOf lbl).map fun pt => (pt.pos, (pt.src, pt.dst))
  let positions := (reqs.map (·.1)).eraseDups
  -- (2) solve each position.
  let solved : List (Nat × List (String × Nat)) :=
    positions.filterMap fun p =>
      let posReqs := (reqs.filter (·.1 == p)).map (·.2)
      match rankConstructors posReqs with
      | some rk => some (p, rk)
      | none    => none
  -- (3) patch graphs.
  let rankAt := fun p c => (solved.find? (·.1 == p)).bind (fun (_, m) => (m.find? (·.1 == c)).map (·.2))
  let patched : List SCGraph := labeled.map fun (lbl, g) =>
    let extra : List SCEdge := (phaseOf lbl).filterMap fun pt =>
      match rankAt pt.pos pt.src, rankAt pt.pos pt.dst with
      | some rf, some rt => if rf > rt then some ⟨pt.pos, pt.pos, .strict⟩ else none
      | _, _ => none
    -- Avoid duplicate self-loops if one already exists.
    let newEdges := extra.filter fun e => ¬ g.edges.contains e
    { g with edges := g.edges ++ newEdges }
  { graphs := patched, ranks := solved }

end CyclicTactic.Proof
