import Cyclic.ProofTree

/-!
# Stage 3: unravelling a validated cyclic proof into a Lean tactic script

Consumes a `ProofTree` and emits a Lean 4 theorem (as a `String`) that
proves the sequent by well-founded induction on the case-split variable.

The emitted script is eyeball-verified and copy-paste-able; wrapping
this in an actual command macro (`cyclic_thm`) is a later step.

## Scope

Supports exactly the shape of the toy `∀ x : Nat, P(x)` derivation:

  * Root = `.caseSplit` on one variable of type `Nat`.
  * Each case's subtree is either:
    - a `.leaf`              → emit `simp [<leanPred>]`.
    - a `.node [.back … root]` → emit `simp [<leanPred>]; exact ih`.
    - a bare `.back … root`   → emit `exact ih`.
  * The user supplies the Lean-side predicate's name (`leanPred`) and
    the theorem's name. The predicate must exist on the Lean side with
    signature `leanPred : Nat → Prop` and unfold equations that match
    the abstract `P(0) ⇔ ⊤` / `P(succ x) ⇔ P(x)` the proof tree relies on.

Anything outside this shape falls back to a `sorry` stub so the emitted
script still parses, making it easy to see which part generalised and
which part didn't.
-/

namespace Cyclic.Unravel

open Cyclic.Proof

/-- Turn a constructor pattern into the `induction … with`-case header,
    plus whether it binds an induction hypothesis. -/
def patToInductionCase : SubjectTerm → Option (String × Bool)
  | .ctor "zero" []        => some ("zero", false)
  | .ctor "succ" [.var n]  => some ("succ " ++ n, true)
  | _                      => none

/-- Translate the subtree under one `induction` case. -/
def translateSub (leanPred rootLabel : String) : ProofTree → String
  | .leaf _ _ _ =>
    "    simp [" ++ leanPred ++ "]"
  | .node _ _ _ [.back _ _ anc _] =>
    if anc == rootLabel then
      "    simp [" ++ leanPred ++ "]\n    exact ih"
    else
      "    sorry -- unsupported back target: " ++ anc
  | .back _ _ anc _ =>
    if anc == rootLabel then "    exact ih"
    else "    sorry -- unsupported back target: " ++ anc
  | _ =>
    "    sorry -- unsupported subtree shape"

/-- Emit a full Lean theorem from a proof tree. -/
def translate (leanPred thmName : String) : ProofTree → String
  | .caseSplit rootLbl _ var cases =>
    let arms := cases.filterMap fun (pat, sub) =>
      match patToInductionCase pat with
      | none => none
      | some (patTxt, hasIh) =>
        let ihPart := if hasIh then " ih" else ""
        some ("  | " ++ patTxt ++ ihPart ++ " =>\n"
              ++ translateSub leanPred rootLbl sub)
    let header := "theorem " ++ thmName ++ " (" ++ var ++ " : Nat) : "
                  ++ leanPred ++ " " ++ var ++ " := by"
    let body := "  induction " ++ var ++ " with\n"
                ++ String.intercalate "\n" arms
    header ++ "\n" ++ body
  | t =>
    "-- unsupported root (expected .caseSplit); got: " ++ t.label

end Cyclic.Unravel
