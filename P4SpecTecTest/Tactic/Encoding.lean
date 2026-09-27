import P4SpecTec.Tactic.Encoding
import P4SpecTec.Tactic.Refine.ForwardRules
import P4SpecTec.Tactic.Audit
import P4SpecTec.Runtime.Value.Value

/-! Nested encoder transport and rejection of a non-map recursive helper. -/

namespace P4SpecTecTest.Tactic.Encoding

open Lean Elab Tactic P4SpecTec.Lang.Il

namespace Nested

inductive Tree where
  | leaf : Nat → Tree
  | children : List Tree → Tree

mutual

def Tree.toValue : Tree → value
  | .leaf n => P4SpecTec.Runtime.Value.Make.nat n
  | .children nodes => P4SpecTec.Runtime.Value.Make.list .TextT (Tree.toValue_0 nodes)

def Tree.toValue_0 : List Tree → List value
  | [] => []
  | x :: xs => Tree.toValue x :: Tree.toValue_0 xs

end

end Nested

-- A symbolic recursive list encoder must remain opaque during ordinary normalization.
-- Its unconditional eq_def expands under its own branches without making progress.
example (xs : List Nested.Tree) (P : List value → Prop) (h : P (Nested.Tree.toValue_0 xs)) :
    P (Nested.Tree.toValue_0 xs) := by
  run_tac
    let rules ← P4SpecTec.Tactic.valueConstants `P4SpecTecTest.Tactic.Encoding.Nested
    let _ ← P4SpecTec.Tactic.normalize { lemmas := rules.toArray, procs := #[] }
  exact h

elab "prove_encoder_map" : tactic => withoutRecover do
  P4SpecTec.Tactic.encodingFacts `P4SpecTecTest.Tactic.Encoding.Nested
  evalTactic (← `(tactic| simp only [*]))

theorem nestedListMap (xs : List Nested.Tree) :
    Nested.Tree.toValue_0 xs = xs.map Nested.Tree.toValue := by
  prove_encoder_map

/-- info: 'P4SpecTecTest.Tactic.Encoding.nestedListMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nestedListMap
#audit_axioms nestedListMap

elab "prove_encoder_lengths" : tactic => withoutRecover do
  P4SpecTec.Tactic.encodingLengths
  let _ ← P4SpecTec.Tactic.normalize { lemmas := #[], procs := #[] }
  unless (← getGoals).isEmpty do throwError "encoded lengths did not normalize the goal"

theorem relatedLength (vs : List value) (xs : List Nested.Tree)
    (h : P4SpecTec.Refine.canons vs = P4SpecTec.Refine.canons (xs.map Nested.Tree.toValue)) :
    vs.length = xs.length := by
  prove_encoder_lengths

/-- info: 'P4SpecTecTest.Tactic.Encoding.relatedLength' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relatedLength
#audit_axioms relatedLength

elab "close_encoded_shape" : tactic => withoutRecover do
  let rules : P4SpecTec.Tactic.SimpSet := {
    lemmas := #[``P4SpecTec.Refine.canon_mk, ``P4SpecTec.Refine.canon'], procs := #[] }
  let _ ← P4SpecTec.Tactic.normalize rules
  if (← getGoals).isEmpty then throwError "regression did not require a compound payload fact"
  P4SpecTec.Tactic.encodingShapes
  P4SpecTec.Tactic.encodingShapes
  P4SpecTec.Tactic.normalizeFacts rules
  evalTactic (← `(tactic| contradiction))
  unless (← getGoals).isEmpty do throwError "encoded payload contradiction remains\n{← getMainGoal}"

theorem compoundPayload (encode : Nat → value) (n : Nat) (payload : value')
    (note : vnote) (region : P4SpecTec.Util.Source.region)
    (rf_h : (encode n).it = payload)
    (rf_c_guard : P4SpecTec.Refine.canon (encode n) ≠
      P4SpecTec.Refine.canon ⟨payload, note, region⟩) : False := by
  close_encoded_shape

/-- info: 'P4SpecTecTest.Tactic.Encoding.compoundPayload' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compoundPayload
#audit_axioms compoundPayload

namespace Broken

def toValue_0 : List Nat → List value
  | [] => []
  | x :: _ => [P4SpecTec.Runtime.Value.Make.nat x]

end Broken

elab "propose_broken_encoder" : tactic => withoutRecover do
  P4SpecTec.Tactic.encodingFacts `P4SpecTecTest.Tactic.Encoding.Broken

example : True := by
  fail_if_success propose_broken_encoder
  trivial

end P4SpecTecTest.Tactic.Encoding
