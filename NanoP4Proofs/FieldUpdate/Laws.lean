import NanoP4Proofs.FieldUpdate.Semantics
import NanoP4Proofs.FieldUpdate.Representation

/-!
First-match laws for the generated Nano-P4 field update, including duplicate names.
Commutation concerns distinct names and already evaluated replacement values; it does not
reorder expression evaluation or claim that arbitrary P4 assignment statements commute.
-/

namespace NanoP4Proofs.FieldUpdate

open NanoP4Spec P4SpecTec P4SpecTec.Prelude

/-- Updating an empty field list leaves it empty. -/
theorem updateNil (name : nameIR) (replacement : value) :
    update [] name replacement = [] := rfl

/-- info: 'NanoP4Proofs.FieldUpdate.updateNil' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updateNil

/-- A matching head is replaced and the complete tail is left untouched. -/
theorem updateHead (old replacement : value) (name : nameIR) (tail : List fieldValue) :
    update (.semi old name :: tail) name replacement = .semi replacement name :: tail := by
  simp [update, nameEq]

/-- info: 'NanoP4Proofs.FieldUpdate.updateHead' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updateHead

/-- A differently named head is retained and the search continues in the tail. -/
theorem updateConsOfNe (old replacement : value) (stored name : nameIR)
    (tail : List fieldValue) (h : stored ≠ name) :
    update (.semi old stored :: tail) name replacement =
      .semi old stored :: update tail name replacement := by
  simp [update, nameEq, h]

/-- info: 'NanoP4Proofs.FieldUpdate.updateConsOfNe' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updateConsOfNe

/-- Updating preserves all field names, their order, and their multiplicities. -/
theorem updateNames (fields : List fieldValue) (name : nameIR) (replacement : value) :
    names (update fields name replacement) = names fields := by
  induction fields with
  | nil => rfl
  | cons field tail ih =>
    cases field with
    | semi old stored =>
      by_cases h : stored = name
      · subst stored
        simp [updateHead, names, fieldName]
      · simp only [updateConsOfNe old replacement stored name tail h]
        exact congrArg (stored :: ·) ih

/-- info: 'NanoP4Proofs.FieldUpdate.updateNames' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updateNames

/-- Updating neither inserts nor removes a field. -/
theorem updateLength (fields : List fieldValue) (name : nameIR) (replacement : value) :
    (update fields name replacement).length = fields.length := by
  simpa only [names, List.length_map] using
    congrArg List.length (updateNames fields name replacement)

/-- info: 'NanoP4Proofs.FieldUpdate.updateLength' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updateLength

/-- Updating an absent name is exactly the identity, including payloads. -/
theorem updateOfAbsent (fields : List fieldValue) (name : nameIR) (replacement : value)
    (absent : name ∉ names fields) : update fields name replacement = fields := by
  induction fields with
  | nil => rfl
  | cons field tail ih =>
    cases field with
    | semi old stored =>
      have different : stored ≠ name := by
        intro h
        apply absent
        simp [names, fieldName, h]
      have tailAbsent : name ∉ names tail := by
        intro h
        apply absent
        exact List.mem_cons_of_mem stored h
      rw [updateConsOfNe old replacement stored name tail different, ih tailAbsent]

/-- info: 'NanoP4Proofs.FieldUpdate.updateOfAbsent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updateOfAbsent

/-- A prefix without the target is preserved; the first matching field is replaced once. -/
theorem updateFirst (front suffix : List fieldValue) (name : nameIR)
    (old replacement : value) (absent : name ∉ names front) :
    update (front ++ .semi old name :: suffix) name replacement =
      front ++ .semi replacement name :: suffix := by
  induction front with
  | nil => exact updateHead old replacement name suffix
  | cons field front ih =>
    cases field with
    | semi payload stored =>
      have different : stored ≠ name := by
        intro h
        apply absent
        simp [names, fieldName, h]
      have tailAbsent : name ∉ names front := by
        intro h
        apply absent
        exact List.mem_cons_of_mem stored h
      simp only [List.cons_append, updateConsOfNe payload replacement stored name _ different,
        ih tailAbsent]

/-- info: 'NanoP4Proofs.FieldUpdate.updateFirst' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updateFirst

/-- Updates at distinct names commute, even when either name occurs more than once. -/
theorem updateCommute (fields : List fieldValue) (left right : nameIR)
    (leftValue rightValue : value) (different : left ≠ right) :
    update (update fields left leftValue) right rightValue =
      update (update fields right rightValue) left leftValue := by
  induction fields with
  | nil => rfl
  | cons field tail ih =>
    cases field with
    | semi old stored =>
      by_cases hl : stored = left
      · subst stored
        simp [updateHead, updateConsOfNe, different]
      · by_cases hr : stored = right
        · subst stored
          simp [updateHead, updateConsOfNe, hl]
        · simp only [updateConsOfNe old leftValue stored left tail hl,
            updateConsOfNe old rightValue stored right _ hr,
            updateConsOfNe old leftValue stored left _ hl, ih]

/-- info: 'NanoP4Proofs.FieldUpdate.updateCommute' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms updateCommute

/-- Sequential calls to the actual generated function commute at distinct field names. -/
theorem generatedCommute (fields : List fieldValue) (left right : nameIR)
    (leftValue rightValue : value) (different : left ≠ right) :
    (do
      let first ← ExceptT.mk (NanoP4Spec.«$update_fieldValue» fields left leftValue)
      ExceptT.mk (NanoP4Spec.«$update_fieldValue» first right rightValue) :
      Eval (List fieldValue)).run =
    (do
      let first ← ExceptT.mk (NanoP4Spec.«$update_fieldValue» fields right rightValue)
      ExceptT.mk (NanoP4Spec.«$update_fieldValue» first left leftValue) :
      Eval (List fieldValue)).run := by
  simp only [generatedEqUpdate]
  change (some (.ok (update (update fields left leftValue) right rightValue)) :
      Option (Except Fail (List fieldValue))) =
    some (.ok (update (update fields right rightValue) left leftValue))
  rw [updateCommute fields left right leftValue rightValue different]

/-- info: 'NanoP4Proofs.FieldUpdate.generatedCommute' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms generatedCommute

/-- First-match update within the independently specified scalar-field source profile. -/
def updateFields : List Field → ByteText → Scalar → List Field
  | [], _, _ => []
  | field :: tail, name, replacement =>
    if field.name == name then ⟨replacement, name⟩ :: tail
    else field :: updateFields tail name replacement

/-- Source-profile updating represents the general generated-value update exactly. -/
theorem generatedFieldsUpdate (fields : List Field) (name : ByteText) (replacement : Scalar) :
    generatedFields (updateFields fields name replacement) =
      update (generatedFields fields) name replacement.generated := by
  induction fields with
  | nil => rfl
  | cons field tail ih =>
    cases field with
    | mk payload stored =>
      cases h : (stored == name) <;>
        simp [updateFields, generatedFields, Field.generated, update, h] at ih ⊢
      exact ih

/-- info: 'NanoP4Proofs.FieldUpdate.generatedFieldsUpdate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms generatedFieldsUpdate

end NanoP4Proofs.FieldUpdate
