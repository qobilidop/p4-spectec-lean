import NanoP4Spec.«8.04-eval-lvalue»

/-!
A total first-match field update, connected to the actual generated Nano-P4 function.
The domain includes every generated value and field name, including duplicate field names.
Replacement values are already evaluated; this interface makes no claim about expression effects.
-/

namespace ExampleProofs.NanoP4FieldUpdate

open NanoP4Spec P4SpecTec P4SpecTec.Prelude

/-- The name of one generated field. -/
def fieldName : fieldValue → nameIR
  | .semi _ name => name

/-- Field names in their original order, with duplicates retained. -/
def names (fields : List fieldValue) : List nameIR := fields.map fieldName

/-- Generated name comparison is exact equality of byte strings. -/
theorem nameEq (left right : nameIR) : (left == right) = true ↔ left = right := by
  unfold BEq.beq NanoP4Spec.instBEqTypeId valueEq
  simp only [ToValue.toValue, NanoP4Spec.typeId.toValue, NanoP4Spec.nameIR.toValue,
    NanoP4Spec.callableId.toValue, NanoP4Spec.id.toValue, Runtime.Value.eq,
    Runtime.Value.Make.text, Runtime.Value.Make.mk, Runtime.Value.compare,
    Runtime.Value.compare']
  simp only [beq_iff_eq]
  exact ByteText.compare_eq_iff_eq left right

/-- info: 'ExampleProofs.NanoP4FieldUpdate.nameEq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nameEq

/-- Replace only the first matching field, retaining every later field verbatim.
If the name is absent, the original list is returned. -/
def update : List fieldValue → nameIR → value → List fieldValue
  | [], _, _ => []
  | .semi old stored :: tail, name, replacement =>
    if stored == name then .semi replacement name :: tail
    else .semi old stored :: update tail name replacement

/-- The actual generated partial-fixpoint function always terminates successfully and
returns precisely the total first-match update, for every generated field list. -/
theorem generatedEqUpdate (fields : List fieldValue) (name : nameIR) (replacement : value) :
    NanoP4Spec.«$update_fieldValue» fields name replacement =
      some (.ok (update fields name replacement)) := by
  induction fields with
  | nil =>
    rw [NanoP4Spec.«$update_fieldValue».eq_def]
    rfl
  | cons field tail ih =>
    cases field with
    | semi old stored =>
      rw [NanoP4Spec.«$update_fieldValue».eq_def]
      cases h : (stored == name) <;>
        simp only [update, bne, h, ih] <;> rfl

/-- info: 'ExampleProofs.NanoP4FieldUpdate.generatedEqUpdate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms generatedEqUpdate

end ExampleProofs.NanoP4FieldUpdate
