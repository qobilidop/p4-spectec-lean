import NanoP4Proofs.FieldUpdate.Laws
import NanoP4Proofs.FieldUpdate.Correspondence

/-!
# Independent field writes commute

This checked walkthrough concerns the pinned Nano-P4 helper `update_fieldValue`,
used by struct/header member writes in `8.04-eval-lvalue.watsup`.

The input is an arbitrary finite ordered field list with scalar payloads:
unsigned/signed integer-literal shapes, booleans, and match-kind names. Widths
and integer payloads are not restricted by an invented range check. Names are
exact byte strings. Empty lists, absent names, and duplicates are allowed.

The operation replaces the **first** matching field. It does not insert absent
fields and does not change later duplicates. `generatedEqUpdate` connects the convenient
total interface to the actual generated partial-fixpoint function. `Laws`
proves its properties rather than treating that interface as a replacement
semantics.

The consumer property is a small reordering law: writes at distinct names
commute when both replacement values are already evaluated. This is not a
theorem permitting arbitrary P4 assignment statements to be reordered: their
right-hand-side expressions and lvalue evaluation can have dependencies or
effects. Nested payloads, packet/table objects, printing, and source parsing
are outside the scalar correspondence profile.
-/

namespace NanoP4Proofs.FieldUpdate

open P4SpecTec P4SpecTec.Prelude

/-- Two calls to the actual generated helper, not to the total proof interface. -/
def generatedWrites (fields : List NanoP4Spec.fieldValue) (left right : ByteText)
    (leftValue rightValue : NanoP4Spec.value) : Eval (List NanoP4Spec.fieldValue) := do
  let first ← ExceptT.mk (NanoP4Spec.«$update_fieldValue» fields left leftValue)
  ExceptT.mk (NanoP4Spec.«$update_fieldValue» first right rightValue)

/-!
## The generated consumer theorem

Only distinct names are required. There is no hidden uniqueness assumption on
the list, no assumption that either field occurs, and no termination premise.
The generated-operation totality theorem supplies termination on this domain.
-/

/-- Independent scalar writes commute as actual generated computations. -/
theorem independentWritesCommute (fields : List Field) (left right : ByteText)
    (leftValue rightValue : Scalar) (different : left ≠ right) :
    (generatedWrites (generatedFields fields) left right
      leftValue.generated rightValue.generated).run =
    (generatedWrites (generatedFields fields) right left
      rightValue.generated leftValue.generated).run :=
  generatedCommute _ _ _ _ _ different

/-- info: 'NanoP4Proofs.FieldUpdate.independentWritesCommute' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms independentWritesCommute

/-!
## Boundary examples

These checked statements demonstrate why "first" and "absent" matter. The
second duplicate below is preserved even when its payload differs. An absent
name is a no-op; that behavior is deliberately not map insertion.
-/

/-- A later duplicate is untouched by the first matching update. -/
theorem duplicateExample (name : ByteText) (first later replacement : Scalar) :
    update [.semi first.generated name, .semi later.generated name]
      name replacement.generated =
    [.semi replacement.generated name, .semi later.generated name] :=
  updateHead _ _ _ _

/-- info: 'NanoP4Proofs.FieldUpdate.duplicateExample' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duplicateExample

/-- An absent field is not appended to the list. -/
theorem absentExample (stored missing : ByteText) (old replacement : Scalar)
    (different : stored ≠ missing) :
    update [.semi old.generated stored] missing replacement.generated =
      [.semi old.generated stored] := by
  rw [updateConsOfNe _ _ _ _ _ different, updateNil]

/-- info: 'NanoP4Proofs.FieldUpdate.absentExample' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms absentExample

/-!
## The reference boundary

The following entry point runs the actual quoted helper in the concrete,
successfully initialized Nano environment. Guards and debug tracing are off;
there are no extern implementations or local callback overrides. Fuel is an
interpreter resource, not part of the field-update result. At insufficient
fuel, no semantic outcome is claimed.
-/


/-!
`Environment.initEqOk` proves initialization succeeds; `referenceRealizes`
constructs a successful run of the actual AL helper. Its internal list induction
uses fuel `7 * length + 33`, with arbitrary input notes. `referenceSound`
also rules out terminating failures on related inputs. Together,
`referenceObservesIff` gives the exact observable result of two reference calls.

The composition passes the actual first output to the second call. Each call
may use its own finite fuel budget; observations erase only source annotations.
The existence theorem below makes the final equivalence non-vacuous.

Trust boundary: these are Lean kernel-checked proofs about the generated model
and the Lean AL reference. The normal quotation check verifies that all 342
quoted definitions match the pinned export; it is not a proof of the upstream
exporter, the source parser, or the OCaml-to-Lean interpreter port.
-/

/-- The reference consumer has an observation for every supported source input. -/
theorem referenceWritesExist (rawFields : Lang.Il.value) (source : SourceFields rawFields)
    (left right : ByteText) (leftValue rightValue : Scalar) :
    ∃ observation, ReferenceObserves rawFields left right leftValue rightValue observation := by
  obtain ⟨fields, hfields⟩ := fieldsCoverage source
  obtain ⟨firstFuel, secondFuel, output, hrun, _⟩ :=
    referenceWritesRealize fields rawFields hfields left right leftValue rightValue
  exact ⟨Refine.canon output, firstFuel, secondFuel, output, hrun, rfl⟩

/-- info: 'NanoP4Proofs.FieldUpdate.referenceWritesExist' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceWritesExist

/-- Distinct, already-evaluated scalar writes commute in the actual reference execution.
The source-domain premise is independent of the generated encoder. -/
theorem independentReferenceWritesCommute
    (rawFields : Lang.Il.value) (source : SourceFields rawFields)
    (left right : ByteText) (leftValue rightValue : Scalar) (different : left ≠ right)
    (observation : Lang.Il.value) :
    ReferenceObserves rawFields left right leftValue rightValue observation ↔
      ReferenceObserves rawFields right left rightValue leftValue observation := by
  obtain ⟨fields, hfields⟩ := fieldsCoverage source
  rw [referenceObservesIff fields rawFields hfields,
    referenceObservesIff fields rawFields hfields,
    updateCommute _ left right leftValue.generated rightValue.generated different]

/-- info: 'NanoP4Proofs.FieldUpdate.independentReferenceWritesCommute' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms independentReferenceWritesCommute

end NanoP4Proofs.FieldUpdate
