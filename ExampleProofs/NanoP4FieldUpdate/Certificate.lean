import ExampleProofs.NanoP4FieldUpdate.Correspondence
import ExampleProofs.NanoP4FieldUpdate.Laws

/-!
# Checked field-update certificate

`certificate` packages actual proof obligations for the pinned Nano-P4 helper,
not strings naming theorems. Its fields expose source coverage, observation
faithfulness, decoding, successful initialization, and both directions of
correspondence with the actual generated function. All terminating reference
outcomes are covered, including exclusion of failures on related inputs; the
reverse direction supplies finite fuel rather than assuming termination.

The declared source profile is `SourceFields` with `Scalar` replacements:
finite ordered lists, exact byte names, W/S/B/MATCH_KIND payloads, duplicates
and absent fields included. It is not a typing or numeric-range theorem.
The environment disables guards and has no local function overrides; printing,
externs, nested payloads and arbitrary assignment reordering are not certified.

The quoted definition is the actual `NanoP4Spec.«$update_fieldValue».al`, from
`8.04-eval-lvalue.watsup`. Membership below connects it to the successfully
initialized quoted spec. Source-file/export identity is a separate runtime
check: `check-quotes` compares every compiled quotation with the decoded pinned
export. The kernel certificate does not prove the exporter or the reference
interpreter port faithful to upstream OCaml.

Dependencies are proof terms, including the generated forward refinement and
the handwritten realization, representation and initialization theorems.
The axiom audit checks their transitive logical dependencies. This is one
bounded certificate, not a generator-wide coverage or dependency census.
-/

namespace ExampleProofs.NanoP4FieldUpdate

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- Obligations certified for the scalar field-update slice. Each field is a
proposition over the actual source profile, implementation or reference. -/
structure Certificate : Prop where
  /-- The helper quotation belongs to the spec used to initialize the reference. -/
  sourceMember : NanoP4Spec.«$update_fieldValue».al ∈ NanoP4Spec.spec
  /-- Every admitted source list has a related generated representation. -/
  sourceCoverage : ∀ raw, SourceFields raw →
    ∃ fields : List Field, Rel raw (generatedFields fields)
  /-- Generated profile encodings remain in the independently declared source domain. -/
  encodingValid : ∀ fields, SourceFields (toValue (generatedFields fields))
  /-- Decoding the independent source encoding succeeds with sufficient fuel. -/
  decoderRoundTrip : ∀ fields fuel,
    OfValue.ofValue (α := List NanoP4Spec.fieldValue) (fuel + 6) (sourceFields fields) =
      some (generatedFields fields)
  /-- Observations retain field order, duplicates, names, scalar tags and payloads. -/
  observationFaithful : ∀ left right,
    canon (sourceFields left) = canon (sourceFields right) ↔ left = right
  /-- Actual reference initialization succeeds; it is not a caller assumption. -/
  initialized : Interp_al.Ctx.init NanoP4Spec.spec = .ok Environment.global
  /-- All quoted dependencies are present in the concrete global environment. -/
  environmentHolds : HoldsSpec NanoP4Spec.spec Environment.global
  /-- No local callbacks replace functions from the initialized specification. -/
  noOverrides : Environment.ctx.local.fenv = []
  /-- The actual generated operation is the total first-match update. -/
  generatedMeaning : ∀ fields name replacement,
    NanoP4Spec.«$update_fieldValue» fields name replacement =
      some (.ok (update fields name replacement))
  /-- Every terminating reference outcome matches the actual generated operation. -/
  referenceToGenerated : ∀ fuel (fields : List Field) name (replacement : Scalar)
      rawFields rawName rawReplacement,
    Rel rawFields (generatedFields fields) → Rel rawName name →
    Rel rawReplacement replacement.generated → ∀ result,
    (referenceUpdate fuel rawFields rawName rawReplacement).run = some result →
    ∃ output generated, result = .ok output ∧
      NanoP4Spec.«$update_fieldValue» (generatedFields fields) name replacement.generated =
        some (.ok generated) ∧ Rel output generated
  /-- Every successful generated outcome has an actual finite reference realization. -/
  generatedToReference : ∀ (fields : List Field) name (replacement : Scalar)
      rawFields rawName rawReplacement,
    Rel rawFields (generatedFields fields) → Rel rawName name →
    Rel rawReplacement replacement.generated → ∀ generated,
    NanoP4Spec.«$update_fieldValue» (generatedFields fields) name replacement.generated =
      some (.ok generated) →
    ∃ fuel output, (referenceUpdate fuel rawFields rawName rawReplacement).run =
      some (.ok output) ∧ Rel output generated
  /-- Two reference calls compose using the first raw output, with finite witnesses. -/
  composedObservations : ∀ fields rawFields,
    Rel rawFields (generatedFields fields) → ∀ left right leftValue rightValue observation,
    ReferenceObserves rawFields left right leftValue rightValue observation ↔
      observation = canon (toValue
        (update (update (generatedFields fields) left leftValue.generated)
          right rightValue.generated))
  /-- Distinct-name updates commute for already evaluated replacement values. -/
  independentUpdates : ∀ fields left right leftValue rightValue, left ≠ right →
    update (update fields left leftValue) right rightValue =
      update (update fields right rightValue) left leftValue

/-- The checked certificate for the existing bounded field-update proof.
No new source-domain, termination or environment assumption is introduced. -/
theorem certificate : Certificate where
  sourceMember := by
    run_tac
      let proof ← Tactic.memProof `NanoP4Spec.spec `NanoP4Spec.«$update_fieldValue».al
      (← Lean.Elab.Tactic.getMainGoal).assign proof
      Lean.Elab.Tactic.replaceMainGoal []
  sourceCoverage := fun _ source => fieldsCoverage source
  encodingValid := fieldsEncodingValid
  decoderRoundTrip := decodeFields
  observationFaithful := sourceFieldsInjective
  initialized := Environment.initEqOk
  environmentHolds := Environment.holdsSpec
  noOverrides := Environment.localFenvEmpty
  generatedMeaning := generatedEqUpdate
  referenceToGenerated := by
    intro fuel fields name replacement rawFields rawName rawReplacement hf hn hr result hrun
    obtain ⟨output, ho, hrel⟩ := referenceSound fuel (generatedFields fields)
      name replacement.generated rawFields rawName rawReplacement hf hn hr result hrun
    exact ⟨output, update (generatedFields fields) name replacement.generated,
      ho, generatedEqUpdate _ _ _, hrel⟩
  generatedToReference := by
    intro fields name replacement rawFields rawName rawReplacement hf hn hr generated hrun
    rw [generatedEqUpdate] at hrun
    cases Except.ok.inj (Option.some.inj hrun)
    exact referenceRealizes (generatedFields fields) name replacement.generated
      rawFields rawName rawReplacement hf hn hr
  composedObservations := referenceObservesIff
  independentUpdates := updateCommute

/-- info: 'ExampleProofs.NanoP4FieldUpdate.certificate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms certificate
#audit_axioms certificate

end ExampleProofs.NanoP4FieldUpdate
