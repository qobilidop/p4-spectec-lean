import NanoP4Proofs.FieldUpdate.Domain
import NanoP4Spec.«3.0-value»
import P4SpecTec.Refine.Calc

/-!
# Representation adequacy for scalar field lists

Every constructor of the independently selected source profile has a generated
representation. The scope is stated in `Domain`, not inferred from the generated
encoder. Decoder bounds below concern scalar values only, not nested records.
-/

namespace NanoP4Proofs.FieldUpdate

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- Embed a source-profile scalar into the actual generated Nano value type. -/
def Scalar.generated : Scalar → NanoP4Spec.value
  | .unsigned w i => .W w i
  | .signed w i => .S w i
  | .boolean b => ._B b
  | .matchKind n => .MATCH_KIND_dot n

/-- Embed an independently represented field into the generated field type. -/
def Field.generated (f : Field) : NanoP4Spec.fieldValue :=
  .semi f.payload.generated f.name

/-- Preserve the order and multiplicity of source-profile fields. -/
def generatedFields (fs : List Field) : List NanoP4Spec.fieldValue := fs.map Field.generated

/-- Generated scalar encodings agree with the independently specified source mixops. -/
theorem Scalar.sourceRel (s : Scalar) : Rel s.source s.generated := by
  cases s <;> rfl

/-- info: 'NanoP4Proofs.FieldUpdate.Scalar.sourceRel' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Scalar.sourceRel

/-- Generated field encodings preserve payload, name, and their positions. -/
theorem Field.sourceRel (f : Field) : Rel f.source f.generated := by
  cases f with
  | mk s n => cases s <;> rfl

/-- info: 'NanoP4Proofs.FieldUpdate.Field.sourceRel' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Field.sourceRel

/-- Source field lists and generated field lists have the same observations. -/
theorem sourceFieldsRel (fs : List Field) : Rel (sourceFields fs) (generatedFields fs) := by
  suffices h : Refine.canons (fs.map Field.source) =
      Refine.canons ((generatedFields fs).map toValue) from
    congrArg (fun vs => (⟨.ListV vs, dummy, Util.Source.no_region⟩ : Lang.Il.value)) h
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change Refine.canon f.source :: Refine.canons (fs.map Field.source) =
      Refine.canon (toValue f.generated) ::
        Refine.canons ((generatedFields fs).map toValue)
    rw [show Refine.canon f.source = Refine.canon (toValue f.generated) from f.sourceRel, ih]

/-- info: 'NanoP4Proofs.FieldUpdate.sourceFieldsRel' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceFieldsRel

/-- No supported source scalar is omitted by the generated representation. -/
theorem scalarCoverage {v : Lang.Il.value} (h : SourceScalar v) :
    ∃ s : Scalar, Rel v s.generated := by
  obtain ⟨s, h⟩ := h
  exact ⟨s, h.trans s.sourceRel⟩

/-- info: 'NanoP4Proofs.FieldUpdate.scalarCoverage' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalarCoverage

/-- No supported source field list is omitted by the generated representation. -/
theorem fieldsCoverage {v : Lang.Il.value} (h : SourceFields v) :
    ∃ fs : List Field, Rel v (generatedFields fs) := by
  obtain ⟨fs, h⟩ := h
  exact ⟨fs, h.trans (sourceFieldsRel fs)⟩

/-- info: 'NanoP4Proofs.FieldUpdate.fieldsCoverage' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fieldsCoverage

/-- A generated scalar from this profile encodes a supported source shape. -/
theorem scalarEncodingValid (s : Scalar) : SourceScalar (toValue s.generated) :=
  ⟨s, s.sourceRel.symm⟩

/-- info: 'NanoP4Proofs.FieldUpdate.scalarEncodingValid' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms scalarEncodingValid

/-- A generated field list from this profile encodes a supported source shape. -/
theorem fieldsEncodingValid (fs : List Field) :
    SourceFields (toValue (generatedFields fs)) :=
  ⟨fs, (sourceFieldsRel fs).symm⟩

/-- info: 'NanoP4Proofs.FieldUpdate.fieldsEncodingValid' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fieldsEncodingValid

set_option linter.unusedSimpArgs false in
/-- Five layers cover the scalar plus the generated text-alias decoder chain. -/
theorem Scalar.decodeGenerated (s : Scalar) (fuel : Nat) :
    NanoP4Spec.value.ofValue (fuel + 5) (toValue s.generated) = some s.generated := by
  cases s <;>
    simp [NanoP4Spec.value.ofValue, Scalar.generated, toValue, NanoP4Spec.value.toValue,
      Value.caseArgs, Domain.Mixfix.eq_mixop, Domain.Mixfix.eq, Domain.Mixfix.eq.eqs,
      Domain.Mixfix.args, Runtime.Value.Make.case, Runtime.Value.Make.mk,
      Value.atom, Domain.Atom.eq, Domain.Atom.compare, Domain.Atom.tag,
      OfValue.ofValue, Runtime.Value.Make.nat, Runtime.Value.Make.int,
      Runtime.Value.Make.bool, Runtime.Value.Make.text, Util.Source.mkPhrase,
      NanoP4Spec.typeId.ofValue, NanoP4Spec.nameIR.ofValue, NanoP4Spec.callableId.ofValue,
      NanoP4Spec.id.ofValue, NanoP4Spec.typeId.toValue, NanoP4Spec.nameIR.toValue,
      NanoP4Spec.callableId.toValue, NanoP4Spec.id.toValue]

/-- info: 'NanoP4Proofs.FieldUpdate.Scalar.decodeGenerated' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Scalar.decodeGenerated

set_option linter.unusedSimpArgs false in
/-- Independent source scalar encodings decode into the corresponding generated values. -/
theorem Scalar.decodeSource (s : Scalar) (fuel : Nat) :
    NanoP4Spec.value.ofValue (fuel + 5) s.source = some s.generated := by
  cases s <;>
    simp [NanoP4Spec.value.ofValue, Scalar.generated, Scalar.source, Value.caseArgs,
      Domain.Mixfix.eq_mixop, Domain.Mixfix.eq, Domain.Mixfix.eq.eqs,
      Domain.Mixfix.args, Runtime.Value.Make.case, Runtime.Value.Make.mk,
      Value.atom, Domain.Atom.eq, Domain.Atom.compare, Domain.Atom.tag,
      OfValue.ofValue, Runtime.Value.Make.nat, Runtime.Value.Make.int,
      Runtime.Value.Make.bool, Runtime.Value.Make.text, Util.Source.mkPhrase,
      NanoP4Spec.typeId.ofValue, NanoP4Spec.nameIR.ofValue, NanoP4Spec.callableId.ofValue,
      NanoP4Spec.id.ofValue]

/-- info: 'NanoP4Proofs.FieldUpdate.Scalar.decodeSource' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Scalar.decodeSource

set_option linter.unusedSimpArgs false in
/-- One field layer plus the five-layer scalar bound suffices. -/
theorem Field.decodeGenerated (f : Field) (fuel : Nat) :
    NanoP4Spec.fieldValue.ofValue (fuel + 6) (toValue f.generated) = some f.generated := by
  cases f with
  | mk s n =>
    simp [Field.generated, toValue, NanoP4Spec.fieldValue.toValue,
      NanoP4Spec.fieldValue.ofValue, Value.caseArgs, Domain.Mixfix.eq_mixop,
      Domain.Mixfix.eq, Domain.Mixfix.eq.eqs, Domain.Mixfix.args,
      Runtime.Value.Make.case, Runtime.Value.Make.mk, Value.atom,
      Domain.Atom.eq, Domain.Atom.compare, Domain.Atom.tag, Util.Source.mkPhrase,
      show NanoP4Spec.value.ofValue (fuel + 5) s.generated.toValue = some s.generated
        from s.decodeGenerated fuel, OfValue.ofValue, NanoP4Spec.typeId.toValue,
      Runtime.Value.Make.text, NanoP4Spec.typeId.ofValue, NanoP4Spec.nameIR.ofValue,
      NanoP4Spec.callableId.ofValue, NanoP4Spec.id.ofValue, NanoP4Spec.nameIR.toValue,
      NanoP4Spec.callableId.toValue, NanoP4Spec.id.toValue]

/-- info: 'NanoP4Proofs.FieldUpdate.Field.decodeGenerated' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Field.decodeGenerated

set_option linter.unusedSimpArgs false in
/-- The independent field encoding has the same sufficient decoder bound. -/
theorem Field.decodeSource (f : Field) (fuel : Nat) :
    NanoP4Spec.fieldValue.ofValue (fuel + 6) f.source = some f.generated := by
  cases f with
  | mk s n =>
    simp [Field.source, Field.generated, NanoP4Spec.fieldValue.ofValue,
      Value.caseArgs, Domain.Mixfix.eq_mixop, Domain.Mixfix.eq,
      Domain.Mixfix.eq.eqs, Domain.Mixfix.args, Runtime.Value.Make.case,
      Runtime.Value.Make.mk, Value.atom, Domain.Atom.eq, Domain.Atom.compare,
      Domain.Atom.tag, Util.Source.mkPhrase, s.decodeSource fuel,
      OfValue.ofValue, Runtime.Value.Make.text, NanoP4Spec.typeId.ofValue,
      NanoP4Spec.nameIR.ofValue, NanoP4Spec.callableId.ofValue, NanoP4Spec.id.ofValue]

/-- info: 'NanoP4Proofs.FieldUpdate.Field.decodeSource' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Field.decodeSource

/-- List decoding applies the scalar-field bound to each element without a length cutoff. -/
theorem decodeFields (fs : List Field) (fuel : Nat) :
    OfValue.ofValue (α := List NanoP4Spec.fieldValue) (fuel + 6) (sourceFields fs) =
      some (generatedFields fs) := by
  change (fs.map Field.source).mapM (NanoP4Spec.fieldValue.ofValue (fuel + 6)) = _
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.map_cons, List.mapM_cons, f.decodeSource, ih]
    rfl

/-- info: 'NanoP4Proofs.FieldUpdate.decodeFields' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeFields

set_option linter.unusedSimpArgs false in
/-- Canonical observations distinguish every scalar tag and payload in this profile. -/
theorem Scalar.sourceInjective (a b : Scalar) :
    canon a.source = canon b.source ↔ a = b := by
  cases a <;> cases b <;>
    simp [Scalar.source, canon, canon', canonMixfix, canonMixfixes,
      Runtime.Value.Make.case, Runtime.Value.Make.mk, Runtime.Value.Make.nat,
      Runtime.Value.Make.int, Runtime.Value.Make.bool, Runtime.Value.Make.text,
      Util.Source.info.mk.injEq, Value.atom, Util.Source.mkPhrase]

/-- info: 'NanoP4Proofs.FieldUpdate.Scalar.sourceInjective' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Scalar.sourceInjective

/-- Canonical field observations retain both the scalar payload and the exact name. -/
theorem Field.sourceInjective (a b : Field) :
    canon a.source = canon b.source ↔ a = b := by
  cases a with
  | mk av an =>
    cases b with
    | mk bv bn =>
      simpa [Field.source, canon, canon', canonMixfix, canonMixfixes,
        Runtime.Value.Make.case, Runtime.Value.Make.mk, Runtime.Value.Make.text,
        Util.Source.info.mk.injEq, Field.mk.injEq] using
        and_congr (av.sourceInjective bv) (Iff.rfl (a := an = bn))

/-- info: 'NanoP4Proofs.FieldUpdate.Field.sourceInjective' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Field.sourceInjective

/-- Ordered canonical field-list observations do not identify different profile inputs. -/
theorem sourceFieldsInjective (as bs : List Field) :
    canon (sourceFields as) = canon (sourceFields bs) ↔ as = bs := by
  suffices h : canons (as.map Field.source) = canons (bs.map Field.source) ↔ as = bs by
    simpa [sourceFields, canon, canon', Runtime.Value.Make.list,
      Runtime.Value.Make.mk, Util.Source.info.mk.injEq] using h
  induction as generalizing bs with
  | nil => cases bs <;> simp [canons]
  | cons a as ih =>
    cases bs with
    | nil => simp [canons]
    | cons b bs => simp [canons, a.sourceInjective b, ih]

/-- info: 'NanoP4Proofs.FieldUpdate.sourceFieldsInjective' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sourceFieldsInjective

end NanoP4Proofs.FieldUpdate
