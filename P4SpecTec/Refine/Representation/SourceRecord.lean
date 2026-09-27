import P4SpecTec.Refine.Representation.SourceAlias

/-!
Ordered record domains from actual source declarations. Labels, field positions and
multiplicity are retained independently of generated record decoder behavior.
This is our own proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.Representation.Source
open P4SpecTec.Lang.Il P4SpecTec.Domain

/-- A source record has exact ordered labels and independently valid instantiated fields. -/
def RecordDomain (spec : Lang.Al.spec) (externalDomain : String → value → Prop)
    (sourceFields : List typfield) (types : List typ) (v : value) : Prop :=
  ∃ fields : List valuefield, v.it = .StructV fields ∧
    List.Forall₂ (fun source actual => Atom.eq source.1.it actual.1.it = true)
      sourceFields fields ∧ Values spec externalDomain types (fields.map (·.2))

/-- Actual record membership exposes source labels, finite substitution and valid payloads. -/
theorem Valid.recordPayload {spec externalDomain} (name : id) (args : List typ)
    (parameters : List tparam) (sourceFields : List typfield) (v : value)
    (declared : body spec name.it = Option.some (parameters, .StructT sourceFields))
    (valid : Valid spec externalDomain (.VarT name args) v) :
    ∃ fields, instantiatedFields parameters args (sourceFields.map (·.2)) fields ∧
      RecordDomain spec externalDomain sourceFields fields v := by
  cases valid with
  | «alias» name args parameters definition instantiated v found =>
    simp [declared] at found
  | record name args parameters' sourceFields' instantiated v valueFields
      found shape labels fields payload =>
    have same := Option.some.inj (found.symm.trans declared)
    cases same
    exact ⟨instantiated, fields, valueFields, shape, labels, payload⟩
  | variant name args parameters cases constructor instantiated v tree found =>
    simp [declared] at found
  | external name v found payload =>
    simp [externalFalseOfBody declared] at found

/-- info: 'P4SpecTec.Refine.Representation.Source.Valid.recordPayload' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Valid.recordPayload
#audit_axioms Valid.recordPayload

/-- Actual record declaration and instantiated ordered payloads establish the named domain. -/
theorem RecordDomain.valid {spec externalDomain} (name : id) (args : List typ)
    (parameters : List tparam) (sourceFields : List typfield) (fields : List typ) (v : value)
    (declared : body spec name.it = Option.some (parameters, .StructT sourceFields))
    (instantiated : instantiatedFields parameters args (sourceFields.map (·.2)) fields)
    (valid : RecordDomain spec externalDomain sourceFields fields v) :
    Valid spec externalDomain (.VarT name args) v := by
  obtain ⟨valueFields, shape, labels, payload⟩ := valid
  exact .record name args parameters sourceFields fields v valueFields declared
    shape labels instantiated payload

/-- info: 'P4SpecTec.Refine.Representation.Source.RecordDomain.valid' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms RecordDomain.valid
#audit_axioms RecordDomain.valid

/-- Related ordered labelled fields have identical canonical record payloads. -/
theorem canonicalRecordFields {fields rendered : List valuefield}
    (related : List.Forall₂ (fun a b => Atom.eq a.1.it b.1.it = true ∧ Rel a.2 b.2)
      fields rendered) : canonFields fields = canonFields rendered := by
  induction related with
  | nil => rfl
  | @cons a b fields rendered head tail ih =>
    have label : a.1.it = b.1.it := by
      simpa [Atom.eq, Atom.compare_eq_iff] using head.1
    simp only [canonFields, label]
    rw [show canon a.2 = canon b.2 from head.2, ih]

/-- info: 'P4SpecTec.Refine.Representation.Source.canonicalRecordFields' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonicalRecordFields
#audit_axioms canonicalRecordFields

/-- Related ordered labels and payloads imply related source and rendered records. -/
theorem recordRelation {v w : value} {fields rendered : List valuefield}
    (sourceShape : v.it = .StructV fields) (renderedShape : w.it = .StructV rendered)
    (related : List.Forall₂ (fun a b => Atom.eq a.1.it b.1.it = true ∧ Rel a.2 b.2)
      fields rendered) : Rel v w := by
  have same := canonicalRecordFields related
  simp only [Rel, Prelude.ToValue.toValue, _root_.id, canon, canon',
    sourceShape, renderedShape]
  rw [same]

/-- info: 'P4SpecTec.Refine.Representation.Source.recordRelation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recordRelation
#audit_axioms recordRelation

end P4SpecTec.Refine.Representation.Source
