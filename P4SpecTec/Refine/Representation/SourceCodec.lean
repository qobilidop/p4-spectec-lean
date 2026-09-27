import P4SpecTec.Refine.Representation.SourceContainer

/-!
Primitive and container codecs bound to independent source grammar derivations.
This is our own proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.Representation.Source
open P4SpecTec.Lang.Il P4SpecTec.Prelude

/-- The independent Boolean grammar is precisely the strict Boolean value shape. -/
theorem boolIff {spec externalDomain} (v : value) :
    Valid spec externalDomain .BoolT v ↔ Shape.bool v := by
  constructor
  · intro h; cases h with | bool v b shape => exact ⟨b, shape⟩
  · rintro ⟨b, shape⟩; exact .bool v b shape

/-- info: 'P4SpecTec.Refine.Representation.Source.boolIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boolIff
#audit_axioms boolIff

/-- Source naturals use the natural numeric tag, preserving arbitrary value metadata. -/
theorem natIff {spec externalDomain} (v : value) :
    Valid spec externalDomain (.NumT .NatT) v ↔ Shape.nat v := by
  constructor
  · intro h; cases h with | nat v n shape => exact ⟨n, shape⟩
  · rintro ⟨n, shape⟩; exact .nat v n shape

/-- info: 'P4SpecTec.Refine.Representation.Source.natIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natIff
#audit_axioms natIff

/-- Source integers use the integer numeric tag, independently of runtime membership. -/
theorem intIff {spec externalDomain} (v : value) :
    Valid spec externalDomain (.NumT .IntT) v ↔ Shape.int v := by
  constructor
  · intro h; cases h with | int v n shape => exact ⟨n, shape⟩
  · rintro ⟨n, shape⟩; exact .int v n shape

/-- info: 'P4SpecTec.Refine.Representation.Source.intIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intIff
#audit_axioms intIff

/-- The independent text grammar accepts exactly byte-text values. -/
theorem textIff {spec externalDomain} (v : value) :
    Valid spec externalDomain .TextT v ↔ Shape.text v := by
  constructor
  · intro h; cases h with | text v s shape => exact ⟨s, shape⟩
  · rintro ⟨s, shape⟩; exact .text v s shape

/-- info: 'P4SpecTec.Refine.Representation.Source.textIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms textIff
#audit_axioms textIff

/-- Homogeneous positional source derivations coincide with elementwise source validity. -/
theorem Values.replicateIff {spec externalDomain} (element : typ) (vs : List value) :
    Values spec externalDomain (List.replicate vs.length element) vs ↔
      ∀ v ∈ vs, Valid spec externalDomain element.it v := by
  constructor
  · intro h
    induction vs with
    | nil => simp
    | cons v vs ih =>
      cases h with
      | cons type v types values head tail =>
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact head
        · exact ih tail w hw
  · exact Values.replicate element vs

/-- info: 'P4SpecTec.Refine.Representation.Source.Values.replicateIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Values.replicateIff
#audit_axioms Values.replicateIff

/-- A source list preserves its exact list tag, element order and every element domain. -/
theorem listIff {spec externalDomain} (element : typ) (v : value) :
    Valid spec externalDomain (.IterT element .List) v ↔
      Shape.list (Valid spec externalDomain element.it) v := by
  constructor
  · intro h
    cases h with
    | list element v values shape elements =>
      exact ⟨values, shape, (Values.replicateIff element values).mp elements⟩
  · rintro ⟨vs, shape, elements⟩
    exact .list element v vs shape (Values.replicate element vs elements)

/-- info: 'P4SpecTec.Refine.Representation.Source.listIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms listIff
#audit_axioms listIff

/-- A source option preserves the absent or present tag and its payload domain. -/
theorem optionIff {spec externalDomain} (element : typ) (v : value) :
    Valid spec externalDomain (.IterT element .Opt) v ↔
      Shape.option (Valid spec externalDomain element.it) v := by
  constructor
  · intro h
    cases h with
    | none element v shape => exact .inl shape
    | some element v inner shape payload => exact .inr ⟨inner, shape, payload⟩
  · rintro (shape | ⟨inner, shape, payload⟩)
    · exact .none element v shape
    · exact .some element v inner shape payload

/-- info: 'P4SpecTec.Refine.Representation.Source.optionIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms optionIff
#audit_axioms optionIff

/-- The primitive Boolean codec discharges its actual independent source grammar. -/
theorem boolCodec {spec externalDomain} :
    Codec (Valid spec externalDomain .BoolT) (fun _ : Bool => True) := by
  have domain := funext fun v =>
    propext (boolIff (spec := spec) (externalDomain := externalDomain) v)
  rw [domain]
  exact Representation.boolCodec

/-- info: 'P4SpecTec.Refine.Representation.Source.boolCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boolCodec
#audit_axioms boolCodec

/-- The primitive natural codec discharges the strict natural source grammar. -/
theorem natCodec {spec externalDomain} :
    Codec (Valid spec externalDomain (.NumT .NatT)) (fun _ : Nat => True) := by
  have domain := funext fun v =>
    propext (natIff (spec := spec) (externalDomain := externalDomain) v)
  rw [domain]
  exact Representation.natCodec

/-- info: 'P4SpecTec.Refine.Representation.Source.natCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natCodec
#audit_axioms natCodec

/-- The primitive integer codec discharges the strict integer source grammar. -/
theorem intCodec {spec externalDomain} :
    Codec (Valid spec externalDomain (.NumT .IntT)) (fun _ : Int => True) := by
  have domain := funext fun v =>
    propext (intIff (spec := spec) (externalDomain := externalDomain) v)
  rw [domain]
  exact Representation.intCodec

/-- info: 'P4SpecTec.Refine.Representation.Source.intCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intCodec
#audit_axioms intCodec

/-- The primitive byte-text codec discharges its independent source grammar. -/
theorem textCodec {spec externalDomain} :
    Codec (Valid spec externalDomain .TextT) (fun _ : ByteText => True) := by
  have domain := funext fun v =>
    propext (textIff (spec := spec) (externalDomain := externalDomain) v)
  rw [domain]
  exact Representation.textCodec

/-- info: 'P4SpecTec.Refine.Representation.Source.textCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms textCodec
#audit_axioms textCodec

/-- A legal element instance yields a source-list codec without a length or depth bound. -/
theorem listCodec {spec externalDomain} {α : Type} [ToValue α] [OfValue α]
    (element : typ) (admitted : α → Prop)
    (contract : Codec (Valid spec externalDomain element.it) admitted) :
    Codec (Valid spec externalDomain (.IterT element .List))
      (fun xs : List α => ∀ x ∈ xs, admitted x) := by
  have domain := funext fun v =>
    propext (listIff (spec := spec) (externalDomain := externalDomain) element v)
  rw [domain]
  exact contract.list

/-- info: 'P4SpecTec.Refine.Representation.Source.listCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms listCodec
#audit_axioms listCodec

/-- A legal element instance yields an exact source-option codec. -/
theorem optionCodec {spec externalDomain} {α : Type} [ToValue α] [OfValue α]
    (element : typ) (admitted : α → Prop)
    (contract : Codec (Valid spec externalDomain element.it) admitted) :
    Codec (Valid spec externalDomain (.IterT element .Opt))
      (fun x : Option α => ∀ y ∈ x, admitted y) := by
  have domain := funext fun v =>
    propext (optionIff (spec := spec) (externalDomain := externalDomain) element v)
  rw [domain]
  exact contract.option

/-- info: 'P4SpecTec.Refine.Representation.Source.optionCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms optionCodec
#audit_axioms optionCodec

end P4SpecTec.Refine.Representation.Source
