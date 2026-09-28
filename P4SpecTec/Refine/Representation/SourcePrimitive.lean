import P4SpecTec.Refine.Representation.SourceTuple

/-!
A checked profile of existing primitive and contextual container codecs. Numeric tags
and option shapes are the independent source grammar, not runtime Match acceptance.
Actual producer/call admission and declared container codecs remain separate obligations.
-/

namespace P4SpecTec.Refine.Representation.Source

open P4SpecTec.Lang.Il P4SpecTec.Prelude

/-- Existing primitive codecs and constructors for every explicitly legal child codec.
The profile fixes contextual tuple dictionaries and never assumes arbitrary instance laws. -/
structure PrimitiveProfile (spec : Lang.Al.spec) (externalDomain : Domain) :
    Prop where
  /-- Strict source Boolean representation. -/
  booleans : Codec (Valid spec externalDomain .BoolT) (fun _ : Bool => True)
  /-- Strict natural-tag source representation. -/
  naturals : Codec (Valid spec externalDomain (.NumT .NatT)) (fun _ : Nat => True)
  /-- Strict integer-tag source representation. -/
  integers : Codec (Valid spec externalDomain (.NumT .IntT)) (fun _ : Int => True)
  /-- Arbitrary byte-text source representation. -/
  texts : Codec (Valid spec externalDomain .TextT) (fun _ : ByteText => True)
  /-- Ordered source lists inherit their exact legal child dictionary and admission. -/
  lists : ∀ {α : Type} [ToValue α] [OfValue α] (element : typ) (admitted : α → Prop),
    Codec (Valid spec externalDomain element.it) admitted →
    Codec (Valid spec externalDomain (.IterT element .List))
      (fun xs : List α => ∀ x ∈ xs, admitted x)
  /-- Exact absent/present options inherit their legal child dictionary and admission. -/
  options : ∀ {α : Type} [ToValue α] [OfValue α] (element : typ) (admitted : α → Prop),
    Codec (Valid spec externalDomain element.it) admitted →
    Codec (Valid spec externalDomain (.IterT element .Opt))
      (fun x : Option α => ∀ y ∈ x, admitted y)
  /-- Two-field tuples retain their right field as one value, even for product carriers. -/
  pairs : ∀ {α β : Type} [ToValue α] [OfValue α] [ToValue β] [OfValue β]
    (leftType rightType : typ) (left : α → Prop) (right : β → Prop),
    Codec (Valid spec externalDomain leftType.it) left →
    Codec (Valid spec externalDomain rightType.it) right →
    @Codec (α × β) ⟨pairEncoder⟩ ⟨pairDecoder⟩
      (Valid spec externalDomain (.TupleT [leftType, rightType]))
      (fun p => left p.1 ∧ right p.2)
  /-- Exact zero-output tuples use Unit and the contextual empty-tuple decoder. -/
  units : @Codec Unit inferInstance ⟨unitDecoder⟩
    (Valid spec externalDomain (.TupleT [])) (fun _ => True)

/-- Package the existing audited codecs without reproving or widening any source domain. -/
theorem primitiveProfile {spec externalDomain} : PrimitiveProfile spec externalDomain :=
  ⟨boolCodec, natCodec, intCodec, textCodec, @listCodec spec externalDomain,
    @optionCodec spec externalDomain, @pairCodec spec externalDomain, unitCodec⟩

/-- info: 'P4SpecTec.Refine.Representation.Source.primitiveProfile' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms primitiveProfile
#audit_axioms primitiveProfile

end P4SpecTec.Refine.Representation.Source
