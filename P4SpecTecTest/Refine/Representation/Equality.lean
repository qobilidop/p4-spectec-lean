import NanoP4Spec.«0-stdlib»
import P4SpecTec.Refine.Representation.Equality

/-! Legal equality dictionaries preserve canonical observations without assuming injectivity. -/

namespace P4SpecTecTest.Refine.Representation.Equality

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Refine.Representation

/-- Ordinary lawful equality can distinguish a field omitted by the encoder. -/
structure Tagged where
  key : Bool
  ghost : Bool
  deriving BEq, ReflBEq, LawfulBEq

instance : ToValue Tagged := ⟨fun x => toValue x.key⟩

/-- The example's Boolean equality is lawful for its actual Lean values. -/
theorem taggedLawful (x y : Tagged) : (x == y) = true ↔ x = y := beq_iff_eq

/-- info: 'P4SpecTecTest.Refine.Representation.Equality.taggedLawful' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms taggedLawful
#audit_axioms taggedLawful

/-- Lawful Boolean equality alone does not establish canonical compatibility. -/
theorem lawfulInsufficient : ¬ValueBEq Tagged := by
  intro law
  letI := law
  have h := (ValueBEq.beqTrueIffCanon
    (⟨false, false⟩ : Tagged) ⟨false, true⟩).2 rfl
  change false = true at h
  contradiction

/-- info: 'P4SpecTecTest.Refine.Representation.Equality.lawfulInsufficient' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lawfulInsufficient
#audit_axioms lawfulInsufficient

/-- A lossy carrier with value-based equality is a legal equality dictionary. -/
structure Observed where
  key : Nat
  ghost : Bool

instance : ToValue Observed := ⟨fun x => toValue x.key⟩
instance : BEq Observed := ⟨valueEq⟩
instance : ValueBEq Observed := ValueBEq.ofValueEq

/-- Canonical-compatible equality deliberately permits non-injective representations. -/
theorem noninjectiveCompatible :
    ((⟨0, false⟩ : Observed) == ⟨0, true⟩) = true ∧
      (⟨0, false⟩ : Observed) ≠ ⟨0, true⟩ := by
  constructor
  · exact (ValueBEq.beqTrueIffCanon _ _).2 rfl
  · intro h
    have hghost := congrArg Observed.ghost h
    contradiction

/-- info: 'P4SpecTecTest.Refine.Representation.Equality.noninjectiveCompatible' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms noninjectiveCompatible
#audit_axioms noninjectiveCompatible

/-- Nested list/option instances retain compatibility for arbitrary extern JSON payloads. -/
theorem nestedExtern (xs ys : List (Option (List ExternValue))) :
    (xs == ys) = true ↔ canon (toValue xs) = canon (toValue ys) :=
  ValueBEq.beqTrueIffCanon xs ys

/-- info: 'P4SpecTecTest.Refine.Representation.Equality.nestedExtern' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nestedExtern
#audit_axioms nestedExtern

/-- Arbitrary raw metadata and nested values agree with the selected element dictionary. -/
theorem representedEquality {v w : Lang.Il.value} {xs ys : List (Option ByteText)}
    (hx : Rel v xs) (hy : Rel w ys) : Runtime.Value.eq v w = (xs == ys) :=
  ValueBEq.eqOfRel hx hy

/-- info: 'P4SpecTecTest.Refine.Representation.Equality.representedEquality' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms representedEquality
#audit_axioms representedEquality

/-- The actual generated `in_set` needs exactly this law for polymorphic membership. -/
theorem generatedInSet {α : Type} [ToValue α] [BEq α] [ValueBEq α]
    {v : Lang.Il.value} {x : α} {raws : List Lang.Il.value} {xs : List α}
    (hx : Rel v x) (hs : canons raws = canons (xs.map toValue)) :
    NanoP4Spec.«$in_set» (.lbrace_rbrace xs) x =
      some (.ok (raws.any (Runtime.Value.eq v))) := by
  change some (Except.ok (ε := Fail) (xs.elem x)) = _
  rw [ValueBEq.elemOfRel hx hs]

/-- info: 'P4SpecTecTest.Refine.Representation.Equality.generatedInSet' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generatedInSet
#audit_axioms generatedInSet

end P4SpecTecTest.Refine.Representation.Equality
