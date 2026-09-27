import NanoP4Spec.«0-stdlib»
import P4SpecTec.Prelude.Extern
import P4SpecTec.Refine.Builtin.Set

/-! Set contracts cover actual Nano images, nested externs, and malformed inputs. -/

namespace P4SpecTecTest.Refine.Builtin.Set

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine
open P4SpecTec.Refine.Builtin

private def image {α : Type} [ToValue α] (xs : List α) : Lang.Il.value :=
  toValue (NanoP4Spec.set.lbrace_rbrace xs)

private theorem imageRel {α : Type} [ToValue α] (xs : List α) :
    Rel (image xs) (Collection.bracketed (xs.map toValue)) := rfl

/-- The generated set constructor satisfies the independent shared collection interface. -/
theorem nanoImage {α : Type} [ToValue α] (xs : List α) :
    ∃ raws, P4SpecTec.Builtin.Call.set_of_value (image xs) = some raws ∧
      canons raws = canons (xs.map toValue) :=
  Collection.bracketedDecodeOfRel (imageRel xs)

/-- info: 'P4SpecTecTest.Refine.Builtin.Set.nanoImage' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoImage
#audit_axioms nanoImage

/-- Arbitrary nested extern elements pass through actual intersection dispatch. -/
theorem nestedIntersection (xs ys : List (Option (List ExternValue)))
    (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "intersect_set" [typ]
      [image xs, image ys]).run = some (.ok out) ∧
      Rel out (Collection.bracketed
        ((P4SpecTec.Builtin.Sets.intersect_set xs ys).map toValue)) :=
  Set.intersectRunOfRel (imageRel xs) (imageRel ys) hints typ

/-- info: 'P4SpecTecTest.Refine.Builtin.Set.nestedIntersection' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nestedIntersection
#audit_axioms nestedIntersection

/-- A deliberately non-injective encoder must not be assumed faithful by set proofs. -/
structure Tagged where
  key : Nat
  ghost : Bool

instance : ToValue Tagged := ⟨fun x => toValue x.key⟩

/-- Union retains the actual final duplicate representatives before encoding. -/
theorem representatives :
    P4SpecTec.Builtin.Sets.union_set
      ([⟨2, false⟩, ⟨1, true⟩] : List Tagged) [⟨2, true⟩, ⟨1, false⟩] =
      [⟨1, false⟩, ⟨2, true⟩] := by cbv

/-- info: 'P4SpecTecTest.Refine.Builtin.Set.representatives' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms representatives
#audit_axioms representatives

/-- Union refinement does not require injectivity of the typed encoder. -/
theorem noninjectiveUnion (xs ys : List Tagged) (hints : P4.Unparse.HEnv)
    (typ : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "union_set" [typ]
      [image xs, image ys]).run = some (.ok out) ∧
      Rel out (Collection.bracketed ((P4SpecTec.Builtin.Sets.union_set xs ys).map toValue)) :=
  Set.unionRunOfRel (imageRel xs) (imageRel ys) hints typ

/-- info: 'P4SpecTecTest.Refine.Builtin.Set.noninjectiveUnion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms noninjectiveUnion
#audit_axioms noninjectiveUnion

/-- Difference shares the same arbitrary nested payload contract. -/
theorem nestedDifference (xs ys : List (List ExternValue)) (hints : P4.Unparse.HEnv)
    (typ : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "diff_set" [typ]
      [image xs, image ys]).run = some (.ok out) ∧
      Rel out (Collection.bracketed ((P4SpecTec.Builtin.Sets.diff_set xs ys).map toValue)) :=
  Set.diffRunOfRel (imageRel xs) (imageRel ys) hints typ

/-- info: 'P4SpecTecTest.Refine.Builtin.Set.nestedDifference' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nestedDifference
#audit_axioms nestedDifference

/-- Union over arbitrary lists of represented sets preserves nested extern payloads. -/
theorem nestedUnions (sets : List (List (Option ExternValue)))
    (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "unions_set" [typ]
      [toValue (sets.map fun xs => Collection.bracketed (xs.map toValue))]).run =
        some (.ok out) ∧
      Rel out (Collection.bracketed ((P4SpecTec.Builtin.Sets.unions_set sets).map toValue)) :=
  Set.unionsRunOfRel rfl hints typ

/-- info: 'P4SpecTecTest.Refine.Builtin.Set.nestedUnions' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nestedUnions
#audit_axioms nestedUnions

/-- Subset dispatch ignores supplied type metadata, just as the pinned dispatcher does. -/
theorem subsetTypes (xs ys : List ExternValue) (hints : P4.Unparse.HEnv)
    (types : List Lang.Il.typ) :
    (Interp_al.Effects.builtinEval hints "sub_set" types [image xs, image ys]).run =
      some (.ok (toValue (P4SpecTec.Builtin.Sets.sub_set xs ys))) :=
  Set.subRunOfRel (imageRel xs) (imageRel ys) hints types

/-- info: 'P4SpecTecTest.Refine.Builtin.Set.subsetTypes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms subsetTypes
#audit_axioms subsetTypes

/-- Equality accepts unsorted represented sets and observes their membership. -/
theorem equalityTypes (xs ys : List ExternValue) (hints : P4.Unparse.HEnv)
    (types : List Lang.Il.typ) :
    (Interp_al.Effects.builtinEval hints "eq_set" types [image xs, image ys]).run =
      some (.ok (toValue (P4SpecTec.Builtin.Sets.eq_set xs ys))) :=
  Set.eqRunOfRel (imageRel xs) (imageRel ys) hints types

/-- info: 'P4SpecTecTest.Refine.Builtin.Set.equalityTypes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms equalityTypes
#audit_axioms equalityTypes

/-- A malformed second argument is still rejected when the first is a valid empty set. -/
theorem malformedSecond (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) :
    (Interp_al.Effects.builtinEval hints "union_set" [typ]
      [image ([] : List Nat), toValue true]).run = some (.error .unmatch) :=
  Set.binaryShapeMismatch "union_set" (.inr (.inl rfl)) hints typ _ _ (.inr rfl)

/-- info: 'P4SpecTecTest.Refine.Builtin.Set.malformedSecond' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformedSecond
#audit_axioms malformedSecond

/-- Union over sets rejects a list containing a non-set value. -/
theorem malformedElement (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) :
    (Interp_al.Effects.builtinEval hints "unions_set" [typ]
      [toValue ([toValue true] : List Lang.Il.value)]).run = some (.error .unmatch) :=
  Set.unionsElementMismatch hints typ _ _ _ rfl

/-- info: 'P4SpecTecTest.Refine.Builtin.Set.malformedElement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms malformedElement
#audit_axioms malformedElement

end P4SpecTecTest.Refine.Builtin.Set
