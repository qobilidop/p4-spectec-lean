import P4SpecTec.Refine.Representation.SourceCodec

/-!
Contextual positional tuple codecs. Two-field encoding fixes the right component to
one value even when its carrier is itself a product; no ambient Prod decoder is assumed.
The empty tuple has its own exact decoder. Legal child codecs remain explicit.
-/

namespace P4SpecTec.Refine.Representation.Source

open P4SpecTec.Lang.Il P4SpecTec.Prelude

/-- Encode exactly two source fields, independently of ambient tuple-flattening instances. -/
def pairEncoder {α β : Type} [ToValue α] [ToValue β] (pair : α × β) : value :=
  Runtime.Value.Make.tuple .TextT [toValue pair.1, toValue pair.2]

/-- Decode exactly two source fields with their actual child dictionaries at the same fuel. -/
def pairDecoder {α β : Type} [OfValue α] [OfValue β] (fuel : Nat) (v : value) :
    Option (α × β) :=
  match v.it with
  | .TupleV [left, right] => do
    pure (← OfValue.ofValue fuel left, ← OfValue.ofValue fuel right)
  | _ => none

/-- The contextual encoder is the standard product encoder with the right singleton fixed. -/
theorem pairEncoderEq {α β : Type} [ToValue α] [ToValue β] (pair : α × β) :
    pairEncoder pair =
      (letI : ToValues β := ⟨fun b => [toValue b]⟩; toValue pair) := rfl

/-- info: 'P4SpecTec.Refine.Representation.Source.pairEncoderEq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairEncoderEq
#audit_axioms pairEncoderEq

/-- Exact two-field source representation, with explicit frozen encoder and decoder dictionaries. -/
theorem pairCodec {spec externalDomain} {α β : Type}
    [ToValue α] [OfValue α] [ToValue β] [OfValue β]
    (leftType rightType : typ) (left : α → Prop) (right : β → Prop)
    (leftCodec : Codec (Valid spec externalDomain leftType.it) left)
    (rightCodec : Codec (Valid spec externalDomain rightType.it) right) :
    @Codec (α × β) ⟨pairEncoder⟩ ⟨pairDecoder⟩
      (Valid spec externalDomain (.TupleT [leftType, rightType]))
      (fun pair => left pair.1 ∧ right pair.2) := by
  refine @Codec.mk _ ⟨pairEncoder⟩ ⟨pairDecoder⟩ _ _ ?_ ?_
  · intro pair accepted
    exact .tuple [leftType, rightType] _ [toValue pair.1, toValue pair.2] rfl
      (.cons leftType _ _ _ (leftCodec.encodingValid pair.1 accepted.1)
        (.cons rightType _ _ _ (rightCodec.encodingValid pair.2 accepted.2) .nil))
  · constructor
    · intro fuel v pair valid decoded
      cases valid with
      | tuple types v values shape payload =>
        cases payload with
        | cons t a ts vs ha rest =>
          cases rest with
          | cons t b ts vs hb rest =>
            cases rest
            cases hl : OfValue.ofValue (α := α) fuel a with
            | none => simp [OfValue.ofValue, pairDecoder, shape, hl] at decoded
            | some x =>
              cases hr : OfValue.ofValue (α := β) fuel b with
              | none => simp [OfValue.ofValue, pairDecoder, shape, hl, hr] at decoded
              | some y =>
                have same : (x, y) = pair := by
                  simpa [OfValue.ofValue, pairDecoder, shape, hl, hr] using decoded
                subst pair
                obtain ⟨hx, rx⟩ := leftCodec.decoder.sound fuel a x ha hl
                obtain ⟨hy, ry⟩ := rightCodec.decoder.sound fuel b y hb hr
                refine ⟨⟨hx, hy⟩, ?_⟩
                change canon v = canon (pairEncoder (x, y))
                change canon a = canon (toValue x) at rx
                change canon b = canon (toValue y) at ry
                simp only [canon, shape, pairEncoder, Runtime.Value.Make.tuple,
                  Runtime.Value.Make.mk, canon', canons]
                simp only [canon] at rx ry
                rw [rx, ry]
    · intro v valid
      cases valid with
      | tuple types v values shape payload =>
        cases payload with
        | cons t a ts vs ha rest =>
          cases rest with
          | cons t b ts vs hb rest =>
            cases rest
            obtain ⟨x, leftBound, hl⟩ := leftCodec.decoder.sufficient a ha
            obtain ⟨y, rightBound, hr⟩ := rightCodec.decoder.sufficient b hb
            refine ⟨(x, y), max leftBound rightBound, ?_⟩
            intro fuel large
            have hleft := hl fuel (Nat.le_trans (Nat.le_max_left _ _) large)
            have hright := hr fuel (Nat.le_trans (Nat.le_max_right _ _) large)
            simp [OfValue.ofValue, pairDecoder, shape, hleft, hright]

/-- info: 'P4SpecTec.Refine.Representation.Source.pairCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairCodec
#audit_axioms pairCodec

/-- Decode only the empty source tuple, preserving the exact source arity. -/
def unitDecoder (_fuel : Nat) (v : value) : Option Unit :=
  match v.it with | .TupleV [] => some () | _ => none

/-- The exact empty-tuple source codec uses the actual Unit encoder and contextual decoder. -/
theorem unitCodec {spec externalDomain} :
    @Codec Unit inferInstance ⟨unitDecoder⟩
      (Valid spec externalDomain (.TupleT [])) (fun _ => True) := by
  refine @Codec.mk Unit inferInstance ⟨unitDecoder⟩ _ _ ?_ ?_
  · intro x _
    exact .tuple [] _ [] rfl .nil
  · constructor
    · intro fuel v x valid _
      cases valid with
      | tuple types v values shape payload =>
        cases payload
        refine ⟨trivial, ?_⟩
        cases x
        change canon v = canon (toValue ())
        simp [canon, shape, ToValue.toValue, Runtime.Value.Make.tuple, Runtime.Value.Make.mk,
          canon', canons]
    · intro v valid
      cases valid with
      | tuple types v values shape payload =>
        cases payload
        exact ⟨(), 0, fun _ _ => by simp [OfValue.ofValue, unitDecoder, shape]⟩

/-- info: 'P4SpecTec.Refine.Representation.Source.unitCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unitCodec
#audit_axioms unitCodec

end P4SpecTec.Refine.Representation.Source
