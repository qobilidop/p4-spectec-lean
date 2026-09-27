import P4SpecTec.Refine.Representation

/-!
A generated alias consumes one unit of decoder fuel before invoking its captured
instance. These rules compose the actual decoders without assuming that reducible
aliases resolve to the same type-class dictionary. This is our own proof support.
-/

namespace P4SpecTec.Refine.Representation

open P4SpecTec.Lang.Il P4SpecTec.Prelude

/-- Adding an alias decoder layer preserves soundness and shifts its sufficient bound. -/
theorem DecoderCorrect.delay {α : Type} [ToValue α] {source : SourceDomain}
    {admitted : α → Prop} {decode : Nat → value → Option α}
    (contract : DecoderCorrect source admitted decode) :
    DecoderCorrect source admitted (fun
      | 0, _ => none
      | fuel + 1, v => decode fuel v) where
  sound fuel v x hv hd := by
    cases fuel with
    | zero => cases hd
    | succ fuel => exact contract.sound fuel v x hv hd
  sufficient v hv := by
    obtain ⟨x, bound, hb⟩ := contract.sufficient v hv
    refine ⟨x, bound + 1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel => exact hb fuel (by omega)

/-- info: 'P4SpecTec.Refine.Representation.DecoderCorrect.delay' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DecoderCorrect.delay
#audit_axioms DecoderCorrect.delay

end P4SpecTec.Refine.Representation
