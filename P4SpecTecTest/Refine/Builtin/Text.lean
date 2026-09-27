import NanoP4Spec.«0-stdlib»
import P4SpecTec.Refine.Builtin.Text

/-! The actual Nano whitespace wrapper obeys the reusable byte-operation contract. -/

namespace P4SpecTecTest.Refine.Builtin.Text

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- Every related byte input agrees with the actual generated Nano wrapper. -/
theorem nanoWhitespace {v : Lang.Il.value} {s : ByteText} (h : Rel v s)
    (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "strip_all_whitespace" [] [v]).run =
      (NanoP4Spec.«$strip_all_whitespace» s).map (Except.map toValue) := by
  exact P4SpecTec.Refine.Builtin.Text.stripWhitespaceRunOfRel h hints

/-- info: 'P4SpecTecTest.Refine.Builtin.Text.nanoWhitespace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoWhitespace

-- Spaces disappear; invalid UTF-8, NUL and tab bytes remain unchanged.
#guard match NanoP4Spec.«$strip_all_whitespace» (ByteText.ofBytes ⟨#[255, 32, 0, 9, 32]⟩) with
  | some (.ok s) => s == ByteText.ofBytes ⟨#[255, 0, 9]⟩
  | _ => false

end P4SpecTecTest.Refine.Builtin.Text
