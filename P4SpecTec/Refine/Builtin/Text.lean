import P4SpecTec.Refine.ValueShape
import P4SpecTec.Interp.Effects

/-! Operation contracts for Nano byte-text builtins through actual AL dispatch. -/

namespace P4SpecTec.Refine.Builtin.Text

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- Canonically related text inputs decode to the same exact bytes. -/
theorem textPayloadOfRel {v : Lang.Il.value} {s : ByteText} (h : Rel v s) :
    v.it = .TextV s := by
  apply canon'_eq_text
  apply canon_eq_it
  exact h

/-- info: 'P4SpecTec.Refine.Builtin.Text.textPayloadOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms textPayloadOfRel

/-- Removing ASCII spaces preserves exact bytes through the actual builtin dispatcher.
The operation is total on all represented byte strings, including invalid UTF-8. -/
theorem stripWhitespaceRunOfRel {v : Lang.Il.value} {s : ByteText}
    (h : Rel v s) (hints : P4.Unparse.HEnv) :
    (Interp_al.Effects.builtinEval hints "strip_all_whitespace" [] [v]).run =
      some (.ok (toValue (P4SpecTec.Builtin.Texts.strip_all_whitespace s))) := by
  have hv := textPayloadOfRel h
  cases v with
  | mk payload note region =>
    change payload = .TextV s at hv
    subst payload
    rfl

/-- info: 'P4SpecTec.Refine.Builtin.Text.stripWhitespaceRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stripWhitespaceRunOfRel

/-- Text builtins reject nonempty type arguments as a retryable mismatch. -/
theorem stripWhitespaceTypeArgs (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ)
    (types : List Lang.Il.typ) (v : Lang.Il.value) :
    (Interp_al.Effects.builtinEval hints "strip_all_whitespace" (typ :: types) [v]).run =
      some (.error .unmatch) := by
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Text.stripWhitespaceTypeArgs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stripWhitespaceTypeArgs

/-- A correctly applied whitespace operation fails hard when the input is not text. -/
theorem stripWhitespaceShapeError (hints : P4.Unparse.HEnv) (v : Lang.Il.value)
    (h : Runtime.Value.Get.text v = none) :
    (Interp_al.Effects.builtinEval hints "strip_all_whitespace" [] [v]).run =
      some (.error .err) := by
  cases v with
  | mk payload note region =>
    cases payload <;> simp_all [Runtime.Value.Get.text] <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.Text.stripWhitespaceShapeError' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stripWhitespaceShapeError

/-- Incorrect value arity is rejected before operation decoding. -/
theorem stripWhitespaceArity (hints : P4.Unparse.HEnv)
    (args : List Lang.Il.value) (h : args.length ≠ 1) :
    (Interp_al.Effects.builtinEval hints "strip_all_whitespace" [] args).run =
      some (.error .unmatch) := by
  cases args with
  | nil => rfl
  | cons arg args =>
    cases args with
    | nil => exact False.elim (h rfl)
    | cons arg2 rest => rfl

/-- info: 'P4SpecTec.Refine.Builtin.Text.stripWhitespaceArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stripWhitespaceArity

end P4SpecTec.Refine.Builtin.Text
