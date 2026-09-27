import NanoP4Spec.«3.2-bits»
import P4SpecTec.Refine.Builtin.Numeric

/-! All eleven actual Nano numeric wrappers share the checked raw-dispatch contracts. -/

namespace P4SpecTecTest.Refine.Builtin.Numeric

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine
open P4SpecTec.Refine.Builtin.Numeric

/-- Universal contracts connect every Nano numeric wrapper to actual builtin dispatch.
The hypotheses retain all source metadata and distinguish numeric constructor tags. -/
theorem nanoNumerics {v w n bs : Lang.Il.value} {x y : Int} {width : Nat} {bits : List Bool}
    (hv : Rel v x) (hw : Rel w y) (hn : Rel n width) (hb : Rel bs bits)
    (hints : P4.Unparse.HEnv) :
    ((Interp_al.Effects.builtinEval hints "bitstr_to_int" [] [v, w]).run =
      (NanoP4Spec.«$bitstr_to_int» x y).map (Except.map toValue)) ∧
    ((Interp_al.Effects.builtinEval hints "int_to_bitstr" [] [v, w]).run =
      (NanoP4Spec.«$int_to_bitstr» x y).map (Except.map toValue)) ∧
    ((Interp_al.Effects.builtinEval hints "pow2" [] [n]).run =
      (NanoP4Spec.«$pow2» width).map (Except.map toValue)) ∧
    ((Interp_al.Effects.builtinEval hints "bneg" [] [v]).run =
      (NanoP4Spec.«$bneg» x).map (Except.map toValue)) ∧
    ((Interp_al.Effects.builtinEval hints "band" [] [v, w]).run =
      (NanoP4Spec.«$band» x y).map (Except.map toValue)) ∧
    ((Interp_al.Effects.builtinEval hints "bxor" [] [v, w]).run =
      (NanoP4Spec.«$bxor» x y).map (Except.map toValue)) ∧
    ((Interp_al.Effects.builtinEval hints "bor" [] [v, w]).run =
      (NanoP4Spec.«$bor» x y).map (Except.map toValue)) ∧
    ((Interp_al.Effects.builtinEval hints "bits_to_int_unsigned" [] [bs]).run =
      (NanoP4Spec.«$bits_to_int_unsigned» bits).map (Except.map toValue)) ∧
    ((Interp_al.Effects.builtinEval hints "bits_to_int_signed" [] [bs]).run =
      (NanoP4Spec.«$bits_to_int_signed» bits).map (Except.map toValue)) ∧
    ((Interp_al.Effects.builtinEval hints "int_to_bits_unsigned" [] [n, v]).run.map
      (Except.map canon) = (NanoP4Spec.«$int_to_bits_unsigned» width x).map
        (Except.map (fun result => canon (toValue result)))) ∧
    ((Interp_al.Effects.builtinEval hints "int_to_bits_signed" [] [n, v]).run.map
      (Except.map canon) = (NanoP4Spec.«$int_to_bits_signed» width x).map
        (Except.map (fun result => canon (toValue result)))) := by
  exact ⟨bitstrToIntRun hv hw hints,
    intToBitstrRun hv hw hints,
    pow2Run hn hints,
    bnegRun hv hints,
    bandRun hv hw hints,
    bxorRun hv hw hints,
    borRun hv hw hints,
    bitsToIntUnsignedRun hb hints,
    bitsToIntSignedRun hb hints,
    intToBitsUnsignedRun hn hv hints,
    intToBitsSignedRun hn hv hints⟩

/-- info: 'P4SpecTecTest.Refine.Builtin.Numeric.nanoNumerics' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoNumerics

-- The width boundary is inclusive, and rejected widths retain retryable failure.
private def mismatches {α : Type} : Option (Except Fail α) → Bool
  | some (.error .unmatch) => true
  | _ => false

#guard match NanoP4Spec.«$int_to_bits_unsigned» 2048 (-1) with
  | some (.ok bits) => bits.length == 2048
  | _ => false
#guard mismatches (NanoP4Spec.«$int_to_bits_unsigned» 2049 0)
#guard mismatches (NanoP4Spec.«$int_to_bits_signed» 2049 0)
#guard mismatches (NanoP4Spec.«$bitstr_to_int» 2049 0)
#guard mismatches (NanoP4Spec.«$int_to_bitstr» 2049 0)
#guard mismatches (NanoP4Spec.«$bits_to_int_signed» [])
#guard match NanoP4Spec.«$bits_to_int_unsigned» [] with
  | some (.ok i) => i == 0
  | _ => false

end P4SpecTecTest.Refine.Builtin.Numeric
