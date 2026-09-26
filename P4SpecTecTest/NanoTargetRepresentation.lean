import NanoP4Spec.«3.0-value»
import P4SpecTec.Refine.Value

/-!
Checked obstruction to the current typed Nano target interface. Successful
extract returns a raw extern, but every generated source `value` is a case.
A faithful runtime extension must explicitly replace these limitations; a
PACKET wrapper cannot preserve the present value relation.
-/

namespace P4SpecTecTest.NanoTargetRepresentation

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- No current generated Nano value represents any raw extern payload. -/
theorem rawExternUnrepresentable (note : Lang.Il.typ') (json : Lean.Json)
    (x : NanoP4Spec.value) : ¬ Rel (Runtime.Value.Make.extern note json) x := by
  cases x <;>
    simp [Rel, ToValue.toValue, NanoP4Spec.value.toValue,
      Runtime.Value.Make.extern, Runtime.Value.Make.case,
      Runtime.Value.Make.mk, canon, canon']

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.rawExternUnrepresentable'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rawExternUnrepresentable

/-- Increasing decoder fuel cannot recover a missing runtime constructor. -/
theorem rawExternUndecodable (fuel : Nat) (note : Lang.Il.typ') (json : Lean.Json) :
    NanoP4Spec.value.ofValue fuel (Runtime.Value.Make.extern note json) = none := by
  cases fuel <;> rfl

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.rawExternUndecodable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rawExternUndecodable

end P4SpecTecTest.NanoTargetRepresentation
