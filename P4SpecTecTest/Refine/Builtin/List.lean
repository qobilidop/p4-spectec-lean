import NanoP4Spec.«0-stdlib»
import P4SpecTec.Refine.Builtin.List

/-! Universal correspondence checks for the actual generated Nano list wrappers. -/

namespace P4SpecTecTest.Refine.Builtin.List

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- Actual generated distinctness agrees with raw dispatch on every related list. -/
theorem nanoDistinct {α : Type} [ToValue α] [BEq α] {v : Lang.Il.value} {xs : List α}
    (h : Rel v xs) (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ) :
    (Interp_al.Effects.builtinEval hints "distinct_" types [v]).run =
      (NanoP4Spec.«$distinct_» xs).map (Except.map toValue) := by
  exact P4SpecTec.Refine.Builtin.List.distinctRunOfRel h hints types

/-- info: 'P4SpecTecTest.Refine.Builtin.List.nanoDistinct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoDistinct

/-- Actual generated reversal and raw dispatch share the same represented result. -/
theorem nanoReverse {α : Type} [ToValue α] [BEq α] {v : Lang.Il.value} {xs : List α}
    (h : Rel v xs) (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "rev_" [typ] [v]).run = some (.ok out) ∧
      NanoP4Spec.«$rev_» xs = some (.ok xs.reverse) ∧ Rel out xs.reverse := by
  obtain ⟨out, run, rel⟩ := P4SpecTec.Refine.Builtin.List.reverseRunOfRel h hints typ
  exact ⟨out, run, rfl, rel⟩

/-- info: 'P4SpecTecTest.Refine.Builtin.List.nanoReverse' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoReverse

/-- Actual generated association agrees with raw dispatch, including absent keys. -/
theorem nanoAssoc {α β : Type} [ToValue α] [BEq α] [ToValue β] [BEq β]
    {key pairs : Lang.Il.value} {x : α} {xs : List (α × β)}
    (hk : Rel key x) (hp : Rel pairs xs) (hints : P4.Unparse.HEnv)
    (keyType valueType : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "assoc_" [keyType, valueType]
      [key, pairs]).run = some (.ok out) ∧
      NanoP4Spec.«$assoc_» x xs = some (.ok (P4SpecTec.Builtin.Lists.assoc_ x xs)) ∧
      Rel out (P4SpecTec.Builtin.Lists.assoc_ x xs) := by
  obtain ⟨out, run, rel⟩ := P4SpecTec.Refine.Builtin.List.assocRunOfRel
    hk hp hints keyType valueType
  exact ⟨out, run, rfl, rel⟩

/-- info: 'P4SpecTecTest.Refine.Builtin.List.nanoAssoc' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoAssoc

end P4SpecTecTest.Refine.Builtin.List
