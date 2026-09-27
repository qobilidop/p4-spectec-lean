import NanoP4Spec.«0-stdlib»
import P4SpecTec.Refine.Builtin.Map

/-! Instantiate reusable map contracts with the actual generated Nano carrier. -/

namespace P4SpecTecTest.Refine.Builtin.Map

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- The reusable source encoding matches the actual Nano map carrier canonically. -/
theorem nanoMapEncoding {α β : Type} [ToValue α] [ToValue β] (xs : List (α × β)) :
    Rel (P4SpecTec.Refine.Builtin.Map.encode xs)
      (NanoP4Spec.set.lbrace_rbrace (xs.map fun p => NanoP4Spec.pair.colon p.1 p.2)) := by
  apply congrArg (fun entries =>
    (⟨.CaseV (.Brack (Value.atom .LBrace)
      (.Arg ⟨.ListV entries, dummy, Util.Source.no_region⟩) (Value.atom .RBrace)),
      dummy, Util.Source.no_region⟩ : Lang.Il.value))
  simp only [canons_eq_map, List.map_map]
  apply List.map_congr_left
  intro pair _
  rfl

/-- info: 'P4SpecTecTest.Refine.Builtin.Map.nanoMapEncoding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoMapEncoding

/-- The actual Nano map wrapper agrees with raw lookup on all related ordered maps. -/
theorem nanoFind {α β : Type} [ToValue α] [BEq α] [ToValue β] [BEq β]
    {map key : Lang.Il.value} {xs : List (α × β)} {x : α}
    (hm : Rel map
      (NanoP4Spec.set.lbrace_rbrace (xs.map fun p => NanoP4Spec.pair.colon p.1 p.2)))
    (hk : Rel key x) (hints : P4.Unparse.HEnv) (keyType valueType : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "find_map" [keyType, valueType]
      [map, key]).run = some (.ok out) ∧
      NanoP4Spec.«$find_map»
        (NanoP4Spec.set.lbrace_rbrace (xs.map fun p => NanoP4Spec.pair.colon p.1 p.2)) x =
        some (.ok (P4SpecTec.Builtin.Maps.find_map xs x)) ∧
      Rel out (P4SpecTec.Builtin.Maps.find_map xs x) := by
  have encoded : Rel map (P4SpecTec.Refine.Builtin.Map.encode xs) :=
    hm.trans (nanoMapEncoding xs).symm
  obtain ⟨out, run, rel⟩ := P4SpecTec.Refine.Builtin.Map.findRunOfRel
    encoded hk hints keyType valueType
  refine ⟨out, run, ?_, rel⟩
  simp only [NanoP4Spec.«$find_map», List.map_map, Function.comp_def, Prod.eta, List.map_id']
  rfl

/-- info: 'P4SpecTecTest.Refine.Builtin.Map.nanoFind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoFind

private def carrier {α β : Type} (xs : List (α × β)) : NanoP4Spec.map α β :=
  .lbrace_rbrace (xs.map fun p => .colon p.1 p.2)

/-- The independent ordered encoding matches lists of actual Nano map carriers. -/
theorem nanoMapsEncoding {α β : Type} [ToValue α] [ToValue β]
    (maps : List (List (α × β))) :
    Rel (toValue (maps.map P4SpecTec.Refine.Builtin.Map.encode)) (maps.map carrier) := by
  apply congrArg (fun entries =>
    (⟨.ListV entries, dummy, Util.Source.no_region⟩ : Lang.Il.value))
  simp only [canons_eq_map, List.map_map]
  apply List.map_congr_left
  intro map _
  exact nanoMapEncoding map

/-- info: 'P4SpecTecTest.Refine.Builtin.Map.nanoMapsEncoding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoMapsEncoding

/-- The actual multi-map wrapper preserves first-present ordering on all related maps. -/
theorem nanoFindMaps {α β : Type} [ToValue α] [BEq α] [ToValue β] [BEq β]
    {rawMaps key : Lang.Il.value} {maps : List (List (α × β))} {x : α}
    (hm : Rel rawMaps (maps.map carrier)) (hk : Rel key x)
    (hints : P4.Unparse.HEnv) (keyType valueType : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "find_maps" [keyType, valueType]
      [rawMaps, key]).run = some (.ok out) ∧
      NanoP4Spec.«$find_maps» (maps.map carrier) x =
        some (.ok (P4SpecTec.Builtin.Maps.find_maps maps x)) ∧
      Rel out (P4SpecTec.Builtin.Maps.find_maps maps x) := by
  have encoded : Rel rawMaps (maps.map P4SpecTec.Refine.Builtin.Map.encode) :=
    hm.trans (nanoMapsEncoding maps).symm
  obtain ⟨out, run, rel⟩ := P4SpecTec.Refine.Builtin.Map.findMapsRunOfRel
    encoded hk hints keyType valueType
  refine ⟨out, run, ?_, rel⟩
  simp only [NanoP4Spec.«$find_maps», carrier, List.map_map, Function.comp_def,
    Prod.eta, List.map_id']
  rfl

/-- info: 'P4SpecTecTest.Refine.Builtin.Map.nanoFindMaps' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoFindMaps

/-- Actual map addition preserves the whole ordered generated carrier result. -/
theorem nanoAdd {α β : Type} [ToValue α] [BEq α] [ToValue β] [BEq β]
    {map key val : Lang.Il.value} {xs : List (α × β)} {x : α} {y : β}
    (hm : Rel map (carrier xs)) (hk : Rel key x) (hv : Rel val y)
    (hints : P4.Unparse.HEnv) (keyType valueType : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "add_map" [keyType, valueType]
      [map, key, val]).run = some (.ok out) ∧
      NanoP4Spec.«$add_map» (carrier xs) x y =
        some (.ok (carrier (P4SpecTec.Builtin.Maps.add_map xs x y))) ∧
      Rel out (carrier (P4SpecTec.Builtin.Maps.add_map xs x y)) := by
  have encoded : Rel map (P4SpecTec.Refine.Builtin.Map.encode xs) :=
    hm.trans (nanoMapEncoding xs).symm
  obtain ⟨out, run, rel⟩ := P4SpecTec.Refine.Builtin.Map.addRunOfRel
    encoded hk hv hints keyType valueType
  refine ⟨out, run, ?_, rel.trans (nanoMapEncoding _)⟩
  simp only [NanoP4Spec.«$add_map», carrier, List.map_map, Function.comp_def,
    Prod.eta, List.map_id']
  congr 4

/-- info: 'P4SpecTecTest.Refine.Builtin.Map.nanoAdd' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoAdd

/-- Actual update shares the same ordered carrier preservation as addition. -/
theorem nanoUpdate {α β : Type} [ToValue α] [BEq α] [ToValue β] [BEq β]
    {map key val : Lang.Il.value} {xs : List (α × β)} {x : α} {y : β}
    (hm : Rel map (carrier xs)) (hk : Rel key x) (hv : Rel val y)
    (hints : P4.Unparse.HEnv) (keyType valueType : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "update_map" [keyType, valueType]
      [map, key, val]).run = some (.ok out) ∧
      NanoP4Spec.«$update_map» (carrier xs) x y =
        some (.ok (carrier (P4SpecTec.Builtin.Maps.update_map xs x y))) ∧
      Rel out (carrier (P4SpecTec.Builtin.Maps.update_map xs x y)) := by
  have encoded : Rel map (P4SpecTec.Refine.Builtin.Map.encode xs) :=
    hm.trans (nanoMapEncoding xs).symm
  obtain ⟨out, run, rel⟩ := P4SpecTec.Refine.Builtin.Map.updateRunOfRel
    encoded hk hv hints keyType valueType
  refine ⟨out, run, ?_, rel.trans (nanoMapEncoding _)⟩
  simp only [NanoP4Spec.«$update_map», carrier, List.map_map, Function.comp_def,
    Prod.eta, List.map_id']
  congr 4

/-- info: 'P4SpecTecTest.Refine.Builtin.Map.nanoUpdate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nanoUpdate

end P4SpecTecTest.Refine.Builtin.Map
