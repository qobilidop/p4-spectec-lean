import P4SpecTec.Refine.Builtin.Collection
import P4SpecTec.Refine.Builtin.List

/-! Map contracts use the source brace/colon encoding and preserve first-match ordering. -/

namespace P4SpecTec.Refine.Builtin.Map

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- The existing source map encoding for typed key/value pairs, without normalization. -/
def encode {α β : Type} [ToValue α] [ToValue β] (xs : List (α × β)) : Lang.Il.value :=
  Collection.bracketed (xs.map fun p => Collection.colon (toValue p.1) (toValue p.2))

/-- Canonically related colon-pair lists decode into separately related components. -/
theorem decodePairs {α β : Type} [ToValue α] [ToValue β]
    (raws : List Lang.Il.value) (xs : List (α × β))
    (h : canons raws = canons
      (xs.map fun p => Collection.colon (toValue p.1) (toValue p.2))) :
    ∃ pairs, raws.mapM P4SpecTec.Builtin.Call.pair_of_value = some pairs ∧
      List.Forall₂ (fun p q => Rel p.1 q.1 ∧ Rel p.2 q.2) pairs xs := by
  induction xs generalizing raws with
  | nil =>
    have hn := canons_eq_nil h
    subst raws
    exact ⟨[], rfl, .nil⟩
  | cons xy xs ih =>
    obtain ⟨raw, rest, rfl, hr, ht⟩ := canons_eq_cons h
    obtain ⟨rx, ry, hd, hx, hy⟩ := Collection.colonDecodeOfRel hr
    obtain ⟨pairs, hp, hs⟩ := ih rest ht
    refine ⟨(rx, ry) :: pairs, ?_, .cons ⟨hx, hy⟩ hs⟩
    simp only [List.mapM_cons, hd, hp]
    rfl

/-- info: 'P4SpecTec.Refine.Builtin.Map.decodePairs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodePairs

/-- Every related source map decodes while retaining its ordered pair relation. -/
theorem decodeOfRel {α β : Type} [ToValue α] [ToValue β]
    {raw : Lang.Il.value} {xs : List (α × β)} (h : Rel raw (encode xs)) :
    ∃ pairs, (do
      let entries ← P4SpecTec.Builtin.Call.map_of_value raw
      entries.mapM P4SpecTec.Builtin.Call.pair_of_value) = some pairs ∧
      List.Forall₂ (fun p q => Rel p.1 q.1 ∧ Rel p.2 q.2) pairs xs := by
  obtain ⟨entries, hd, hs⟩ := Collection.bracketedDecodeOfRel h
  obtain ⟨pairs, hp, hr⟩ := decodePairs entries xs hs
  refine ⟨pairs, ?_, hr⟩
  change (P4SpecTec.Builtin.Call.set_of_value raw >>= fun entries =>
    entries.mapM P4SpecTec.Builtin.Call.pair_of_value) = some pairs
  rw [hd]
  exact hp

/-- info: 'P4SpecTec.Refine.Builtin.Map.decodeOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeOfRel

/-- Actual map lookup preserves the first optional result, including an absent key. -/
theorem findRunOfRel {α β : Type} [ToValue α] [ToValue β]
    {map key : Lang.Il.value} {xs : List (α × β)} {x : α}
    (hm : Rel map (encode xs)) (hk : Rel key x) (hints : P4.Unparse.HEnv)
    (keyType valueType : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "find_map" [keyType, valueType]
      [map, key]).run = some (.ok out) ∧ Rel out (P4SpecTec.Builtin.Maps.find_map xs x) := by
  obtain ⟨decoded, hd, hr⟩ := decodeOfRel hm
  let answer := P4SpecTec.Builtin.Maps.find_map decoded key
  refine ⟨Runtime.Value.Make.opt (.IterT valueType .Opt) answer, ?_, ?_⟩
  · have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "find_map"
        [keyType, valueType] [map, key] = .ok (do
          let entries ← P4SpecTec.Builtin.Call.map_of_value map
          let ps ← entries.mapM P4SpecTec.Builtin.Call.pair_of_value
          pure (Runtime.Value.Make.opt (.IterT valueType .Opt)
            (P4SpecTec.Builtin.Maps.find_map ps key))) := by rfl
    have result : (do
        let entries ← P4SpecTec.Builtin.Call.map_of_value map
        let ps ← entries.mapM P4SpecTec.Builtin.Call.pair_of_value
        pure (Runtime.Value.Make.opt (.IterT valueType .Opt)
          (P4SpecTec.Builtin.Maps.find_map ps key))) =
        some (Runtime.Value.Make.opt (.IterT valueType .Opt) answer) := by
      rw [← bind_assoc, hd]
      rfl
    unfold Interp_al.Effects.builtinEval
    rw [dispatch, result]
    rfl
  · have ho := P4SpecTec.Refine.Builtin.List.assocPairsRel hk hr
    change Rel (toValue answer) (P4SpecTec.Builtin.Maps.find_map xs x) at ho
    cases he : answer with
    | none => rw [he] at ho; exact ho
    | some raw => rw [he] at ho; exact ho

/-- info: 'P4SpecTec.Refine.Builtin.Map.findRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms findRunOfRel

/-- Ordered lists of related maps decode with their separate pair relations intact. -/
theorem decodeMaps {α β : Type} [ToValue α] [ToValue β]
    (raws : List Lang.Il.value) (maps : List (List (α × β)))
    (h : canons raws = canons (maps.map encode)) :
    ∃ decoded, raws.mapM (fun raw => do
      let entries ← P4SpecTec.Builtin.Call.map_of_value raw
      entries.mapM P4SpecTec.Builtin.Call.pair_of_value) = some decoded ∧
      List.Forall₂ (List.Forall₂ (fun p q => Rel p.1 q.1 ∧ Rel p.2 q.2)) decoded maps := by
  induction maps generalizing raws with
  | nil =>
    have hn := canons_eq_nil h
    subst raws
    exact ⟨[], rfl, .nil⟩
  | cons map maps ih =>
    obtain ⟨raw, rest, rfl, hr, ht⟩ := canons_eq_cons h
    obtain ⟨pairs, hd, hp⟩ := decodeOfRel hr
    obtain ⟨decoded, hs, hm⟩ := ih rest ht
    refine ⟨pairs :: decoded, ?_, .cons hp hm⟩
    simp only [List.mapM_cons, hd, hs]
    rfl

/-- info: 'P4SpecTec.Refine.Builtin.Map.decodeMaps' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodeMaps

/-- Ordered multi-map lookup preserves the first present result and complete absence. -/
theorem findMapsRel {α β : Type} [ToValue α] [ToValue β]
    {raw : Lang.Il.value} {key : α} (hk : Rel raw key)
    {raws : List (List (Lang.Il.value × Lang.Il.value))} {maps : List (List (α × β))}
    (h : List.Forall₂ (List.Forall₂ (fun p q => Rel p.1 q.1 ∧ Rel p.2 q.2)) raws maps) :
    Rel (toValue (P4SpecTec.Builtin.Maps.find_maps raws raw))
      (P4SpecTec.Builtin.Maps.find_maps maps key) := by
  induction h with
  | nil => rfl
  | @cons p q ps qs hp hs ih =>
    have lookup := P4SpecTec.Refine.Builtin.List.assocPairsRel hk hp
    change Rel (toValue (P4SpecTec.Builtin.Maps.find raw p))
      (P4SpecTec.Builtin.Maps.find key q) at lookup
    simp only [P4SpecTec.Builtin.Maps.find_maps, List.findSome?_cons]
    cases hf : P4SpecTec.Builtin.Maps.find raw p <;>
      cases hg : P4SpecTec.Builtin.Maps.find key q <;>
      rw [hf, hg] at lookup
    · exact ih
    · cases congrArg (fun v : Lang.Il.value => v.it) lookup
    · cases congrArg (fun v : Lang.Il.value => v.it) lookup
    · exact lookup

/-- info: 'P4SpecTec.Refine.Builtin.Map.findMapsRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms findMapsRel

/-- Actual multi-map dispatch preserves ordered lookup on every represented map list. -/
theorem findMapsRunOfRel {α β : Type} [ToValue α] [ToValue β]
    {rawMaps key : Lang.Il.value} {maps : List (List (α × β))} {x : α}
    (hm : Rel rawMaps (maps.map encode)) (hk : Rel key x) (hints : P4.Unparse.HEnv)
    (keyType valueType : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "find_maps" [keyType, valueType]
      [rawMaps, key]).run = some (.ok out) ∧
      Rel out (P4SpecTec.Builtin.Maps.find_maps maps x) := by
  obtain ⟨raws, hv, hs⟩ := P4SpecTec.Refine.Builtin.List.listPayloadOfRel hm
  change canons raws = canons ((maps.map encode).map id) at hs
  rw [List.map_id] at hs
  obtain ⟨decoded, hd, hr⟩ := decodeMaps raws maps hs
  let answer := P4SpecTec.Builtin.Maps.find_maps decoded key
  refine ⟨Runtime.Value.Make.opt (.IterT valueType .Opt) answer, ?_, ?_⟩
  · cases rawMaps with
    | mk payload note region =>
      change payload = .ListV raws at hv
      subst payload
      have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "find_maps"
          [keyType, valueType] [⟨.ListV raws, note, region⟩, key] = .ok (do
            let ms ← raws.mapM (fun raw => do
              let entries ← P4SpecTec.Builtin.Call.map_of_value raw
              entries.mapM P4SpecTec.Builtin.Call.pair_of_value)
            pure (Runtime.Value.Make.opt (.IterT valueType .Opt)
              (P4SpecTec.Builtin.Maps.find_maps ms key))) := by rfl
      unfold Interp_al.Effects.builtinEval
      rw [dispatch, hd]
      rfl
  · have ho := findMapsRel hk hr
    change Rel (toValue answer) (P4SpecTec.Builtin.Maps.find_maps maps x) at ho
    cases he : answer with
    | none => rw [he] at ho; exact ho
    | some raw => rw [he] at ho; exact ho

/-- info: 'P4SpecTec.Refine.Builtin.Map.findMapsRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms findMapsRunOfRel

/-- Source pair notes do not change separately related key/value observations. -/
theorem pairEncodeRel {α β : Type} [ToValue α] [ToValue β]
    {key val : Lang.Il.value} {x : α} {y : β} (hk : Rel key x) (hv : Rel val y)
    (keyType valueType : Lang.Il.typ) :
    Rel (P4SpecTec.Builtin.Call.make_pair keyType valueType key val)
      (Collection.colon (toValue x) (toValue y)) := by
  change (⟨.CaseV (.Seq [.Arg (canon key), .Atom (Value.atom (.Operator ":")),
      .Arg (canon val)]), dummy, Util.Source.no_region⟩ : Lang.Il.value) = _
  rw [hk, hv]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Map.pairEncodeRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairEncodeRel

/-- Re-encoding related ordered pairs preserves the complete source map observation. -/
theorem encodePairsRel {α β : Type} [ToValue α] [ToValue β]
    {raws : List (Lang.Il.value × Lang.Il.value)} {xs : List (α × β)}
    (h : List.Forall₂ (fun p q => Rel p.1 q.1 ∧ Rel p.2 q.2) raws xs)
    (keyType valueType : Lang.Il.typ) :
    Rel (P4SpecTec.Builtin.Call.value_of_map keyType valueType
      (raws.map fun p => P4SpecTec.Builtin.Call.make_pair keyType valueType p.1 p.2))
      (encode xs) := by
  apply congrArg (fun entries =>
    (⟨.CaseV (.Brack (Value.atom .LBrace)
      (.Arg ⟨.ListV entries, dummy, Util.Source.no_region⟩) (Value.atom .RBrace)),
      dummy, Util.Source.no_region⟩ : Lang.Il.value))
  induction h with
  | nil => rfl
  | @cons p q ps qs hp hs ih =>
    have pairEq : canon (P4SpecTec.Builtin.Call.make_pair keyType valueType p.1 p.2) =
        canon (Collection.colon (toValue q.1) (toValue q.2)) :=
      pairEncodeRel hp.1 hp.2 keyType valueType
    simp only [List.map_cons, canons, pairEq, ih]

/-- info: 'P4SpecTec.Refine.Builtin.Map.encodePairsRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms encodePairsRel

/-- Update replaces the first equal key or appends, preserving related ordered pairs. -/
theorem updatePairsRel {α β : Type} [ToValue α] [ToValue β]
    {key val : Lang.Il.value} {x : α} {y : β} (hk : Rel key x) (hv : Rel val y)
    {raws : List (Lang.Il.value × Lang.Il.value)} {xs : List (α × β)}
    (h : List.Forall₂ (fun p q => Rel p.1 q.1 ∧ Rel p.2 q.2) raws xs) :
    List.Forall₂ (fun p q => Rel p.1 q.1 ∧ Rel p.2 q.2)
      (P4SpecTec.Builtin.Maps.update key val raws) (P4SpecTec.Builtin.Maps.update x y xs) := by
  induction h with
  | nil => exact .cons ⟨hk, hv⟩ .nil
  | @cons p q ps qs hp hs ih =>
    have he : valueEq key p.1 = valueEq x q.1 := eq_of_rel hk hp.1
    simp only [P4SpecTec.Builtin.Maps.update]
    rw [he]
    cases ht : valueEq x q.1
    · exact .cons hp ih
    · exact .cons ⟨hk, hv⟩ hs

/-- info: 'P4SpecTec.Refine.Builtin.Map.updatePairsRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms updatePairsRel

/-- Actual map addition replaces the first equal key or appends while preserving all pairs. -/
theorem addRunOfRel {α β : Type} [ToValue α] [ToValue β]
    {map key val : Lang.Il.value} {xs : List (α × β)} {x : α} {y : β}
    (hm : Rel map (encode xs)) (hk : Rel key x) (hv : Rel val y)
    (hints : P4.Unparse.HEnv) (keyType valueType : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "add_map" [keyType, valueType]
      [map, key, val]).run = some (.ok out) ∧
      Rel out (encode (P4SpecTec.Builtin.Maps.add_map xs x y)) := by
  obtain ⟨decoded, hd, hr⟩ := decodeOfRel hm
  let answer := P4SpecTec.Builtin.Maps.add_map decoded key val
  let out := P4SpecTec.Builtin.Call.value_of_map keyType valueType
    (answer.map fun p => P4SpecTec.Builtin.Call.make_pair keyType valueType p.1 p.2)
  refine ⟨out, ?_, ?_⟩
  · have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "add_map"
        [keyType, valueType] [map, key, val] = .ok (do
          let entries ← P4SpecTec.Builtin.Call.map_of_value map
          let ps ← entries.mapM P4SpecTec.Builtin.Call.pair_of_value
          pure (P4SpecTec.Builtin.Call.value_of_map keyType valueType
            ((P4SpecTec.Builtin.Maps.add_map ps key val).map fun p =>
              P4SpecTec.Builtin.Call.make_pair keyType valueType p.1 p.2))) := by rfl
    have result : (do
        let entries ← P4SpecTec.Builtin.Call.map_of_value map
        let ps ← entries.mapM P4SpecTec.Builtin.Call.pair_of_value
        pure (P4SpecTec.Builtin.Call.value_of_map keyType valueType
          ((P4SpecTec.Builtin.Maps.add_map ps key val).map fun p =>
            P4SpecTec.Builtin.Call.make_pair keyType valueType p.1 p.2))) = some out := by
      rw [← bind_assoc, hd]
      rfl
    unfold Interp_al.Effects.builtinEval
    rw [dispatch, result]
    rfl
  · exact encodePairsRel (updatePairsRel hk hv hr) keyType valueType

/-- info: 'P4SpecTec.Refine.Builtin.Map.addRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms addRunOfRel

/-- Actual map update has the same first-replacement/append contract as map addition. -/
theorem updateRunOfRel {α β : Type} [ToValue α] [ToValue β]
    {map key val : Lang.Il.value} {xs : List (α × β)} {x : α} {y : β}
    (hm : Rel map (encode xs)) (hk : Rel key x) (hv : Rel val y)
    (hints : P4.Unparse.HEnv) (keyType valueType : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "update_map" [keyType, valueType]
      [map, key, val]).run = some (.ok out) ∧
      Rel out (encode (P4SpecTec.Builtin.Maps.update_map xs x y)) := by
  have branch : (Interp_al.Effects.builtinEval hints "update_map" [keyType, valueType]
      [map, key, val]).run =
      (Interp_al.Effects.builtinEval hints "add_map" [keyType, valueType]
        [map, key, val]).run := rfl
  rw [branch]
  exact addRunOfRel hm hk hv hints keyType valueType

/-- info: 'P4SpecTec.Refine.Builtin.Map.updateRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms updateRunOfRel

/-- All four Nano map operations reject incorrect value arity before decoding. -/
theorem mapArity (name : String) (arity : Nat)
    (operation : (name, arity) ∈
      [("find_map", 2), ("find_maps", 2), ("add_map", 3), ("update_map", 3)])
    (hints : P4.Unparse.HEnv) (keyType valueType : Lang.Il.typ)
    (args : List Lang.Il.value) (wrong : args.length ≠ arity) :
    (Interp_al.Effects.builtinEval hints name [keyType, valueType] args).run =
      some (.error .unmatch) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at operation
  rcases operation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    cases args with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b rest =>
        cases rest with
        | nil => first | exact False.elim (wrong rfl) | rfl
        | cons c rest =>
          cases rest with
          | nil => first | exact False.elim (wrong rfl) | rfl
          | cons d rest => rfl

/-- info: 'P4SpecTec.Refine.Builtin.Map.mapArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapArity

/-- All map operations require precisely two supplied type arguments. -/
theorem mapTypeArity (name : String)
    (operation : name ∈ ["find_map", "find_maps", "add_map", "update_map"])
    (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ) (args : List Lang.Il.value)
    (wrong : types.length ≠ 2) :
    (Interp_al.Effects.builtinEval hints name types args).run = some (.error .unmatch) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at operation
  rcases operation with rfl | rfl | rfl | rfl
  all_goals
    cases types with
    | nil => rfl
    | cons a rest =>
      cases rest with
      | nil => rfl
      | cons b rest =>
        cases rest with
        | nil => exact False.elim (wrong rfl)
        | cons c rest => rfl

/-- info: 'P4SpecTec.Refine.Builtin.Map.mapTypeArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapTypeArity

/-- Failed source map decoding is a legacy mismatch, not a fabricated absent-key result. -/
theorem findDecodeMismatch (map key : Lang.Il.value) (hints : P4.Unparse.HEnv)
    (keyType valueType : Lang.Il.typ)
    (failed : (do
      let entries ← P4SpecTec.Builtin.Call.map_of_value map
      entries.mapM P4SpecTec.Builtin.Call.pair_of_value) = none) :
    (Interp_al.Effects.builtinEval hints "find_map" [keyType, valueType]
      [map, key]).run = some (.error .unmatch) := by
  have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "find_map"
      [keyType, valueType] [map, key] = .ok (do
        let entries ← P4SpecTec.Builtin.Call.map_of_value map
        let ps ← entries.mapM P4SpecTec.Builtin.Call.pair_of_value
        pure (Runtime.Value.Make.opt (.IterT valueType .Opt)
          (P4SpecTec.Builtin.Maps.find_map ps key))) := by rfl
  have result : (do
      let entries ← P4SpecTec.Builtin.Call.map_of_value map
      let ps ← entries.mapM P4SpecTec.Builtin.Call.pair_of_value
      pure (Runtime.Value.Make.opt (.IterT valueType .Opt)
        (P4SpecTec.Builtin.Maps.find_map ps key))) = none := by
    rw [← bind_assoc, failed]
    rfl
  unfold Interp_al.Effects.builtinEval
  rw [dispatch, result]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Map.findDecodeMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms findDecodeMismatch

/-- Map addition retains a decoding failure instead of repairing the input collection. -/
theorem addDecodeMismatch (map key val : Lang.Il.value) (hints : P4.Unparse.HEnv)
    (keyType valueType : Lang.Il.typ)
    (failed : (do
      let entries ← P4SpecTec.Builtin.Call.map_of_value map
      entries.mapM P4SpecTec.Builtin.Call.pair_of_value) = none) :
    (Interp_al.Effects.builtinEval hints "add_map" [keyType, valueType]
      [map, key, val]).run = some (.error .unmatch) := by
  have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "add_map"
      [keyType, valueType] [map, key, val] = .ok (do
        let entries ← P4SpecTec.Builtin.Call.map_of_value map
        let ps ← entries.mapM P4SpecTec.Builtin.Call.pair_of_value
        pure (P4SpecTec.Builtin.Call.value_of_map keyType valueType
          ((P4SpecTec.Builtin.Maps.add_map ps key val).map fun p =>
            P4SpecTec.Builtin.Call.make_pair keyType valueType p.1 p.2))) := by rfl
  have result : (do
      let entries ← P4SpecTec.Builtin.Call.map_of_value map
      let ps ← entries.mapM P4SpecTec.Builtin.Call.pair_of_value
      pure (P4SpecTec.Builtin.Call.value_of_map keyType valueType
        ((P4SpecTec.Builtin.Maps.add_map ps key val).map fun p =>
          P4SpecTec.Builtin.Call.make_pair keyType valueType p.1 p.2))) = none := by
    rw [← bind_assoc, failed]
    rfl
  unfold Interp_al.Effects.builtinEval
  rw [dispatch, result]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Map.addDecodeMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms addDecodeMismatch

/-- Map update retains the same source decoding failures as addition. -/
theorem updateDecodeMismatch (map key val : Lang.Il.value) (hints : P4.Unparse.HEnv)
    (keyType valueType : Lang.Il.typ)
    (failed : (do
      let entries ← P4SpecTec.Builtin.Call.map_of_value map
      entries.mapM P4SpecTec.Builtin.Call.pair_of_value) = none) :
    (Interp_al.Effects.builtinEval hints "update_map" [keyType, valueType]
      [map, key, val]).run = some (.error .unmatch) := by
  change (Interp_al.Effects.builtinEval hints "add_map" [keyType, valueType]
    [map, key, val]).run = some (.error .unmatch)
  exact addDecodeMismatch map key val hints keyType valueType failed

/-- info: 'P4SpecTec.Refine.Builtin.Map.updateDecodeMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms updateDecodeMismatch

/-- A malformed map in multi-map lookup is rejected before searching any decoded result. -/
theorem findMapsDecodeMismatch (maps key : Lang.Il.value) (hints : P4.Unparse.HEnv)
    (keyType valueType : Lang.Il.typ)
    (failed : (do
      let raws ← Runtime.Value.Get.list maps
      raws.mapM (fun raw => do
        let entries ← P4SpecTec.Builtin.Call.map_of_value raw
        entries.mapM P4SpecTec.Builtin.Call.pair_of_value)) = none) :
    (Interp_al.Effects.builtinEval hints "find_maps" [keyType, valueType]
      [maps, key]).run = some (.error .unmatch) := by
  have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "find_maps"
      [keyType, valueType] [maps, key] = .ok (do
        let raws ← Runtime.Value.Get.list maps
        let decoded ← raws.mapM (fun raw => do
          let entries ← P4SpecTec.Builtin.Call.map_of_value raw
          entries.mapM P4SpecTec.Builtin.Call.pair_of_value)
        pure (Runtime.Value.Make.opt (.IterT valueType .Opt)
          (P4SpecTec.Builtin.Maps.find_maps decoded key))) := by rfl
  have result : (do
      let raws ← Runtime.Value.Get.list maps
      let decoded ← raws.mapM (fun raw => do
        let entries ← P4SpecTec.Builtin.Call.map_of_value raw
        entries.mapM P4SpecTec.Builtin.Call.pair_of_value)
      pure (Runtime.Value.Make.opt (.IterT valueType .Opt)
        (P4SpecTec.Builtin.Maps.find_maps decoded key))) = none := by
    rw [← bind_assoc, failed]
    rfl
  unfold Interp_al.Effects.builtinEval
  rw [dispatch, result]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Map.findMapsDecodeMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms findMapsDecodeMismatch

end P4SpecTec.Refine.Builtin.Map
