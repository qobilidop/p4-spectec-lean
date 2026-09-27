import P4SpecTec.Refine.Builtin.Collection
import P4SpecTec.Refine.Builtin.List
import P4SpecTec.Refine.ValueOrder

/-! Set builtin contracts preserve ordered canonical elements through source normalization. -/

namespace P4SpecTec.Refine.Builtin.Set

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine
open P4SpecTec.Lang.Il

private abbrev before (a b : value) : Bool := Runtime.Value.compare a b != .gt

private theorem canonsMerge {as bs cs ds : List value}
    (ha : canons as = canons cs) (hb : canons bs = canons ds) :
    canons (as.merge bs before) = canons (cs.merge ds before) := by
  cases as with
  | nil =>
    have hc := canons_eq_nil ha.symm
    subst cs
    simpa using hb
  | cons a as =>
    cases cs with
    | nil => simp [canons] at ha
    | cons c cs =>
      obtain ⟨hac, has⟩ := List.cons.inj ha
      cases bs with
      | nil =>
        have hd := canons_eq_nil hb.symm
        subst ds
        simpa using ha
      | cons b bs =>
        cases ds with
        | nil => simp [canons] at hb
        | cons d ds =>
          obtain ⟨hbd, hbs⟩ := List.cons.inj hb
          have he : before a b = before c d :=
            congrArg (fun o => o != .gt) (ValueOrder.compareOfCanon hac hbd)
          simp only [List.cons_merge_cons, he]
          split
          · simp only [canons]
            exact congr (congrArg List.cons hac) (canonsMerge has hb)
          · simp only [canons]
            exact congr (congrArg List.cons hbd) (canonsMerge ha hbs)
termination_by as.length + bs.length

private theorem canonsSort {as bs : List value} (h : canons as = canons bs) :
    canons (as.mergeSort before) = canons (bs.mergeSort before) := by
  have hl : as.length = bs.length := by simpa [canons_eq_map] using congrArg List.length h
  match as, bs with
  | [], [] => rfl
  | [a], [b] => simpa using h
  | a :: b :: as, c :: d :: bs =>
    simp only [List.mergeSort, List.MergeSort.Internal.splitInTwo_fst,
      List.MergeSort.Internal.splitInTwo_snd]
    apply canonsMerge
    · apply canonsSort
      simpa only [canons_eq_map, List.map_take, hl] using congrArg (List.take _) h
    · apply canonsSort
      simpa only [canons_eq_map, List.map_drop, hl] using congrArg (List.drop _) h
  | [], _ :: _ | _ :: _, [] | [_], _ :: _ :: _ | _ :: _ :: _, [_] => simp at hl
termination_by as.length

private theorem canonsDedup {as bs : List value} (h : canons as = canons bs) :
    canons (P4SpecTec.Builtin.Sets.normalize.dedup as) =
      canons (P4SpecTec.Builtin.Sets.normalize.dedup bs) := by
  match as, bs with
  | [], [] => rfl
  | [a], [b] => exact h
  | a :: b :: as, c :: d :: bs =>
    obtain ⟨hac, ht⟩ := List.cons.inj h
    obtain ⟨hbd, _⟩ := List.cons.inj ht
    have he : valueEq a b = valueEq c d := eq_of_canon hac hbd
    simp only [P4SpecTec.Builtin.Sets.normalize.dedup, he]
    split
    · exact canonsDedup ht
    · simp only [canons]
      exact congr (congrArg List.cons hac) (canonsDedup ht)
  | [], _ :: _ | _ :: _, [] | [_], _ :: _ :: _ | _ :: _ :: _, [_] =>
    simp [canons] at h
termination_by as.length

/-- Source normalization preserves the exact ordered canonical list of related elements. -/
theorem normalizeOfCanons {as bs : List value} (h : canons as = canons bs) :
    canons (P4SpecTec.Builtin.Sets.normalize as) =
      canons (P4SpecTec.Builtin.Sets.normalize bs) :=
  canonsDedup (canonsSort h)

/-- info: 'P4SpecTec.Refine.Builtin.Set.normalizeOfCanons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms normalizeOfCanons
#audit_axioms normalizeOfCanons

private theorem mapDedup {α : Type} [ToValue α] (xs : List α) :
    (P4SpecTec.Builtin.Sets.normalize.dedup xs).map toValue =
      P4SpecTec.Builtin.Sets.normalize.dedup (xs.map toValue) := by
  match xs with
  | [] => rfl
  | [a] => rfl
  | a :: b :: xs =>
    simp only [P4SpecTec.Builtin.Sets.normalize.dedup, List.map_cons]
    have he : valueEq (toValue a) (toValue b) = valueEq a b := rfl
    rw [he]
    split <;> simp only [List.map_cons, mapDedup]

/-- Encoding commutes with actual sorting and representative-preserving deduplication. -/
theorem mapNormalize {α : Type} [ToValue α] (xs : List α) :
    (P4SpecTec.Builtin.Sets.normalize xs).map toValue =
      P4SpecTec.Builtin.Sets.normalize (xs.map toValue) := by
  unfold P4SpecTec.Builtin.Sets.normalize
  rw [mapDedup, List.map_mergeSort (s := fun a b : value => valueCompare a b != .gt)]
  intros
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Set.mapNormalize' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapNormalize
#audit_axioms mapNormalize

private theorem memRelated {α : Type} [ToValue α] {v : value} {x : α}
    {raws : List value} {xs : List α} (hx : Rel v x)
    (hs : canons raws = canons (xs.map toValue)) :
    P4SpecTec.Builtin.Sets.mem v raws = P4SpecTec.Builtin.Sets.mem x xs := by
  have h := List.anyEqOfCanons hx hs
  change raws.any (Runtime.Value.eq v) =
    xs.any (fun y => Runtime.Value.eq (toValue x) (toValue y))
  simpa only [List.any_map, Function.comp_def] using h

private theorem filterRelated {α : Type} [ToValue α] {raws : List value} {xs : List α}
    {p : value → Bool} {q : α → Bool} (hs : canons raws = canons (xs.map toValue))
    (hp : ∀ v x, Rel v x → p v = q x) :
    canons (raws.filter p) = canons ((xs.filter q).map toValue) := by
  match raws, xs with
  | [], [] => rfl
  | v :: raws, x :: xs =>
    obtain ⟨hx, ht⟩ := List.cons.inj hs
    simp only [List.filter_cons, hp v x hx]
    split <;> simp only [List.map_cons, canons, hx, filterRelated ht hp]
  | [], _ :: _ | _ :: _, [] => simp [canons] at hs

private theorem subRelated {α : Type} [ToValue α] {raws bs : List value} {xs ys : List α}
    (ha : canons raws = canons (xs.map toValue))
    (hb : canons bs = canons (ys.map toValue)) :
    P4SpecTec.Builtin.Sets.sub_set raws bs = P4SpecTec.Builtin.Sets.sub_set xs ys := by
  match raws, xs with
  | [], [] => rfl
  | v :: raws, x :: xs =>
    obtain ⟨hx, ht⟩ := List.cons.inj ha
    simp only [P4SpecTec.Builtin.Sets.sub_set, List.all_cons, memRelated hx hb]
    exact congrArg (fun z => P4SpecTec.Builtin.Sets.mem x ys && z) (subRelated ht hb)
  | [], _ :: _ | _ :: _, [] => simp [canons] at ha

private theorem resultRel {raws expected : List value} (typ : Lang.Il.typ)
    (h : canons raws = canons expected) :
    Rel (P4SpecTec.Builtin.Call.value_of_set typ (P4SpecTec.Builtin.Sets.normalize raws))
      (Collection.bracketed (P4SpecTec.Builtin.Sets.normalize expected)) := by
  have hn := normalizeOfCanons h
  rw [show P4SpecTec.Builtin.Call.value_of_set typ
      (P4SpecTec.Builtin.Sets.normalize raws) =
      P4SpecTec.Builtin.Call.value_of_set typ raws by
        unfold P4SpecTec.Builtin.Call.value_of_set
        rw [ValueOrder.normalizeIdempotent]]
  change (⟨.CaseV (.Brack _ (.Arg ⟨.ListV _, dummy, _⟩) _), dummy, _⟩ : value) = _
  rw [hn]
  rfl

/-- Intersection dispatch agrees on arbitrary represented elements, including extern payloads. -/
theorem intersectRunOfRel {α : Type} [ToValue α] {a b : value} {xs ys : List α}
    (ha : Rel a (Collection.bracketed (xs.map toValue)))
    (hb : Rel b (Collection.bracketed (ys.map toValue)))
    (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "intersect_set" [typ] [a, b]).run =
      some (.ok out) ∧
      Rel out (Collection.bracketed
        ((P4SpecTec.Builtin.Sets.intersect_set xs ys).map toValue)) := by
  obtain ⟨raws, da, ca⟩ := Collection.bracketedDecodeOfRel ha
  obtain ⟨bs, db, cb⟩ := Collection.bracketedDecodeOfRel hb
  refine ⟨P4SpecTec.Builtin.Call.value_of_set typ
    (P4SpecTec.Builtin.Sets.intersect_set raws bs), ?_, ?_⟩
  · have dispatch := (show P4SpecTec.Builtin.Call.invokeWithHints hints
        "intersect_set" [typ] [a, b] =
        .ok (do
          let as ← P4SpecTec.Builtin.Call.set_of_value a
          let bs ← P4SpecTec.Builtin.Call.set_of_value b
          pure (P4SpecTec.Builtin.Call.value_of_set typ
            (P4SpecTec.Builtin.Sets.intersect_set as bs))) from by rfl)
    unfold Interp_al.Effects.builtinEval
    rw [dispatch, da, db]
    rfl
  · unfold P4SpecTec.Builtin.Sets.intersect_set
    rw [mapNormalize]
    apply resultRel
    exact filterRelated ca fun v x hx => memRelated hx cb

/-- info: 'P4SpecTec.Refine.Builtin.Set.intersectRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intersectRunOfRel
#audit_axioms intersectRunOfRel

/-- Union dispatch agrees on arbitrary represented elements, including extern payloads. -/
theorem unionRunOfRel {α : Type} [ToValue α] {a b : value} {xs ys : List α}
    (ha : Rel a (Collection.bracketed (xs.map toValue)))
    (hb : Rel b (Collection.bracketed (ys.map toValue)))
    (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "union_set" [typ] [a, b]).run =
      some (.ok out) ∧
      Rel out (Collection.bracketed ((P4SpecTec.Builtin.Sets.union_set xs ys).map toValue)) := by
  obtain ⟨raws, da, ca⟩ := Collection.bracketedDecodeOfRel ha
  obtain ⟨bs, db, cb⟩ := Collection.bracketedDecodeOfRel hb
  refine ⟨P4SpecTec.Builtin.Call.value_of_set typ
    (P4SpecTec.Builtin.Sets.union_set raws bs), ?_, ?_⟩
  · have dispatch := (show P4SpecTec.Builtin.Call.invokeWithHints hints
        "union_set" [typ] [a, b] =
        .ok (do
          let as ← P4SpecTec.Builtin.Call.set_of_value a
          let bs ← P4SpecTec.Builtin.Call.set_of_value b
          pure (P4SpecTec.Builtin.Call.value_of_set typ
            (P4SpecTec.Builtin.Sets.union_set as bs))) from by rfl)
    unfold Interp_al.Effects.builtinEval
    rw [dispatch, da, db]
    rfl
  · unfold P4SpecTec.Builtin.Sets.union_set
    rw [mapNormalize]
    apply resultRel
    simp only [canons_eq_map, List.map_append] at ca cb ⊢
    rw [ca, cb]

/-- info: 'P4SpecTec.Refine.Builtin.Set.unionRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unionRunOfRel
#audit_axioms unionRunOfRel

/-- Difference dispatch agrees on arbitrary represented elements, including extern payloads. -/
theorem diffRunOfRel {α : Type} [ToValue α] {a b : value} {xs ys : List α}
    (ha : Rel a (Collection.bracketed (xs.map toValue)))
    (hb : Rel b (Collection.bracketed (ys.map toValue)))
    (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "diff_set" [typ] [a, b]).run =
      some (.ok out) ∧
      Rel out (Collection.bracketed ((P4SpecTec.Builtin.Sets.diff_set xs ys).map toValue)) := by
  obtain ⟨raws, da, ca⟩ := Collection.bracketedDecodeOfRel ha
  obtain ⟨bs, db, cb⟩ := Collection.bracketedDecodeOfRel hb
  refine ⟨P4SpecTec.Builtin.Call.value_of_set typ
    (P4SpecTec.Builtin.Sets.diff_set raws bs), ?_, ?_⟩
  · have dispatch := (show P4SpecTec.Builtin.Call.invokeWithHints hints
        "diff_set" [typ] [a, b] =
        .ok (do
          let as ← P4SpecTec.Builtin.Call.set_of_value a
          let bs ← P4SpecTec.Builtin.Call.set_of_value b
          pure (P4SpecTec.Builtin.Call.value_of_set typ
            (P4SpecTec.Builtin.Sets.diff_set as bs))) from by rfl)
    unfold Interp_al.Effects.builtinEval
    rw [dispatch, da, db]
    rfl
  · unfold P4SpecTec.Builtin.Sets.diff_set
    rw [mapNormalize]
    apply resultRel
    exact filterRelated ca fun v x hx => congrArg Bool.not (memRelated hx cb)

/-- info: 'P4SpecTec.Refine.Builtin.Set.diffRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms diffRunOfRel
#audit_axioms diffRunOfRel

/-- Subset dispatch compares represented elements without requiring canonical input order. -/
theorem subRunOfRel {α : Type} [ToValue α] {a b : value} {xs ys : List α}
    (ha : Rel a (Collection.bracketed (xs.map toValue)))
    (hb : Rel b (Collection.bracketed (ys.map toValue)))
    (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ) :
    (Interp_al.Effects.builtinEval hints "sub_set" types [a, b]).run =
      some (.ok (toValue (P4SpecTec.Builtin.Sets.sub_set xs ys))) := by
  obtain ⟨raws, da, ca⟩ := Collection.bracketedDecodeOfRel ha
  obtain ⟨bs, db, cb⟩ := Collection.bracketedDecodeOfRel hb
  have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "sub_set" types [a, b] =
      .ok (do
        let as ← P4SpecTec.Builtin.Call.set_of_value a
        let bs ← P4SpecTec.Builtin.Call.set_of_value b
        pure (Runtime.Value.Make.bool (P4SpecTec.Builtin.Sets.sub_set as bs))) := by rfl
  unfold Interp_al.Effects.builtinEval
  rw [dispatch, da, db]
  change some (Except.ok (ε := Fail) (toValue (P4SpecTec.Builtin.Sets.sub_set raws bs))) = _
  rw [subRelated ca cb]

/-- info: 'P4SpecTec.Refine.Builtin.Set.subRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms subRunOfRel
#audit_axioms subRunOfRel

/-- Set equality dispatch compares represented elements without requiring canonical input order. -/
theorem eqRunOfRel {α : Type} [ToValue α] {a b : value} {xs ys : List α}
    (ha : Rel a (Collection.bracketed (xs.map toValue)))
    (hb : Rel b (Collection.bracketed (ys.map toValue)))
    (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ) :
    (Interp_al.Effects.builtinEval hints "eq_set" types [a, b]).run =
      some (.ok (toValue (P4SpecTec.Builtin.Sets.eq_set xs ys))) := by
  obtain ⟨raws, da, ca⟩ := Collection.bracketedDecodeOfRel ha
  obtain ⟨bs, db, cb⟩ := Collection.bracketedDecodeOfRel hb
  have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "eq_set" types [a, b] =
      .ok (do
        let as ← P4SpecTec.Builtin.Call.set_of_value a
        let bs ← P4SpecTec.Builtin.Call.set_of_value b
        pure (Runtime.Value.Make.bool (P4SpecTec.Builtin.Sets.eq_set as bs))) := by rfl
  unfold Interp_al.Effects.builtinEval
  rw [dispatch, da, db]
  change some (Except.ok (ε := Fail) (toValue (P4SpecTec.Builtin.Sets.eq_set raws bs))) = _
  unfold P4SpecTec.Builtin.Sets.eq_set
  rw [subRelated ca cb, subRelated cb ca]

/-- info: 'P4SpecTec.Refine.Builtin.Set.eqRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eqRunOfRel
#audit_axioms eqRunOfRel

private theorem decodeSets {α : Type} [ToValue α] {vs : List value} {sets : List (List α)}
    (h : canons vs = canons (sets.map fun xs => Collection.bracketed (xs.map toValue))) :
    ∃ rawss, vs.mapM P4SpecTec.Builtin.Call.set_of_value = some rawss ∧
      canons rawss.flatten = canons (sets.flatten.map toValue) := by
  match vs, sets with
  | [], [] => exact ⟨[], rfl, rfl⟩
  | v :: vs, xs :: sets =>
    obtain ⟨hx, ht⟩ := List.cons.inj h
    obtain ⟨raws, hd, hc⟩ := Collection.bracketedDecodeOfRel hx
    obtain ⟨rawss, hds, hcs⟩ := decodeSets ht
    refine ⟨raws :: rawss, ?_, ?_⟩
    · simp only [List.mapM_cons, hd, hds]
      rfl
    · simp only [List.flatten_cons, canons_eq_map, List.map_append] at hc hcs ⊢
      rw [hc, hcs]
  | [], _ :: _ | _ :: _, [] => simp [canons] at h

/-- Union of a represented list of sets agrees after both source normalization passes. -/
theorem unionsRunOfRel {α : Type} [ToValue α] {v : value} {sets : List (List α)}
    (h : Rel v (sets.map fun xs => Collection.bracketed (xs.map toValue)))
    (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "unions_set" [typ] [v]).run =
      some (.ok out) ∧
      Rel out (Collection.bracketed ((P4SpecTec.Builtin.Sets.unions_set sets).map toValue)) := by
  obtain ⟨vs, hv, hs⟩ := List.listPayloadOfRel h
  have hm : canons vs =
      canons (sets.map fun xs => Collection.bracketed (xs.map toValue)) := by
    change canons vs =
      canons ((sets.map fun xs => Collection.bracketed (xs.map toValue)).map id) at hs
    simpa only [List.map_id] using hs
  obtain ⟨rawss, hd, hc⟩ := decodeSets hm
  refine ⟨P4SpecTec.Builtin.Call.value_of_set typ
    (P4SpecTec.Builtin.Sets.unions_set rawss), ?_, ?_⟩
  · cases v with
    | mk payload note region =>
      change payload = .ListV vs at hv
      subst payload
      have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "unions_set" [typ]
          [⟨.ListV vs, note, region⟩] =
          .ok (do
            let sets ← vs.mapM P4SpecTec.Builtin.Call.set_of_value
            pure (P4SpecTec.Builtin.Call.value_of_set typ
              (P4SpecTec.Builtin.Sets.unions_set sets))) := by rfl
      unfold Interp_al.Effects.builtinEval
      rw [dispatch, hd]
      rfl
  · unfold P4SpecTec.Builtin.Sets.unions_set
    rw [mapNormalize]
    exact resultRel typ hc

/-- info: 'P4SpecTec.Refine.Builtin.Set.unionsRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unionsRunOfRel
#audit_axioms unionsRunOfRel

private theorem binaryDispatch (name : String)
    (h : name = "intersect_set" ∨ name = "union_set" ∨ name = "diff_set" ∨
      name = "sub_set" ∨ name = "eq_set")
    (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) (a b : value) :
    ∃ f : List value → List value → value,
      P4SpecTec.Builtin.Call.invokeWithHints hints name [typ] [a, b] =
        .ok (do
          let as ← P4SpecTec.Builtin.Call.set_of_value a
          let bs ← P4SpecTec.Builtin.Call.set_of_value b
          pure (f as bs)) := by
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact ⟨fun as bs => P4SpecTec.Builtin.Call.value_of_set typ
      (P4SpecTec.Builtin.Sets.intersect_set as bs), rfl⟩
  · exact ⟨fun as bs => P4SpecTec.Builtin.Call.value_of_set typ
      (P4SpecTec.Builtin.Sets.union_set as bs), rfl⟩
  · exact ⟨fun as bs => P4SpecTec.Builtin.Call.value_of_set typ
      (P4SpecTec.Builtin.Sets.diff_set as bs), rfl⟩
  · exact ⟨fun as bs => Runtime.Value.Make.bool
      (P4SpecTec.Builtin.Sets.sub_set as bs), rfl⟩
  · exact ⟨fun as bs => Runtime.Value.Make.bool
      (P4SpecTec.Builtin.Sets.eq_set as bs), rfl⟩

/-- Every binary set operation preserves the pinned malformed-set mismatch classification. -/
theorem binaryShapeMismatch (name : String)
    (hn : name = "intersect_set" ∨ name = "union_set" ∨ name = "diff_set" ∨
      name = "sub_set" ∨ name = "eq_set")
    (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) (a b : value)
    (bad : P4SpecTec.Builtin.Call.set_of_value a = none ∨
      P4SpecTec.Builtin.Call.set_of_value b = none) :
    (Interp_al.Effects.builtinEval hints name [typ] [a, b]).run = some (.error .unmatch) := by
  obtain ⟨f, dispatch⟩ := binaryDispatch name hn hints typ a b
  unfold Interp_al.Effects.builtinEval
  rw [dispatch]
  rcases bad with ha | hb
  · rw [ha]
    rfl
  · rw [hb]
    cases P4SpecTec.Builtin.Call.set_of_value a <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.Set.binaryShapeMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binaryShapeMismatch
#audit_axioms binaryShapeMismatch

/-- Binary set operations require exactly two values before collection decoding. -/
theorem binaryArity (name : String)
    (hn : name = "intersect_set" ∨ name = "union_set" ∨ name = "diff_set" ∨
      name = "sub_set" ∨ name = "eq_set")
    (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) (args : List value)
    (bad : args.length ≠ 2) :
    (Interp_al.Effects.builtinEval hints name [typ] args).run = some (.error .unmatch) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl <;>
    (cases args with
    | nil => rfl
    | cons a args =>
      cases args with
      | nil => rfl
      | cons b args =>
        cases args with
        | nil => exact False.elim (bad rfl)
        | cons c rest => rfl)

/-- info: 'P4SpecTec.Refine.Builtin.Set.binaryArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binaryArity
#audit_axioms binaryArity

/-- Set-producing operations require exactly one type argument in actual legacy dispatch. -/
theorem producerTypeArity (name : String)
    (hn : name = "intersect_set" ∨ name = "union_set" ∨ name = "diff_set" ∨
      name = "unions_set")
    (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ) (args : List value)
    (bad : types.length ≠ 1) :
    (Interp_al.Effects.builtinEval hints name types args).run = some (.error .unmatch) := by
  rcases hn with rfl | rfl | rfl | rfl <;>
    (cases types with
    | nil => rfl
    | cons typ types =>
      cases types with
      | nil => exact False.elim (bad rfl)
      | cons typ2 rest => rfl)

/-- info: 'P4SpecTec.Refine.Builtin.Set.producerTypeArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms producerTypeArity
#audit_axioms producerTypeArity

/-- Union over sets requires a single list argument. -/
theorem unionsArity (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) (args : List value)
    (bad : args.length ≠ 1) :
    (Interp_al.Effects.builtinEval hints "unions_set" [typ] args).run =
      some (.error .unmatch) := by
  cases args with
  | nil => rfl
  | cons a args =>
    cases args with
    | nil => exact False.elim (bad rfl)
    | cons b rest => rfl

/-- info: 'P4SpecTec.Refine.Builtin.Set.unionsArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unionsArity
#audit_axioms unionsArity

/-- A non-list outer argument to union over sets remains a mismatch. -/
theorem unionsOuterMismatch (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) (v : value)
    (bad : Runtime.Value.Get.list v = none) :
    (Interp_al.Effects.builtinEval hints "unions_set" [typ] [v]).run =
      some (.error .unmatch) := by
  cases v with
  | mk payload note region =>
    cases payload <;> simp_all [Runtime.Value.Get.list] <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.Set.unionsOuterMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unionsOuterMismatch
#audit_axioms unionsOuterMismatch

/-- Malformed set elements in union over sets retain the same mismatch outcome. -/
theorem unionsElementMismatch (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ)
    (vs : List value) (note : Lang.Il.vnote) (region : Util.Source.region)
    (bad : vs.mapM P4SpecTec.Builtin.Call.set_of_value = none) :
    (Interp_al.Effects.builtinEval hints "unions_set" [typ]
      [⟨.ListV vs, note, region⟩]).run = some (.error .unmatch) := by
  have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "unions_set" [typ]
      [⟨.ListV vs, note, region⟩] =
      .ok (do
        let sets ← vs.mapM P4SpecTec.Builtin.Call.set_of_value
        pure (P4SpecTec.Builtin.Call.value_of_set typ
          (P4SpecTec.Builtin.Sets.unions_set sets))) := by rfl
  unfold Interp_al.Effects.builtinEval
  rw [dispatch, bad]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.Set.unionsElementMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unionsElementMismatch
#audit_axioms unionsElementMismatch

end P4SpecTec.Refine.Builtin.Set
