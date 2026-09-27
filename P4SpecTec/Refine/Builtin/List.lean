import Batteries.Data.List.Basic
import P4SpecTec.Refine.ValueShape
import P4SpecTec.Interp.Effects

/-! List-operation contracts preserve the canonical representation of elements. -/

namespace P4SpecTec.Refine.Builtin.List

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- Reversal preserves canonical equality between element lists. -/
theorem canonsReverse (vs : List Lang.Il.value) :
    canons vs.reverse = (canons vs).reverse := by
  simp only [canons_eq_map, List.map_reverse]

/-- info: 'P4SpecTec.Refine.Builtin.List.canonsReverse' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canonsReverse

/-- A represented list exposes raw elements with their canonical correspondence. -/
theorem listPayloadOfRel {α : Type} [ToValue α] {v : Lang.Il.value} {xs : List α}
    (h : Rel v xs) :
    ∃ vs, v.it = .ListV vs ∧ canons vs = canons (xs.map toValue) := by
  apply canon'_eq_list
  apply canon_eq_it
  exact h

/-- info: 'P4SpecTec.Refine.Builtin.List.listPayloadOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms listPayloadOfRel

/-- Actual reversal dispatch preserves every represented element and succeeds for one type.
The type argument controls only source result notes; no element shape is silently repaired. -/
theorem reverseRunOfRel {α : Type} [ToValue α] {v : Lang.Il.value} {xs : List α}
    (h : Rel v xs) (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "rev_" [typ] [v]).run = some (.ok out) ∧
      Rel out (P4SpecTec.Builtin.Lists.rev_ xs) := by
  obtain ⟨vs, hv, hs⟩ := listPayloadOfRel h
  refine ⟨Runtime.Value.Make.list (.IterT typ .List) vs.reverse, ?_, ?_⟩
  · cases v with
    | mk payload note region =>
      change payload = .ListV vs at hv
      subst payload
      rfl
  · apply congrArg (fun ws => (⟨.ListV ws, dummy, Util.Source.no_region⟩ : Lang.Il.value))
    rw [canonsReverse, hs, P4SpecTec.Builtin.Lists.rev_, List.map_reverse, canonsReverse]

/-- info: 'P4SpecTec.Refine.Builtin.List.reverseRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverseRunOfRel

/-- Membership equality tests agree on canonically related raw lists. -/
theorem anyEqOfCanons {v w : Lang.Il.value} {vs ws : List Lang.Il.value}
    (hv : canon v = canon w) (hs : canons vs = canons ws) :
    vs.any (Runtime.Value.eq v) = ws.any (Runtime.Value.eq w) := by
  induction vs generalizing ws with
  | nil =>
    have hw : ws = [] := canons_eq_nil hs.symm
    subst ws
    rfl
  | cons x xs ih =>
    cases ws with
    | nil => simp [canons] at hs
    | cons y ys =>
      have hh := List.cons.inj hs
      simp only [List.any_cons, eq_of_canon hv hh.1, ih hh.2]

/-- info: 'P4SpecTec.Refine.Builtin.List.anyEqOfCanons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms anyEqOfCanons

/-- Distinctness observes canonical value equality, including nested raw values. -/
theorem distinctOfCanons {vs ws : List Lang.Il.value} (h : canons vs = canons ws) :
    P4SpecTec.Builtin.Lists.distinct_.go vs = P4SpecTec.Builtin.Lists.distinct_.go ws := by
  induction vs generalizing ws with
  | nil =>
    have hw : ws = [] := canons_eq_nil h.symm
    subst ws
    rfl
  | cons x xs ih =>
    cases ws with
    | nil => simp [canons] at h
    | cons y ys =>
      have hh := List.cons.inj h
      simp only [P4SpecTec.Builtin.Lists.distinct_.go, anyEqOfCanons hh.1 hh.2, ih hh.2]

/-- info: 'P4SpecTec.Refine.Builtin.List.distinctOfCanons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms distinctOfCanons

/-- Actual distinctness dispatch returns the generated Boolean for every related list. -/
theorem distinctRunOfRel {α : Type} [ToValue α] {v : Lang.Il.value} {xs : List α}
    (h : Rel v xs) (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ) :
    (Interp_al.Effects.builtinEval hints "distinct_" types [v]).run =
      some (.ok (toValue (P4SpecTec.Builtin.Lists.distinct_ xs))) := by
  obtain ⟨vs, hv, hs⟩ := listPayloadOfRel h
  have he := distinctOfCanons hs
  cases v with
  | mk payload note region =>
    change payload = .ListV vs at hv
    subst payload
    change some (Except.ok (Runtime.Value.Make.bool
      (P4SpecTec.Builtin.Lists.distinct_ vs)) : Except Fail Lang.Il.value) = _
    change some (Except.ok (Runtime.Value.Make.bool
      (P4SpecTec.Builtin.Lists.distinct_.go (vs.map id))) : Except Fail Lang.Il.value) = _
    rw [List.map_id, he]
    rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.distinctRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms distinctRunOfRel

/-- Reversal requires exactly one type argument even in the guard-free profile. -/
theorem reverseTypeArity (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ)
    (v : Lang.Il.value) (h : types.length ≠ 1) :
    (Interp_al.Effects.builtinEval hints "rev_" types [v]).run = some (.error .unmatch) := by
  cases types with
  | nil => rfl
  | cons typ types =>
    cases types with
    | nil => exact False.elim (h rfl)
    | cons typ2 rest => rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.reverseTypeArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverseTypeArity

/-- The pinned legacy list dispatcher classifies non-list inputs as mismatches. -/
theorem reverseShapeMismatch (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ)
    (v : Lang.Il.value) (h : Runtime.Value.Get.list v = none) :
    (Interp_al.Effects.builtinEval hints "rev_" [typ] [v]).run = some (.error .unmatch) := by
  cases v with
  | mk payload note region =>
    cases payload <;> simp_all [Runtime.Value.Get.list] <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.reverseShapeMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverseShapeMismatch

/-- Distinctness uses the same pinned legacy non-list failure classification. -/
theorem distinctShapeMismatch (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ)
    (v : Lang.Il.value) (h : Runtime.Value.Get.list v = none) :
    (Interp_al.Effects.builtinEval hints "distinct_" types [v]).run =
      some (.error .unmatch) := by
  cases v with
  | mk payload note region =>
    cases payload <;> simp_all [Runtime.Value.Get.list] <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.distinctShapeMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms distinctShapeMismatch

/-- Incorrect value arity is rejected before operation decoding. -/
theorem reverseArity (hints : P4.Unparse.HEnv) (typ : Lang.Il.typ)
    (args : List Lang.Il.value) (h : args.length ≠ 1) :
    (Interp_al.Effects.builtinEval hints "rev_" [typ] args).run =
      some (.error .unmatch) := by
  cases args with
  | nil => rfl
  | cons arg args =>
    cases args with
    | nil => exact False.elim (h rfl)
    | cons arg2 rest => rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.reverseArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverseArity

/-- Incorrect value arity is rejected before operation decoding. -/
theorem distinctArity (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ)
    (args : List Lang.Il.value) (h : args.length ≠ 1) :
    (Interp_al.Effects.builtinEval hints "distinct_" types args).run =
      some (.error .unmatch) := by
  cases args with
  | nil => rfl
  | cons arg args =>
    cases args with
    | nil => exact False.elim (h rfl)
    | cons arg2 rest => rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.distinctArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms distinctArity

/-- A related polymorphic pair decodes into separately related key and result values. -/
theorem pairDecodeOfRel {α β : Type} [ToValue α] [ToValue β]
    {v : Lang.Il.value} {x : α} {y : β} (h : Rel v (x, y)) :
    ∃ rx ry, P4SpecTec.Builtin.Call.pair2 v = some (rx, ry) ∧ Rel rx x ∧ Rel ry y := by
  have hc : canon' v.it = .TupleV [canon (toValue x), canon (toValue y)] := canon_eq_it h
  obtain ⟨raws, hv, hs⟩ := canon'_eq_tuple hc
  obtain ⟨rx, rest, rfl, hx, ht⟩ := canons_eq_cons hs
  obtain ⟨ry, rest, rfl, hy, ht⟩ := canons_eq_cons ht
  have hn := canons_eq_nil ht
  subst rest
  refine ⟨rx, ry, ?_, hx, hy⟩
  cases v with
  | mk payload note region =>
    change payload = .TupleV [rx, ry] at hv
    subst payload
    rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.pairDecodeOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairDecodeOfRel

/-- Related raw pair lists decode without weakening key or value correspondence. -/
theorem pairListDecodeOfCanons {α β : Type} [ToValue α] [ToValue β]
    (raws : List Lang.Il.value) (xs : List (α × β))
    (h : canons raws = canons (xs.map toValue)) :
    ∃ pairs, raws.mapM P4SpecTec.Builtin.Call.pair2 = some pairs ∧
      List.Forall₂ (fun p q => Rel p.1 q.1 ∧ Rel p.2 q.2) pairs xs := by
  induction xs generalizing raws with
  | nil =>
    have hn := canons_eq_nil h
    subst raws
    exact ⟨[], rfl, .nil⟩
  | cons xy xs ih =>
    obtain ⟨raw, rest, rfl, hr, ht⟩ := canons_eq_cons h
    obtain ⟨rx, ry, hd, hx, hy⟩ := pairDecodeOfRel hr
    obtain ⟨pairs, hp, hs⟩ := ih rest ht
    refine ⟨(rx, ry) :: pairs, ?_, .cons ⟨hx, hy⟩ hs⟩
    simp only [List.mapM_cons, hd, hp]
    rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.pairListDecodeOfCanons' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairListDecodeOfCanons

/-- First-match association preserves related optional results, including absence. -/
theorem assocPairsRel {α β : Type} [ToValue α] [ToValue β]
    {raw : Lang.Il.value} {key : α} (hk : Rel raw key)
    {raws : List (Lang.Il.value × Lang.Il.value)} {xs : List (α × β)}
    (h : List.Forall₂ (fun p q => Rel p.1 q.1 ∧ Rel p.2 q.2) raws xs) :
    Rel (toValue (P4SpecTec.Builtin.Lists.assoc_ raw raws))
      (P4SpecTec.Builtin.Lists.assoc_ key xs) := by
  induction h with
  | nil => rfl
  | @cons p q ps qs hp hs ih =>
    have he : Runtime.Value.eq (toValue raw) (toValue p.1) =
        Runtime.Value.eq (toValue key) (toValue q.1) := eq_of_rel hk hp.1
    simp only [P4SpecTec.Builtin.Lists.assoc_, List.find?_cons]
    rw [he]
    cases ht : Runtime.Value.eq (toValue key) (toValue q.1)
    · simpa only [P4SpecTec.Builtin.Lists.assoc_] using ih
    · exact congrArg
        (fun v => (⟨.OptV (some v), dummy, Util.Source.no_region⟩ : Lang.Il.value)) hp.2

/-- info: 'P4SpecTec.Refine.Builtin.List.assocPairsRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assocPairsRel

/-- Actual first-match association preserves presence and absence on all related pair lists. -/
theorem assocRunOfRel {α β : Type} [ToValue α] [ToValue β]
    {key pairs : Lang.Il.value} {x : α} {xs : List (α × β)}
    (hk : Rel key x) (hp : Rel pairs xs) (hints : P4.Unparse.HEnv)
    (keyType valueType : Lang.Il.typ) :
    ∃ out, (Interp_al.Effects.builtinEval hints "assoc_" [keyType, valueType]
      [key, pairs]).run = some (.ok out) ∧ Rel out (P4SpecTec.Builtin.Lists.assoc_ x xs) := by
  obtain ⟨raws, hv, hs⟩ := listPayloadOfRel hp
  obtain ⟨decoded, hd, hr⟩ := pairListDecodeOfCanons raws xs hs
  let answer := P4SpecTec.Builtin.Lists.assoc_ key decoded
  refine ⟨Runtime.Value.Make.opt (.IterT valueType .Opt) answer, ?_, ?_⟩
  · cases pairs with
    | mk payload note region =>
      change payload = .ListV raws at hv
      subst payload
      have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "assoc_"
          [keyType, valueType] [key, ⟨.ListV raws, note, region⟩] =
          .ok (do
            let ps ← raws.mapM P4SpecTec.Builtin.Call.pair2
            pure (Runtime.Value.Make.opt (.IterT valueType .Opt)
              (P4SpecTec.Builtin.Lists.assoc_ key ps))) := by rfl
      unfold Interp_al.Effects.builtinEval
      rw [dispatch, hd]
      rfl
  · have ho := assocPairsRel hk hr
    change Rel (toValue answer) (P4SpecTec.Builtin.Lists.assoc_ x xs) at ho
    cases he : answer with
    | none => rw [he] at ho; exact ho
    | some raw => rw [he] at ho; exact ho

/-- info: 'P4SpecTec.Refine.Builtin.List.assocRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assocRunOfRel

/-- Malformed entries in a correctly applied association remain legacy mismatches. -/
theorem assocPairMismatch (hints : P4.Unparse.HEnv) (keyType valueType : Lang.Il.typ)
    (key : Lang.Il.value) (raws : List Lang.Il.value) (note : Lang.Il.vnote)
    (region : Util.Source.region) (h : raws.mapM P4SpecTec.Builtin.Call.pair2 = none) :
    (Interp_al.Effects.builtinEval hints "assoc_" [keyType, valueType]
      [key, ⟨.ListV raws, note, region⟩]).run = some (.error .unmatch) := by
  have dispatch : P4SpecTec.Builtin.Call.invokeWithHints hints "assoc_"
      [keyType, valueType] [key, ⟨.ListV raws, note, region⟩] =
      .ok (do
        let ps ← raws.mapM P4SpecTec.Builtin.Call.pair2
        pure (Runtime.Value.Make.opt (.IterT valueType .Opt)
          (P4SpecTec.Builtin.Lists.assoc_ key ps))) := by rfl
  unfold Interp_al.Effects.builtinEval
  rw [dispatch, h]
  rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.assocPairMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assocPairMismatch

/-- Association requires exactly two input values before pair decoding. -/
theorem assocArity (hints : P4.Unparse.HEnv) (keyType valueType : Lang.Il.typ)
    (args : List Lang.Il.value) (wrong : args.length ≠ 2) :
    (Interp_al.Effects.builtinEval hints "assoc_" [keyType, valueType] args).run =
      some (.error .unmatch) := by
  cases args with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      cases rest with
      | nil => exact False.elim (wrong rfl)
      | cons c rest => rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.assocArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assocArity

/-- Association rejects type arities other than the declared key and value types. -/
theorem assocTypeArity (hints : P4.Unparse.HEnv) (types : List Lang.Il.typ)
    (args : List Lang.Il.value) (wrong : types.length ≠ 2) :
    (Interp_al.Effects.builtinEval hints "assoc_" types args).run =
      some (.error .unmatch) := by
  cases types with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => rfl
    | cons b rest =>
      cases rest with
      | nil => exact False.elim (wrong rfl)
      | cons c rest => rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.assocTypeArity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assocTypeArity

/-- A non-list association input retains the pinned retryable mismatch. -/
theorem assocShapeMismatch (hints : P4.Unparse.HEnv) (keyType valueType : Lang.Il.typ)
    (key pairs : Lang.Il.value) (failed : Runtime.Value.Get.list pairs = none) :
    (Interp_al.Effects.builtinEval hints "assoc_" [keyType, valueType]
      [key, pairs]).run = some (.error .unmatch) := by
  cases pairs with
  | mk payload note region =>
    cases payload <;> simp_all [Runtime.Value.Get.list] <;> rfl

/-- info: 'P4SpecTec.Refine.Builtin.List.assocShapeMismatch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assocShapeMismatch

end P4SpecTec.Refine.Builtin.List
