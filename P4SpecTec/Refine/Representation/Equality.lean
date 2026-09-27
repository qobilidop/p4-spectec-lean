import P4SpecTec.Refine.Representation

/-!
The equality law required of legal polymorphic representations. Lean equality
and `LawfulBEq` alone say nothing about the observations retained by `ToValue`.
This interface does not establish source-domain membership or codec adequacy.
-/

namespace P4SpecTec.Refine.Representation

open P4SpecTec.Prelude P4SpecTec.Lang.Il

/-- Typed Boolean equality agrees with equality of its encoded source observations. -/
class ValueBEq (α : Type) [ToValue α] [BEq α] : Prop where
  /-- The actual `BEq` dictionary agrees with the shared runtime value equality. -/
  beqEq : ∀ x y : α, (x == y) = valueEq x y

/-- An explicitly value-based equality dictionary satisfies the law without injectivity. -/
theorem ValueBEq.ofValueEq {α : Type} [ToValue α] :
    @ValueBEq α _ ⟨valueEq⟩ := by
  letI : BEq α := ⟨valueEq⟩
  exact ⟨fun _ _ => rfl⟩

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.ofValueEq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.ofValueEq
#audit_axioms ValueBEq.ofValueEq

/-- Compatible typed equality is exactly equality of canonical encoded observations. -/
theorem ValueBEq.beqTrueIffCanon {α : Type} [ToValue α] [BEq α] [ValueBEq α]
    (x y : α) : (x == y) = true ↔ canon (toValue x) = canon (toValue y) := by
  rw [ValueBEq.beqEq]
  exact eq_iff_canon

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.beqTrueIffCanon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.beqTrueIffCanon
#audit_axioms ValueBEq.beqTrueIffCanon

/-- Related source operands agree with the actual typed equality dictionary. -/
theorem ValueBEq.eqOfRel {α : Type} [ToValue α] [BEq α] [ValueBEq α]
    {v w : value} {x y : α} (hx : Rel v x) (hy : Rel w y) :
    Runtime.Value.eq v w = (x == y) := by
  rw [ValueBEq.beqEq]
  exact eq_of_rel hx hy

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.eqOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.eqOfRel
#audit_axioms ValueBEq.eqOfRel

/-- Transport compatibility through a map that preserves both observations and equality. -/
theorem ValueBEq.ofMap {α β : Type} [ToValue α] [BEq α] [ToValue β] [BEq β]
    [ValueBEq β] (f : α → β)
    (equality : ∀ x y, (x == y) = (f x == f y))
    (encoding : ∀ x, Rel (toValue x) (f x)) : ValueBEq α := by
  constructor
  intro x y
  rw [equality, ValueBEq.beqEq]
  exact (eq_of_rel (encoding x) (encoding y)).symm

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.ofMap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.ofMap
#audit_axioms ValueBEq.ofMap

/-- Lawful Lean equality suffices only when canonical encoding is also faithful. -/
theorem ValueBEq.ofLawful {α : Type} [ToValue α] [BEq α] [LawfulBEq α]
    (faithful : Faithful (fun _ : α => True)) : ValueBEq α := by
  constructor
  intro x y
  rw [Bool.eq_iff_iff, beq_iff_eq]
  change x = y ↔ Runtime.Value.eq (toValue x) (toValue y) = true
  rw [eq_iff_canon]
  constructor
  · intro h
    subst y
    rfl
  · exact faithful x y trivial trivial

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.ofLawful' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.ofLawful
#audit_axioms ValueBEq.ofLawful

private theorem listEquality {α : Type} [ToValue α] [BEq α] [ValueBEq α]
    (xs ys : List α) :
    (xs == ys) = true ↔ canons (xs.map toValue) = canons (ys.map toValue) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [canons]
  | cons x xs ih =>
    cases ys with
    | nil => simp [canons]
    | cons y ys =>
      simp only [List.cons_beq_cons, Bool.and_eq_true, List.map_cons, canons,
        List.cons.injEq, ValueBEq.beqTrueIffCanon, ih]

/-- Standard list equality preserves the element dictionary's canonical compatibility. -/
instance ValueBEq.list {α : Type} [ToValue α] [BEq α] [ValueBEq α] :
    ValueBEq (List α) := by
  constructor
  intro xs ys
  rw [Bool.eq_iff_iff]
  change (xs == ys) = true ↔ Runtime.Value.eq (toValue xs) (toValue ys) = true
  rw [eq_iff_canon]
  change (xs == ys) = true ↔
    (⟨.ListV (canons (xs.map toValue)), dummy, Util.Source.no_region⟩ : value) =
      ⟨.ListV (canons (ys.map toValue)), dummy, Util.Source.no_region⟩
  simpa only [Util.Source.info.mk.injEq, value'.ListV.injEq, and_true]
    using listEquality xs ys

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.list' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.list
#audit_axioms ValueBEq.list

/-- Standard option equality preserves the element dictionary's canonical compatibility. -/
instance ValueBEq.option {α : Type} [ToValue α] [BEq α] [ValueBEq α] :
    ValueBEq (Option α) := by
  constructor
  intro xs ys
  rw [Bool.eq_iff_iff]
  change (xs == ys) = true ↔ Runtime.Value.eq (toValue xs) (toValue ys) = true
  rw [eq_iff_canon]
  change (xs == ys) = true ↔
    canon (Runtime.Value.Make.opt .TextT (xs.map toValue)) =
      canon (Runtime.Value.Make.opt .TextT (ys.map toValue))
  cases xs <;> cases ys <;>
    simp [canon, canon', Runtime.Value.Make.opt, Runtime.Value.Make.mk,
      ValueBEq.beqTrueIffCanon]

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.option' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.option
#audit_axioms ValueBEq.option

/-- Membership uses the compatible equality dictionary on every represented element. -/
theorem ValueBEq.elemOfRel {α : Type} [ToValue α] [BEq α] [ValueBEq α]
    {v : value} {x : α} {raws : List value} {xs : List α}
    (hx : Rel v x) (hs : canons raws = canons (xs.map toValue)) :
    raws.any (Runtime.Value.eq v) = xs.elem x := by
  match raws, xs with
  | [], [] => rfl
  | raw :: raws, y :: ys =>
    obtain ⟨hy, ht⟩ := List.cons.inj hs
    simp only [List.any_cons, List.elem_cons, ValueBEq.eqOfRel hx hy]
    rw [ValueBEq.elemOfRel hx ht]
    cases x == y <;> rfl
  | [], _ :: _ | _ :: _, [] => simp [canons] at hs

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.elemOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.elemOfRel
#audit_axioms ValueBEq.elemOfRel

/-- Boolean equality is compatible with the source Boolean representation. -/
instance ValueBEq.bool : ValueBEq Bool := by
  apply ValueBEq.ofLawful
  intro x y _ _ h
  change (⟨.BoolV x, dummy, Util.Source.no_region⟩ : value) =
    ⟨.BoolV y, dummy, Util.Source.no_region⟩ at h
  simpa only [Util.Source.info.mk.injEq, value'.BoolV.injEq, and_true] using h

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.bool' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.bool
#audit_axioms ValueBEq.bool

/-- Natural equality is compatible with the source natural-number tag. -/
instance ValueBEq.nat : ValueBEq Nat := by
  apply ValueBEq.ofLawful
  intro x y _ _ h
  change (⟨.NumV (.Nat x), dummy, Util.Source.no_region⟩ : value) =
    ⟨.NumV (.Nat y), dummy, Util.Source.no_region⟩ at h
  simpa only [Util.Source.info.mk.injEq, value'.NumV.injEq,
    Lang.Xl.Num.t.Nat.injEq, and_true] using h

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.nat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.nat
#audit_axioms ValueBEq.nat

/-- Integer equality is compatible with the source integer-number tag. -/
instance ValueBEq.int : ValueBEq Int := by
  apply ValueBEq.ofLawful
  intro x y _ _ h
  change (⟨.NumV (.Int x), dummy, Util.Source.no_region⟩ : value) =
    ⟨.NumV (.Int y), dummy, Util.Source.no_region⟩ at h
  simpa only [Util.Source.info.mk.injEq, value'.NumV.injEq,
    Lang.Xl.Num.t.Int.injEq, and_true] using h

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.int' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.int
#audit_axioms ValueBEq.int

/-- Byte-text equality compares exactly the bytes retained by the source representation. -/
instance ValueBEq.byteText : ValueBEq ByteText := by
  apply ValueBEq.ofLawful
  intro x y _ _ h
  change (⟨.TextV x, dummy, Util.Source.no_region⟩ : value) =
    ⟨.TextV y, dummy, Util.Source.no_region⟩ at h
  simpa only [Util.Source.info.mk.injEq, value'.TextV.injEq, and_true] using h

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.byteText' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.byteText
#audit_axioms ValueBEq.byteText

/-- Extern equality observes the same original compressed JSON as runtime value equality. -/
instance ValueBEq.extern : ValueBEq ExternValue := by
  constructor
  intro x y
  change (x.json.compress == y.json.compress) = Runtime.Value.eq
    (Runtime.Value.Make.mk _ (.ExternV x.json)) (Runtime.Value.Make.mk _ (.ExternV y.json))
  rw [Bool.eq_iff_iff, beq_iff_eq, eq_iff_canon]
  simp [canon, canon', Runtime.Value.Make.mk]

/-- info: 'P4SpecTec.Refine.Representation.ValueBEq.extern' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ValueBEq.extern
#audit_axioms ValueBEq.extern

end P4SpecTec.Refine.Representation
