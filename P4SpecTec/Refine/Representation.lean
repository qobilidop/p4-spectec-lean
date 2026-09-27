import Batteries.Data.List.Basic
import P4SpecTec.Prelude.Extern
import P4SpecTec.Refine.Value
import P4SpecTec.Tactic.Audit

/-!
Representation obligations on an independently stated source domain. Neither the
source predicate nor admitted generated inputs are defined by decoder success or
by the generated encoder's range. Clients must connect their predicates to the
source specification and establish them at initialization and calls.

Strict shape predicates below are building blocks, not a claim that the runtime
membership checker characterizes representability. In particular its numeric
membership admits both numeric tags, while canonical equality distinguishes them.
A runtime extension can have a separate contract without enlarging a source domain.

Decoder sufficiency means one result at every sufficiently large fuel. Finite
container and well-founded recursive composition require no uniform depth bound
on all inputs, and polymorphic containers require a contract for each actual
parameter instance. This is proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.Representation

open P4SpecTec.Lang.Il P4SpecTec.Prelude P4SpecTec.Runtime.Value

/-- An independently specified set of source values. -/
abbrev SourceDomain := value → Prop

/-- Every admitted source value is represented and every admitted image is valid. -/
structure Adequate {α : Type} [ToValue α] (source : SourceDomain)
    (admitted : α → Prop) : Prop where
  /-- Coverage starts from the source predicate, not from a generated witness. -/
  coverage : ∀ v, source v → ∃ x, admitted x ∧ Rel v x
  /-- Only the explicitly admitted part of a runtime carrier is source-valid. -/
  encodingValid : ∀ x, admitted x → source (toValue x)

/-- This decoder returns the same witness at every sufficiently large fuel. -/
def Decodes {α : Type} (decode : Nat → value → Option α) (v : value) (x : α) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel → decode fuel v = some x

/-- Decoder success is faithful on the independent domain, which is fully covered. -/
structure DecoderCorrect {α : Type} [ToValue α] (source : SourceDomain)
    (admitted : α → Prop) (decode : Nat → value → Option α) : Prop where
  /-- A successful decode on the domain preserves observations and admission. -/
  sound : ∀ fuel v x, source v → decode fuel v = some x → admitted x ∧ Rel v x
  /-- Every source value has a stable sufficient bound, possibly depending on the value. -/
  sufficient : ∀ v, source v → ∃ x, Decodes decode v x

/-- A legal parameter instance supplies source validity and both decoder obligations. -/
structure Codec {α : Type} [ToValue α] [OfValue α] (source : SourceDomain)
    (admitted : α → Prop) : Prop where
  /-- Admitted generated images belong to the independent source domain. -/
  encodingValid : ∀ x, admitted x → source (toValue x)
  /-- The actual `OfValue` instance is sound and sufficient on that domain. -/
  decoder : DecoderCorrect source admitted (OfValue.ofValue (α := α))

/-- Decoder sufficiency and soundness imply source coverage. -/
theorem DecoderCorrect.coverage {α : Type} [ToValue α] {source : SourceDomain}
    {admitted : α → Prop} {decode : Nat → value → Option α}
    (contract : DecoderCorrect source admitted decode) (v : value) (hv : source v) :
    ∃ x, admitted x ∧ Rel v x := by
  obtain ⟨x, bound, h⟩ := contract.sufficient v hv
  exact ⟨x, contract.sound bound v x hv (h bound (Nat.le_refl _))⟩

/-- info: 'P4SpecTec.Refine.Representation.DecoderCorrect.coverage' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DecoderCorrect.coverage
#audit_axioms DecoderCorrect.coverage

/-- A codec discharges representation adequacy without defining its domain by decoding. -/
theorem Codec.adequate {α : Type} [ToValue α] [OfValue α] {source : SourceDomain}
    {admitted : α → Prop} (contract : Codec source admitted) : Adequate source admitted :=
  ⟨contract.decoder.coverage, contract.encodingValid⟩

/-- info: 'P4SpecTec.Refine.Representation.Codec.adequate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Codec.adequate
#audit_axioms Codec.adequate

/-- Finitely many stable obligations have a common finite bound. -/
theorem commonBound {ι : Type} (items : List ι) (holds : ι → Nat → Prop)
    (eventually : ∀ i ∈ items, ∃ bound, ∀ fuel, bound ≤ fuel → holds i fuel) :
    ∃ bound, ∀ fuel, bound ≤ fuel → ∀ i ∈ items, holds i fuel := by
  induction items with
  | nil => exact ⟨0, by simp⟩
  | cons i items ih =>
    obtain ⟨head, hh⟩ := eventually i (by simp)
    obtain ⟨tail, ht⟩ := ih (by
      intro j hj
      exact eventually j (by simp [hj]))
    refine ⟨max head tail, ?_⟩
    intro fuel hf j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hh fuel (Nat.le_trans (Nat.le_max_left _ _) hf)
    · exact ht fuel (Nat.le_trans (Nat.le_max_right _ _) hf) j hj

/-- info: 'P4SpecTec.Refine.Representation.commonBound' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms commonBound
#audit_axioms commonBound

/-- Recursive decoder calls with finitely many well-founded children admit enough fuel.
The index may include a family tag, type parameters and a source derivation, so this
also supports mutual recursion and nested or legally instantiated polymorphic fields. -/
theorem decodesWellFounded {ι : Type} {α : ι → Type} {r : ι → ι → Prop}
    (wellFounded : WellFounded r) (children : ι → List ι)
    (decreases : ∀ i j, j ∈ children i → r j i)
    (decode : (i : ι) → Nat → value → Option (α i))
    (source : ι → value) (represented : (i : ι) → α i)
    (step : ∀ i fuel,
      (∀ j ∈ children i, decode j fuel (source j) = some (represented j)) →
      decode i (fuel + 1) (source i) = some (represented i)) :
    ∀ i, Decodes (decode i) (source i) (represented i) := by
  intro i
  induction i using wellFounded.induction with
  | h i ih =>
    obtain ⟨bound, hb⟩ := commonBound (children i)
      (fun j fuel => decode j fuel (source j) = some (represented j))
      (fun j hj => ih j (decreases i j hj))
    refine ⟨bound + 1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel => exact step i fuel (hb fuel (by omega))

/-- info: 'P4SpecTec.Refine.Representation.decodesWellFounded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodesWellFounded
#audit_axioms decodesWellFounded

namespace Shape

/-- The Boolean constructor shape, allowing arbitrary notes and regions. -/
def bool (v : value) : Prop := ∃ b, v.it = .BoolV b

/-- The natural-tag shape; membership in source `nat` is a separate obligation. -/
def nat (v : value) : Prop := ∃ n, v.it = .NumV (.Nat n)

/-- The integer-tag shape; source casts explicitly normalize naturals to this tag. -/
def int (v : value) : Prop := ∃ i, v.it = .NumV (.Int i)

/-- Exact byte-text constructor shape. -/
def text (v : value) : Prop := ∃ s, v.it = .TextV s

/-- Raw extern shape, to use only for a separately justified source/runtime domain. -/
def extern (v : value) : Prop := ∃ j, v.it = .ExternV j

/-- A list has the source list constructor and independently valid elements. -/
def list (element : SourceDomain) (v : value) : Prop :=
  ∃ vs, v.it = .ListV vs ∧ ∀ x ∈ vs, element x

/-- An option has the source option constructor and an independently valid payload. -/
def option (element : SourceDomain) (v : value) : Prop :=
  v.it = .OptV none ∨ ∃ x, v.it = .OptV (some x) ∧ element x

end Shape

/-- Pointwise related elements give related lists, retaining order and multiplicity. -/
theorem relList {α : Type} [ToValue α] {vs : List value} {xs : List α}
    (h : List.Forall₂ Rel vs xs) (note : vnote) (location : Util.Source.region) :
    Rel ⟨.ListV vs, note, location⟩ xs := by
  suffices hc : canons vs = canons (xs.map toValue) by
    exact congrArg (fun ys => (⟨.ListV ys, dummy, Util.Source.no_region⟩ : value)) hc
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [canons, List.map_cons]
    rw [show canon _ = canon _ from h, ih]

/-- info: 'P4SpecTec.Refine.Representation.relList' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relList
#audit_axioms relList

/-- A related optional payload gives a related present option. -/
theorem relSome {α : Type} [ToValue α] {v : value} {x : α} (h : Rel v x)
    (note : vnote) (location : Util.Source.region) :
    Rel ⟨.OptV (some v), note, location⟩ (some x) := by
  exact congrArg (fun y => (⟨.OptV (some y), dummy, Util.Source.no_region⟩ : value)) h

/-- info: 'P4SpecTec.Refine.Representation.relSome' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms relSome
#audit_axioms relSome

/-- Stable element decodes compose through actual list decoding with a common bound. -/
theorem decodesList {α : Type} [OfValue α] {vs : List value} {xs : List α}
    (h : List.Forall₂ (Decodes (OfValue.ofValue (α := α))) vs xs)
    (note : vnote) (location : Util.Source.region) :
    Decodes (OfValue.ofValue (α := List α)) ⟨.ListV vs, note, location⟩ xs := by
  induction h with
  | nil => exact ⟨0, fun _ _ => rfl⟩
  | @cons v x vs xs hx h ih =>
    obtain ⟨head, hh⟩ := hx
    obtain ⟨tail, ht⟩ := ih
    refine ⟨max head tail, ?_⟩
    intro fuel hf
    have hd := hh fuel (Nat.le_trans (Nat.le_max_left _ _) hf)
    have tl := ht fuel (Nat.le_trans (Nat.le_max_right _ _) hf)
    change (v :: vs).mapM (OfValue.ofValue fuel) = some (x :: xs)
    change vs.mapM (OfValue.ofValue fuel) = some xs at tl
    simp only [List.mapM_cons, hd, tl]
    rfl

/-- info: 'P4SpecTec.Refine.Representation.decodesList' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodesList
#audit_axioms decodesList

/-- Stable element decoding composes through the actual present-option decoder. -/
theorem decodesSome {α : Type} [OfValue α] {v : value} {x : α}
    (h : Decodes (OfValue.ofValue (α := α)) v x)
    (note : vnote) (location : Util.Source.region) :
    Decodes (OfValue.ofValue (α := Option α)) ⟨.OptV (some v), note, location⟩ (some x) := by
  obtain ⟨bound, hb⟩ := h
  exact ⟨bound, fun fuel hf => by
    change (OfValue.ofValue fuel v).map some = some (some x)
    rw [hb fuel hf]
    rfl⟩

/-- info: 'P4SpecTec.Refine.Representation.decodesSome' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodesSome
#audit_axioms decodesSome

/-- An absent option needs no assumptions or fuel for its parameter decoder. -/
theorem decodesNone {α : Type} [OfValue α] (note : vnote) (location : Util.Source.region) :
    Decodes (OfValue.ofValue (α := Option α)) ⟨.OptV none, note, location⟩ none :=
  ⟨0, fun _ _ => rfl⟩

/-- info: 'P4SpecTec.Refine.Representation.decodesNone' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms decodesNone
#audit_axioms decodesNone

/-- Pointwise witnesses for a finite source list assemble without a length cutoff. -/
theorem listWitnesses {α β : Type} (related : α → β → Prop) (xs : List α)
    (witness : ∀ x ∈ xs, ∃ y, related x y) : ∃ ys, List.Forall₂ related xs ys := by
  induction xs with
  | nil => exact ⟨[], .nil⟩
  | cons x xs ih =>
    obtain ⟨y, hy⟩ := witness x (by simp)
    obtain ⟨ys, hys⟩ := ih (by intro x hx; exact witness x (by simp [hx]))
    exact ⟨y :: ys, .cons hy hys⟩

/-- info: 'P4SpecTec.Refine.Representation.listWitnesses' depends on axioms:
[propext] -/
#guard_msgs (whitespace := lax) in #print axioms listWitnesses
#audit_axioms listWitnesses

/-- Successful option-valued traversal supplies a decoding equality for every element. -/
theorem mapMForall₂ {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => cases h; exact .nil
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons, hx] at h
    | some y =>
      cases hxs : xs.mapM f with
      | none => simp [List.mapM_cons, hx, hxs] at h
      | some zs =>
        have heq : y :: zs = ys := by simpa [List.mapM_cons, hx, hxs] using h
        subst ys
        exact .cons hx (ih hxs)

/-- info: 'P4SpecTec.Refine.Representation.mapMForall₂' depends on axioms:
[propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms mapMForall₂
#audit_axioms mapMForall₂

/-- Legal element instances induce a source-list codec preserving order and duplicates. -/
theorem Codec.list {α : Type} [ToValue α] [OfValue α] {source : SourceDomain}
    {admitted : α → Prop} (contract : Codec source admitted) :
    Codec (Shape.list source) (fun xs : List α => ∀ x ∈ xs, admitted x) where
  encodingValid xs hx := by
    refine ⟨xs.map toValue, rfl, ?_⟩
    intro v hv
    obtain ⟨x, hmem, rfl⟩ := List.mem_map.mp hv
    exact contract.encodingValid x (hx x hmem)
  decoder.sound fuel v xs hv hd := by
    obtain ⟨vs, hs, hall⟩ := hv
    obtain ⟨payload, note, location⟩ := v
    cases hs
    change vs.mapM (OfValue.ofValue fuel) = some xs at hd
    have hpair := mapMForall₂ (OfValue.ofValue (α := α) fuel) hd
    have checked : (∀ x ∈ xs, admitted x) ∧ List.Forall₂ Rel vs xs := by
      clear hd
      induction hpair with
      | nil => exact ⟨by simp, .nil⟩
      | @cons v x vs xs h _ ih =>
        obtain ⟨ha, hr⟩ := contract.decoder.sound fuel v x (hall v (by simp)) h
        obtain ⟨has, hrs⟩ := ih (by intro v hv; exact hall v (by simp [hv]))
        exact ⟨by intro y hy; rcases List.mem_cons.mp hy with rfl | hy
                  · exact ha
                  · exact has y hy, .cons hr hrs⟩
    exact ⟨checked.1, relList checked.2 note location⟩
  decoder.sufficient v hv := by
    obtain ⟨vs, hs, hall⟩ := hv
    obtain ⟨payload, note, location⟩ := v
    cases hs
    obtain ⟨xs, hxs⟩ := listWitnesses (Decodes (OfValue.ofValue (α := α))) vs
      (fun v hv => contract.decoder.sufficient v (hall v hv))
    exact ⟨xs, decodesList hxs note location⟩

/-- info: 'P4SpecTec.Refine.Representation.Codec.list' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Codec.list
#audit_axioms Codec.list

/-- Legal element instances induce an option codec with exact constructor checks. -/
theorem Codec.option {α : Type} [ToValue α] [OfValue α] {source : SourceDomain}
    {admitted : α → Prop} (contract : Codec source admitted) :
    Codec (Shape.option source) (fun x : Option α => ∀ y ∈ x, admitted y) where
  encodingValid x hx := by
    cases x with
    | none => exact .inl rfl
    | some x => exact .inr ⟨toValue x, rfl, contract.encodingValid x (hx x rfl)⟩
  decoder.sound fuel v x hv hd := by
    obtain ⟨payload, note, location⟩ := v
    rcases hv with hnone | ⟨w, hw, hs⟩
    · cases hnone
      change some none = some x at hd
      cases hd
      exact ⟨by simp, rfl⟩
    · cases hw
      change (OfValue.ofValue (α := α) fuel w).map some = some x at hd
      cases he : OfValue.ofValue (α := α) fuel w with
      | none => simp [he] at hd
      | some y =>
        have hx : some y = x := by simpa [he] using hd
        subst x
        obtain ⟨ha, hr⟩ := contract.decoder.sound fuel w y hs he
        exact ⟨by intro z hz; cases hz; exact ha, relSome hr note location⟩
  decoder.sufficient v hv := by
    obtain ⟨payload, note, location⟩ := v
    rcases hv with hnone | ⟨w, hw, hs⟩
    · cases hnone
      exact ⟨none, decodesNone note location⟩
    · cases hw
      obtain ⟨x, hx⟩ := contract.decoder.sufficient w hs
      exact ⟨some x, decodesSome hx note location⟩

/-- info: 'P4SpecTec.Refine.Representation.Codec.option' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Codec.option
#audit_axioms Codec.option

/-- The actual `Bool` codec is adequate on its independently named constructor shape. -/
theorem boolCodec : Codec Shape.bool (fun _ : Bool => True) where
  encodingValid b _ := ⟨b, rfl⟩
  decoder.sound fuel v x hv hd := by
    obtain ⟨payload, note, location⟩ := v
    obtain ⟨b, hb⟩ := hv
    cases hb
    change some b = some x at hd
    cases hd
    exact ⟨True.intro, rfl⟩
  decoder.sufficient v hv := by
    obtain ⟨payload, note, location⟩ := v
    obtain ⟨b, hb⟩ := hv
    cases hb
    exact ⟨b, 0, fun _ _ => rfl⟩

/-- info: 'P4SpecTec.Refine.Representation.boolCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms boolCodec
#audit_axioms boolCodec

/-- The actual `Nat` codec is adequate on its independently named constructor shape. -/
theorem natCodec : Codec Shape.nat (fun _ : Nat => True) where
  encodingValid b _ := ⟨b, rfl⟩
  decoder.sound fuel v x hv hd := by
    obtain ⟨payload, note, location⟩ := v
    obtain ⟨b, hb⟩ := hv
    cases hb
    change some b = some x at hd
    cases hd
    exact ⟨True.intro, rfl⟩
  decoder.sufficient v hv := by
    obtain ⟨payload, note, location⟩ := v
    obtain ⟨b, hb⟩ := hv
    cases hb
    exact ⟨b, 0, fun _ _ => rfl⟩

/-- info: 'P4SpecTec.Refine.Representation.natCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms natCodec
#audit_axioms natCodec

/-- The actual `Int` codec is adequate on its independently named constructor shape. -/
theorem intCodec : Codec Shape.int (fun _ : Int => True) where
  encodingValid b _ := ⟨b, rfl⟩
  decoder.sound fuel v x hv hd := by
    obtain ⟨payload, note, location⟩ := v
    obtain ⟨b, hb⟩ := hv
    cases hb
    change some b = some x at hd
    cases hd
    exact ⟨True.intro, rfl⟩
  decoder.sufficient v hv := by
    obtain ⟨payload, note, location⟩ := v
    obtain ⟨b, hb⟩ := hv
    cases hb
    exact ⟨b, 0, fun _ _ => rfl⟩

/-- info: 'P4SpecTec.Refine.Representation.intCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intCodec
#audit_axioms intCodec

/-- The actual `ByteText` codec is adequate on its independently named constructor shape. -/
theorem textCodec : Codec Shape.text (fun _ : ByteText => True) where
  encodingValid b _ := ⟨b, rfl⟩
  decoder.sound fuel v x hv hd := by
    obtain ⟨payload, note, location⟩ := v
    obtain ⟨b, hb⟩ := hv
    cases hb
    change some b = some x at hd
    cases hd
    exact ⟨True.intro, rfl⟩
  decoder.sufficient v hv := by
    obtain ⟨payload, note, location⟩ := v
    obtain ⟨b, hb⟩ := hv
    cases hb
    exact ⟨b, 0, fun _ _ => rfl⟩

/-- info: 'P4SpecTec.Refine.Representation.textCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms textCodec
#audit_axioms textCodec

/-- Raw extern decoding is faithful on its own runtime shape, without a PACKET repair.
Using this for a declared source extern requires a separate source-domain argument. -/
theorem externCodec : Codec Shape.extern (fun _ : ExternValue => True) where
  encodingValid x _ := ⟨x.json, rfl⟩
  decoder.sound fuel v x hv hd := by
    obtain ⟨payload, note, location⟩ := v
    obtain ⟨j, hj⟩ := hv
    cases hj
    change some (ExternValue.mk j) = some x at hd
    cases hd
    exact ⟨True.intro, rfl⟩
  decoder.sufficient v hv := by
    obtain ⟨payload, note, location⟩ := v
    obtain ⟨j, hj⟩ := hv
    cases hj
    exact ⟨⟨j⟩, 0, fun _ _ => rfl⟩

/-- info: 'P4SpecTec.Refine.Representation.externCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms externCodec
#audit_axioms externCodec

/-- Restrict an extended runtime codec to an independently justified source domain.
The admission proof prevents runtime-only constructors leaking into source inputs. -/
theorem Codec.restrict {α : Type} [ToValue α] [OfValue α]
    {runtime source : SourceDomain} {runtimeAdmitted admitted : α → Prop}
    (contract : Codec runtime runtimeAdmitted)
    (included : ∀ v, source v → runtime v)
    (valid : ∀ x, admitted x → source (toValue x))
    (closed : ∀ v x, source v → runtimeAdmitted x → Rel v x → admitted x) :
    Codec source admitted where
  encodingValid := valid
  decoder.sound fuel v x hv hd := by
    obtain ⟨ha, hr⟩ := contract.decoder.sound fuel v x (included v hv) hd
    exact ⟨closed v x hv ha hr, hr⟩
  decoder.sufficient v hv := contract.decoder.sufficient v (included v hv)

/-- info: 'P4SpecTec.Refine.Representation.Codec.restrict' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Codec.restrict
#audit_axioms Codec.restrict

/-- Canonical observation distinguishes admitted generated inputs. -/
def Faithful {α : Type} [ToValue α] (admitted : α → Prop) : Prop :=
  ∀ x y, admitted x → admitted y → Rel (toValue x) y → x = y

/-- Decoder sufficiency gives an exact round trip when admitted representations are faithful. -/
theorem Codec.roundTrip {α : Type} [ToValue α] [OfValue α] {source : SourceDomain}
    {admitted : α → Prop} (contract : Codec source admitted) (faithful : Faithful admitted)
    (x : α) (hx : admitted x) : Decodes (OfValue.ofValue (α := α)) (toValue x) x := by
  have hv := contract.encodingValid x hx
  obtain ⟨y, bound, hb⟩ := contract.decoder.sufficient (toValue x) hv
  obtain ⟨hy, hr⟩ := contract.decoder.sound bound (toValue x) y hv
    (hb bound (Nat.le_refl _))
  have heq := faithful x y hx hy hr
  subst y
  exact ⟨bound, hb⟩

/-- info: 'P4SpecTec.Refine.Representation.Codec.roundTrip' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Codec.roundTrip
#audit_axioms Codec.roundTrip

end P4SpecTec.Refine.Representation
