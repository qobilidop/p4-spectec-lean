import Init.Data.List.Sort.Lemmas
import P4SpecTec.Interface.Builtin.Sets
import P4SpecTec.Refine.Value
import P4SpecTec.Tactic.Audit

/-!
Ordering respects the canonical observations used by refinement. Extern values
are compared through their original compressed JSON strings: comparing canonical
externs again would quote those strings and change ordering. This module is our
own proof support, not an upstream mirror.
-/

namespace P4SpecTec.Refine.ValueOrder

open P4SpecTec.Util.Source P4SpecTec.Domain P4SpecTec.Lang.Il
open P4SpecTec.Runtime.Value

-- Constructor cases share simp sets, whose members are not used in every case.
set_option linter.unusedSimpArgs false

/-- The payload used after comparing atom constructor tags. -/
private def atomPayload : Atom.t → String
  | .Keyword s | .Tag s | .Operator s => s
  | _ => ""

private theorem atomComparison (a b : Atom.t) : Atom.compare a b =
    compareLex (compareOn Atom.tag) (compareOn atomPayload) a b := by
  cases a <;> cases b <;>
    simp [Atom.compare, Atom.tag, atomPayload, compareLex, compareOn, Nat.compare_eq_ite_lt]

private instance atomTransCmp : Std.TransCmp Atom.compare := by
  have heq : Atom.compare = compareLex (compareOn Atom.tag) (compareOn atomPayload) :=
    funext fun a => funext fun b => atomComparison a b
  rw [heq]
  infer_instance

private instance byteTextTransOrd : Std.TransOrd ByteText :=
  inferInstanceAs (Std.TransCmp (compareOn fun t : ByteText => t.bytes.data))

/-- A triple of comparisons has coherent equality and same-direction composition. -/
private def Chain (ab bc ac : Ordering) : Prop :=
  (ab = .eq → ac = bc) ∧ (bc = .eq → ac = ab) ∧ (ab = bc → ab = ac)

private theorem chainOfTransCmp {α : Type} (cmp : α → α → Ordering) [Std.TransCmp cmp]
    (a b c : α) : Chain (cmp a b) (cmp b c) (cmp a c) := by
  refine ⟨Std.TransCmp.congr_left, fun h => (Std.TransCmp.congr_right h).symm, ?_⟩
  intro h
  cases hab : cmp a b with
  | lt => exact (Std.TransCmp.lt_trans hab (h.symm.trans hab)).symm
  | eq => exact (Std.TransCmp.eq_trans hab (h.symm.trans hab)).symm
  | gt => exact (Std.TransCmp.gt_trans hab (h.symm.trans hab)).symm

private theorem chainThen (ab bc ac de ef df : Ordering)
    (first : Chain ab bc ac) (second : Chain de ef df) :
    Chain (ab.then de) (bc.then ef) (ac.then df) := by
  cases ab <;> cases bc <;> cases ac <;> cases de <;> cases ef <;> cases df <;>
    simp_all [Chain, Ordering.then]

private theorem compareNumChain (a b c : Lang.Xl.Num.t) :
    Chain (compareNum a b) (compareNum b c) (compareNum a c) := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
    first
    | (simp [compareNum, Chain]; done)
    | (simpa only [compareNum] using chainOfTransCmp Ord.compare a b c)

set_option maxHeartbeats 2000000

mutual

private theorem compareChain : ∀ (a b c : value),
    Chain (Runtime.Value.compare a b) (Runtime.Value.compare b c) (Runtime.Value.compare a c)
  | ⟨a, _, _⟩, ⟨b, _, _⟩, ⟨c, _, _⟩ => by
    simpa only [Runtime.Value.compare] using comparePayloadChain a b c
termination_by a b c => sizeOf a + sizeOf b + sizeOf c

private theorem comparePayloadChain : ∀ (a b c : value'),
    Chain (compare' a b) (compare' b c) (compare' a c)
  | a, b, c => by
    rcases a with a | a | a | a | a | a | (_ | a) | a | a | a <;>
    rcases b with b | b | b | b | b | b | (_ | b) | b | b | b <;>
    rcases c with c | c | c | c | c | c | (_ | c) | c | c | c <;>
      first
      | (simp [compare', tag, Chain, Nat.compare_eq_ite_lt]; done)
      | (simpa only [compare'] using chainOfTransCmp Ord.compare a b c)
      | (simpa only [compare'] using compareNumChain a b c)
      | (simpa only [compare'] using compareFieldsChain a b c)
      | (simpa only [compare'] using compareMixfixChain a b c)
      | (simpa only [compare'] using comparesChain a b c)
      | (simpa only [compare'] using compareChain a b c)
      | (simpa only [compare'] using chainOfTransCmp Ord.compare a.compress b.compress c.compress)
termination_by a b c => sizeOf a + sizeOf b + sizeOf c

private theorem compareFieldsChain : ∀ (a b c : List (Lang.Il.atom × value)),
    Chain (compareFields a b) (compareFields b c) (compareFields a c)
  | a, b, c => by
    cases a with
    | nil => cases b <;> cases c <;> simp [compareFields, Chain]
    | cons a as =>
      cases b with
      | nil => cases c <;> simp [compareFields, Chain]
      | cons b bs =>
        cases c with
        | nil => simp [compareFields, Chain]
        | cons c cs =>
          obtain ⟨aa, av⟩ := a
          obtain ⟨ba, bv⟩ := b
          obtain ⟨ca, cv⟩ := c
          simp only [compareFields]
          exact chainThen _ _ _ _ _ _ (chainOfTransCmp Atom.compare aa.it ba.it ca.it)
            (chainThen _ _ _ _ _ _ (compareChain av bv cv) (compareFieldsChain as bs cs))
termination_by a b c => sizeOf a + sizeOf b + sizeOf c

private theorem comparesChain : ∀ (a b c : List value),
    Chain (compares a b) (compares b c) (compares a c)
  | a, b, c => by
    cases a with
    | nil => cases b <;> cases c <;> simp [compares, Chain]
    | cons a as =>
      cases b with
      | nil => cases c <;> simp [compares, Chain]
      | cons b bs =>
        cases c with
        | nil => simp [compares, Chain]
        | cons c cs =>
          simp only [compares]
          exact chainThen _ _ _ _ _ _ (compareChain a b c) (comparesChain as bs cs)
termination_by a b c => sizeOf a + sizeOf b + sizeOf c

private theorem compareMixfixChain : ∀ (a b c : Mixfix.t value),
    Chain (compareMixfix a b) (compareMixfix b c) (compareMixfix a c)
  | a, b, c => by
    rcases a with a | a | ⟨la, ma, ra⟩ | ⟨la, aa, ra⟩ | a <;>
    rcases b with b | b | ⟨lb, mb, rb⟩ | ⟨lb, ab, rb⟩ | b <;>
    rcases c with c | c | ⟨lc, mc, rc⟩ | ⟨lc, ac, rc⟩ | c <;>
      first
      | (simp [compareMixfix, Mixfix.tag, Chain, Nat.compare_eq_ite_lt]; done)
      | (simpa only [compareMixfix] using compareChain a b c)
      | (simpa only [compareMixfix] using chainOfTransCmp Atom.compare a.it b.it c.it)
      | (simpa only [compareMixfix] using compareMixfixesChain a b c)
      | (simpa only [compareMixfix] using
          chainThen _ _ _ _ _ _ (chainOfTransCmp Atom.compare la.it lb.it lc.it)
            (chainThen _ _ _ _ _ _ (compareMixfixChain ma mb mc)
              (chainOfTransCmp Atom.compare ra.it rb.it rc.it)))
      | (simpa only [compareMixfix] using
          chainThen _ _ _ _ _ _ (compareMixfixChain la lb lc)
            (chainThen _ _ _ _ _ _ (chainOfTransCmp Atom.compare aa.it ab.it ac.it)
              (compareMixfixChain ra rb rc)))
termination_by a b c => sizeOf a + sizeOf b + sizeOf c

private theorem compareMixfixesChain : ∀ (a b c : List (Mixfix.t value)),
    Chain (compareMixfixes a b) (compareMixfixes b c) (compareMixfixes a c)
  | a, b, c => by
    cases a with
    | nil => cases b <;> cases c <;> simp [compareMixfixes, Chain]
    | cons a as =>
      cases b with
      | nil => cases c <;> simp [compareMixfixes, Chain]
      | cons b bs =>
        cases c with
        | nil => simp [compareMixfixes, Chain]
        | cons c cs =>
          simp only [compareMixfixes]
          exact chainThen _ _ _ _ _ _ (compareMixfixChain a b c) (compareMixfixesChain as bs cs)
termination_by a b c => sizeOf a + sizeOf b + sizeOf c

end

set_option maxHeartbeats 200000

/-- Comparison reverses its ordering when the operands are exchanged. -/
theorem compareSwap (a b : value) :
    Runtime.Value.compare a b = (Runtime.Value.compare b a).swap := by
  have hc := compareChain a b a
  have hs : Runtime.Value.compare a a = .eq := (compare_eq_iff a a).mpr rfl
  cases ha : Runtime.Value.compare a b <;> cases hb : Runtime.Value.compare b a <;>
    simp_all [Chain]

/-- info: 'P4SpecTec.Refine.ValueOrder.compareSwap' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compareSwap
#audit_axioms compareSwap

/-- Non-strict runtime value comparison is transitive, including equivalence classes. -/
theorem compareTrans (a b c : value) :
    (Runtime.Value.compare a b).isLE → (Runtime.Value.compare b c).isLE →
      (Runtime.Value.compare a c).isLE := by
  have hc := compareChain a b c
  cases ha : Runtime.Value.compare a b <;> cases hb : Runtime.Value.compare b c <;>
    cases hac : Runtime.Value.compare a c <;> simp_all [Chain]

/-- info: 'P4SpecTec.Refine.ValueOrder.compareTrans' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compareTrans
#audit_axioms compareTrans

/-- The actual structural comparison is a total preorder on value observations. -/
instance valueTransOrd : Std.TransOrd value where
  eq_swap := compareSwap _ _
  isLE_trans := compareTrans _ _ _

/-- info: 'P4SpecTec.Refine.ValueOrder.valueTransOrd' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms valueTransOrd
#audit_axioms valueTransOrd

/-- Canonical equality on both operands preserves the complete ordering result. -/
theorem compareOfCanon {a a' b b' : value} (ha : canon a = canon a')
    (hb : canon b = canon b') :
    Runtime.Value.compare a b = Runtime.Value.compare a' b' := by
  have left := (compareChain a a' b).1 ((compare_eq_iff a a').mpr ha)
  have right := (compareChain a' b b').2.1 ((compare_eq_iff b b').mpr hb)
  exact left.trans right.symm

/-- info: 'P4SpecTec.Refine.ValueOrder.compareOfCanon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compareOfCanon
#audit_axioms compareOfCanon

/-- Related generated operands preserve runtime ordering, beyond its equality case. -/
theorem compareOfRel {α β : Type} [Prelude.ToValue α] [Prelude.ToValue β]
    {v w : value} {x : α} {y : β} (hx : Rel v x) (hy : Rel w y) :
    Runtime.Value.compare v w = Runtime.Value.compare (Prelude.toValue x) (Prelude.toValue y) :=
  compareOfCanon hx hy

/-- info: 'P4SpecTec.Refine.ValueOrder.compareOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms compareOfRel
#audit_axioms compareOfRel

private instance generatedTransCmp {α : Type} [Prelude.ToValue α] :
    Std.TransCmp (Prelude.valueCompare (α := α)) :=
  inferInstanceAs (Std.TransCmp (compareOn Prelude.toValue))

private theorem orderingLe (o : Ordering) : (o != .gt) = o.isLE := by cases o <;> rfl

private theorem compareLeTrans {α : Type} [Prelude.ToValue α] (a b c : α) :
    (Prelude.valueCompare a b != .gt) → (Prelude.valueCompare b c != .gt) →
      (Prelude.valueCompare a c != .gt) := by
  simpa only [orderingLe] using
    (Std.TransCmp.isLE_trans (cmp := Prelude.valueCompare) (a := a) (b := b) (c := c))

private theorem compareLeTotal {α : Type} [Prelude.ToValue α] (a b : α) :
    (Prelude.valueCompare a b != .gt) || (Prelude.valueCompare b a != .gt) := by
  have h := Std.OrientedCmp.eq_swap (cmp := Prelude.valueCompare) (a := a) (b := b)
  cases ha : Prelude.valueCompare a b <;> cases hb : Prelude.valueCompare b a <;>
    simp_all

open P4SpecTec.Prelude P4SpecTec.Builtin.Sets

private theorem dedupSublist {α : Type} [ToValue α] :
    ∀ xs : List α, List.Sublist (normalize.dedup xs) xs
  | [] => .slnil
  | [a] => List.Sublist.refl _
  | a :: b :: rest => by
    by_cases h : valueEq a b = true
    · simpa only [normalize.dedup, h, ite_true] using (dedupSublist (b :: rest)).cons a
    · simpa only [normalize.dedup, h, Bool.false_eq_true, ite_false] using
        (dedupSublist (b :: rest)).cons_cons a

private theorem dedupStrict {α : Type} [ToValue α] :
    ∀ xs : List α, xs.Pairwise (fun a b => valueCompare a b != .gt) →
      (normalize.dedup xs).Pairwise (fun a b => valueCompare a b = .lt)
  | [], _ => by simp [normalize.dedup]
  | [a], _ => by simp [normalize.dedup]
  | a :: b :: rest, sorted => by
    have tailSorted := (List.pairwise_cons.mp sorted).2
    have ih := dedupStrict (b :: rest) tailSorted
    by_cases h : valueEq a b = true
    · simpa only [normalize.dedup, h, ite_true] using ih
    · have habLe := (List.pairwise_cons.mp sorted).1 b (by simp)
      have hne : valueCompare a b ≠ .eq := by
        intro hc
        apply h
        change (valueCompare a b == .eq) = true
        simp [hc]
      have hab : valueCompare a b = .lt := by
        cases hc : valueCompare a b <;> simp_all
      simp only [normalize.dedup, h, Bool.false_eq_true, ite_false]
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih⟩
      intro c hc
      have hc' := (dedupSublist (b :: rest)).subset hc
      rcases List.mem_cons.mp hc' with rfl | hc'
      · exact hab
      · have hbc := (List.pairwise_cons.mp tailSorted).1 c hc'
        exact Std.TransCmp.lt_of_lt_of_isLE (cmp := valueCompare) hab
          (by simpa only [orderingLe] using hbc)

private theorem dedupOfStrict {α : Type} [ToValue α] :
    ∀ xs : List α, xs.Pairwise (fun a b => valueCompare a b = .lt) →
      normalize.dedup xs = xs
  | [], _ => rfl
  | [a], _ => rfl
  | a :: b :: rest, sorted => by
    have hab := (List.pairwise_cons.mp sorted).1 b (by simp)
    have hneq : valueEq a b = false := by
      change (valueCompare a b == .eq) = false
      simp [hab]
    simp only [normalize.dedup, hneq, Bool.false_eq_true, ite_false,
      dedupOfStrict (b :: rest) (List.pairwise_cons.mp sorted).2]

/-- Actual set normalization is idempotent for arbitrary represented element types.
Sorting uses the runtime total preorder; deduplication retains its chosen representatives. -/
theorem normalizeIdempotent {α : Type} [ToValue α] (xs : List α) :
    normalize (normalize xs) = normalize xs := by
  have hs := List.pairwise_mergeSort (compareLeTrans (α := α)) (compareLeTotal (α := α)) xs
  have hsub := hs.sublist (dedupSublist _)
  have hstrict := dedupStrict _ hs
  simp only [normalize]
  rw [List.mergeSort_of_pairwise hsub]
  exact dedupOfStrict _ hstrict

/-- info: 'P4SpecTec.Refine.ValueOrder.normalizeIdempotent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms normalizeIdempotent
#audit_axioms normalizeIdempotent

end P4SpecTec.Refine.ValueOrder
