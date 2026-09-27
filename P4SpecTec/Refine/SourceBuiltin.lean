import P4SpecTec.Interface.Builtin.Lists
import P4SpecTec.Interface.Builtin.Maps
import P4SpecTec.Interface.Builtin.Sets
import P4SpecTec.Refine.Representation.SourceCodec
import P4SpecTec.Tactic.Audit

/-!
Builtin collection operations preserve arbitrary independently supplied element domains.
These lemmas describe actual copied elements, without equality or ordering law assumptions.
Source codec coverage and constructor adapters are separate obligations.
-/

namespace P4SpecTec.Refine.SourceBuiltin
open P4SpecTec.Prelude

/-- Actual adjacent deduplication only removes elements from its input domain. -/
theorem dedupPreserves {α : Type} [ToValue α] (domain : α → Prop) (xs : List α)
    (valid : ∀ x ∈ xs, domain x) : ∀ x ∈ Builtin.Sets.normalize.dedup xs, domain x := by
  induction xs with
  | nil => simp [Builtin.Sets.normalize.dedup]
  | cons a xs ih =>
    cases xs with
    | nil => simpa only [Builtin.Sets.normalize.dedup] using valid
    | cons b xs =>
      have tail : ∀ x ∈ b :: xs, domain x := by
        intro x member
        exact valid x (List.mem_cons_of_mem _ member)
      simp only [Builtin.Sets.normalize.dedup]
      split
      · exact ih tail
      · intro x member
        rcases List.mem_cons.mp member with rfl | member
        · exact valid _ List.mem_cons_self
        · exact ih tail x member

/-- info: 'P4SpecTec.Refine.SourceBuiltin.dedupPreserves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dedupPreserves
#audit_axioms dedupPreserves

/-- Sorting and adjacent deduplication retain the independently admitted source elements. -/
theorem normalizePreserves {α : Type} [ToValue α] (domain : α → Prop) (xs : List α)
    (valid : ∀ x ∈ xs, domain x) : ∀ x ∈ Builtin.Sets.normalize xs, domain x := by
  apply dedupPreserves
  intro x member
  exact valid x (List.mem_mergeSort.mp member)

/-- info: 'P4SpecTec.Refine.SourceBuiltin.normalizePreserves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms normalizePreserves
#audit_axioms normalizePreserves

/-- Actual intersection returns only elements already admitted by its first input. -/
theorem intersectPreserves {α : Type} [ToValue α] (domain : α → Prop) (xs ys : List α)
    (valid : ∀ x ∈ xs, domain x) : ∀ x ∈ Builtin.Sets.intersect_set xs ys, domain x := by
  apply normalizePreserves
  intro x member
  exact valid x (List.mem_filter.mp member).1

/-- info: 'P4SpecTec.Refine.SourceBuiltin.intersectPreserves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms intersectPreserves
#audit_axioms intersectPreserves

/-- Actual difference returns only elements already admitted by its first input. -/
theorem diffPreserves {α : Type} [ToValue α] (domain : α → Prop) (xs ys : List α)
    (valid : ∀ x ∈ xs, domain x) : ∀ x ∈ Builtin.Sets.diff_set xs ys, domain x := by
  apply normalizePreserves
  intro x member
  exact valid x (List.mem_filter.mp member).1

/-- info: 'P4SpecTec.Refine.SourceBuiltin.diffPreserves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms diffPreserves
#audit_axioms diffPreserves

/-- Actual union preserves the domain of both input lists. -/
theorem unionPreserves {α : Type} [ToValue α] (domain : α → Prop) (xs ys : List α)
    (left : ∀ x ∈ xs, domain x) (right : ∀ y ∈ ys, domain y) :
    ∀ x ∈ Builtin.Sets.union_set xs ys, domain x := by
  apply normalizePreserves
  intro x member
  rcases List.mem_append.mp member with member | member
  · exact left x member
  · exact right x member

/-- info: 'P4SpecTec.Refine.SourceBuiltin.unionPreserves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unionPreserves
#audit_axioms unionPreserves

/-- Actual multi-union preserves each input collection's independent domain. -/
theorem unionsPreserves {α : Type} [ToValue α] (domain : α → Prop) (xss : List (List α))
    (valid : ∀ xs ∈ xss, ∀ x ∈ xs, domain x) :
    ∀ x ∈ Builtin.Sets.unions_set xss, domain x := by
  apply normalizePreserves
  intro x member
  obtain ⟨xs, outer, inner⟩ := List.mem_flatten.mp member
  exact valid xs outer x inner

/-- info: 'P4SpecTec.Refine.SourceBuiltin.unionsPreserves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unionsPreserves
#audit_axioms unionsPreserves

/-- Actual reverse preserves every independently admitted input element. -/
theorem reversePreserves {α : Type} (domain : α → Prop) (xs : List α)
    (valid : ∀ x ∈ xs, domain x) : ∀ x ∈ Builtin.Lists.rev_ xs, domain x := by
  intro x member
  exact valid x (List.mem_reverse.mp member)

/-- info: 'P4SpecTec.Refine.SourceBuiltin.reversePreserves' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms reversePreserves
#audit_axioms reversePreserves

/-- Actual map lookup returns a value from an admitted pair, regardless of key equality laws. -/
theorem findPreserves {K V : Type} [ToValue K] (domain : V → Prop) (key : K)
    (pairs : List (K × V)) (valid : ∀ pair ∈ pairs, domain pair.2)
    (value : V) (found : Builtin.Maps.find key pairs = some value) : domain value := by
  unfold Builtin.Maps.find at found
  cases selected : pairs.find? (fun pair => Runtime.Value.eq (toValue key) (toValue pair.1)) with
  | none => simp only [selected, Option.map_none] at found; cases found
  | some pair =>
    simp only [selected, Option.map_some] at found
    cases Option.some.inj found
    exact valid pair (List.mem_of_find?_eq_some selected)

/-- info: 'P4SpecTec.Refine.SourceBuiltin.findPreserves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms findPreserves
#audit_axioms findPreserves

/-- Actual first-map lookup preserves the domain of every candidate map's values. -/
theorem findMapsPreserves {K V : Type} [ToValue K] (domain : V → Prop) (key : K)
    (maps : List (List (K × V)))
    (valid : ∀ pairs ∈ maps, ∀ pair ∈ pairs, domain pair.2)
    (value : V) (found : Builtin.Maps.find_maps maps key = some value) : domain value := by
  obtain ⟨pairs, member, selected⟩ := List.exists_of_findSome?_eq_some found
  exact findPreserves domain key pairs (valid pairs member) value selected

/-- info: 'P4SpecTec.Refine.SourceBuiltin.findMapsPreserves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms findMapsPreserves
#audit_axioms findMapsPreserves

/-- Actual association lookup preserves the second component's source domain. -/
theorem assocPreserves {K V : Type} [ToValue K] (domain : V → Prop) (key : K)
    (pairs : List (K × V)) (valid : ∀ pair ∈ pairs, domain pair.2)
    (value : V) (found : Builtin.Lists.assoc_ key pairs = some value) : domain value :=
  findPreserves domain key pairs valid value found

/-- info: 'P4SpecTec.Refine.SourceBuiltin.assocPreserves' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms assocPreserves
#audit_axioms assocPreserves

/-- Optional results inherit the independent source domain of every present result. -/
theorem optionSource {α : Type} [ToValue α] {spec externalDomain}
    (element : Lang.Il.typ) (result : Option α)
    (valid : ∀ x, result = some x →
      Representation.Source.Valid spec externalDomain element.it (toValue x)) :
    Representation.Source.Valid spec externalDomain (.IterT element .Opt) (toValue result) := by
  cases result with
  | none => exact .none _ _ rfl
  | some x => exact .some _ _ _ rfl (valid x rfl)

/-- info: 'P4SpecTec.Refine.SourceBuiltin.optionSource' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms optionSource
#audit_axioms optionSource

/-- Actual reverse preserves the complete independent source list predicate. -/
theorem reverseSource {α : Type} [ToValue α] {spec externalDomain}
    (element : Lang.Il.typ) (xs : List α)
    (valid : Representation.Source.Valid spec externalDomain (.IterT element .List)
      (toValue xs)) :
    Representation.Source.Valid spec externalDomain (.IterT element .List)
      (toValue (Builtin.Lists.rev_ xs)) := by
  exact (Representation.Source.encodedListIff element _).mpr
    (reversePreserves _ xs ((Representation.Source.encodedListIff element xs).mp valid))

/-- info: 'P4SpecTec.Refine.SourceBuiltin.reverseSource' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverseSource
#audit_axioms reverseSource

end P4SpecTec.Refine.SourceBuiltin
