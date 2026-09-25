import P4SpecTec.Prelude.Value

/-!
Set builtins. Mirrors `p4spec/lib/interface/builtin/sets.ml`. Upstream
holds a set as an OCaml `Set` ordered by `Value.compare` and returns its
elements in that order; these functions take and return the element list
of the spec's `set<K>` case and keep that order. The generated wrapper
supplies the case's constructor and projection.
-/

namespace P4SpecTec.Prelude.Builtins.Sets

/-- Elements sorted by value, duplicates removed: `VSet.elements` of
`VSet.of_list`. -/
def normalize {K : Type} [ToValue K] (ks : List K) : List K :=
  dedup (ks.mergeSort fun a b => valueCompare a b != .gt)
where
  /-- Remove adjacent equal values. -/
  dedup : List K → List K
    | [] => []
    | [k] => [k]
    | a :: b :: rest => if valueEq a b then dedup (b :: rest) else a :: dedup (b :: rest)

/-- Membership by value. -/
def mem {K : Type} [ToValue K] (k : K) (ks : List K) : Bool := ks.any (valueEq k)

/-- `dec $intersect_set<K>(set<K>, set<K>) : set<K>`. -/
def intersect_set {K : Type} [ToValue K] (a b : List K) : List K :=
  normalize (a.filter fun k => mem k b)

/-- `dec $union_set<K>(set<K>, set<K>) : set<K>`. -/
def union_set {K : Type} [ToValue K] (a b : List K) : List K := normalize (a ++ b)

/-- `dec $unions_set<K>(set<K>*) : set<K>`. -/
def unions_set {K : Type} [ToValue K] (sets : List (List K)) : List K := normalize sets.flatten

/-- `dec $diff_set<K>(set<K>, set<K>) : set<K>`. -/
def diff_set {K : Type} [ToValue K] (a b : List K) : List K :=
  normalize (a.filter fun k => !mem k b)

/-- `dec $sub_set<K>(set<K>, set<K>) : bool`. -/
def sub_set {K : Type} [ToValue K] (a b : List K) : Bool := a.all fun k => mem k b

/-- `dec $eq_set<K>(set<K>, set<K>) : bool`. -/
def eq_set {K : Type} [ToValue K] (a b : List K) : Bool := sub_set a b && sub_set b a

end P4SpecTec.Prelude.Builtins.Sets
