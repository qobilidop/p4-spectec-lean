import P4SpecTec.Prelude.Value

/-!
List builtins. Mirrors `p4spec/lib/interface/builtin/lists.ml`, function
for function. `distinct_` and `assoc_` compare by value, as upstream.
-/

namespace P4SpecTec.Builtin.Lists

open P4SpecTec.Prelude

/-- `dec $rev_<X>(X*) : X*`. -/
def rev_ {X : Type} (xs : List X) : List X := xs.reverse

/-- `dec $concat_<X>((X*)*) : X*`. -/
def concat_ {X : Type} (xss : List (List X)) : List X := xss.flatten

/-- `dec $distinct_<K>(K*) : bool`: no two elements are equal values. -/
def distinct_ {K : Type} [ToValue K] (ks : List K) : Bool :=
  go (ks.map toValue)
where
  /-- No element equals a later one. -/
  go : List _ → Bool
    | [] => true
    | v :: vs => !(vs.any (Runtime.Value.eq v)) && go vs

/-- `dec $partition_<X>(X*, nat) : (X*, X*)`. -/
def partition_ {X : Type} (xs : List X) (n : Nat) : List X × List X := (xs.take n, xs.drop n)

/-- `dec $assoc_<X, Y>(X, (X, Y)*) : Y?`: the first pair whose key equals
the value. -/
def assoc_ {X Y : Type} [ToValue X] (x : X) (pairs : List (X × Y)) : Option Y :=
  let v := toValue x
  (pairs.find? fun (k, _) => Runtime.Value.eq v (toValue k)).map (·.2)

/-- `dec $sort_<X>((nat, X)*) : (nat, X)*`: a stable sort by key. -/
def sort_ {X : Type} (pairs : List (Nat × X)) : List (Nat × X) :=
  pairs.mergeSort fun a b => a.1 ≤ b.1

/-- `dec $transpose_<X>(X**) : X**`; `none` on ragged rows. -/
def transpose_ {X : Type} (rows : List (List X)) : Option (List (List X)) :=
  match rows with
  | [] => some []
  | row :: _ =>
    let width := row.length
    if rows.all (·.length == width) then
      some ((List.range width).map fun j => rows.filterMap (·[j]?))
    else none

end P4SpecTec.Builtin.Lists
