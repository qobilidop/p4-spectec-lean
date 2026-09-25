import P4SpecTec.Prelude.Value

/-!
Map builtins. Mirrors `p4spec/lib/interface/builtin/maps.ml`. A map is
the spec's `map<K, V> = set<pair<K, V>>`; these functions take and return
its list of pairs, keep insertion order as `map_update` does, and compare
keys by value. The generated wrapper supplies the pair case's constructor
and projection.
-/

namespace P4SpecTec.Prelude.Builtins.Maps

/-- Mirrors `map_find_opt`. -/
def find {K V : Type} [ToValue K] (k : K) (pairs : List (K × V)) : Option V :=
  let v := toValue k
  (pairs.find? fun (k', _) => Value.eq v (toValue k')).map (·.2)

/-- Mirrors `map_update`: replace in place or append. -/
def update {K V : Type} [ToValue K] (k : K) (v : V) : List (K × V) → List (K × V)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if valueEq k k' then (k, v) :: rest else (k', v') :: update k v rest

/-- `dec $find_map<K, V>(map<K, V>, K) : V?`. -/
def find_map {K V : Type} [ToValue K] (m : List (K × V)) (k : K) : Option V := find k m

/-- `dec $find_maps<K, V>(map<K, V>*, K) : V?`: the first map that has the key. -/
def find_maps {K V : Type} [ToValue K] (ms : List (List (K × V))) (k : K) : Option V :=
  ms.findSome? (find k)

/-- `dec $add_map<K, V>(map<K, V>, K, V) : map<K, V>`. -/
def add_map {K V : Type} [ToValue K] (m : List (K × V)) (k : K) (v : V) : List (K × V) :=
  update k v m

/-- `dec $adds_map<K, V>(map<K, V>, K*, V*) : map<K, V>`; `none` on a
length mismatch, where `List.fold_left2` raises. -/
def adds_map {K V : Type} [ToValue K] (m : List (K × V)) (ks : List K) (vs : List V) :
    Option (List (K × V)) :=
  if ks.length == vs.length then some ((ks.zip vs).foldl (fun m (k, v) => update k v m) m)
  else none

/-- `dec $update_map<K, V>(map<K, V>, K, V) : map<K, V>`. -/
def update_map {K V : Type} [ToValue K] (m : List (K × V)) (k : K) (v : V) : List (K × V) :=
  update k v m

end P4SpecTec.Prelude.Builtins.Maps
