import P4SpecTec.BackendSim.V1Model.Packet

/-!
Port of `p4spec/lib/backend-sim/v1model/multicast.ml`: multicast groups and replication
nodes. Upstream's integer-keyed maps (`Util.Json.Map`) are association lists kept in
ascending key order, so their JSON objects list the same keys; an insertion replaces an
existing key, as `Map.add` does.
-/

namespace P4SpecTec.BackendSim.V1Model.Multicast

open P4SpecTec.BackendSim.Core.Object (Error)
open P4SpecTec.BackendSim.V1Model.Packet (intOf fieldOf)

/-- A node handle. -/
abbrev handle := Int
/-- A port. -/
abbrev port := Int
/-- A multicast group identifier. -/
abbrev mgid := Int
/-- A replication identifier. -/
abbrev rid := Int

/-- An integer-keyed map as an ascending association list; mirrors `Util.Json.Map`. -/
abbrev IntMap (α : Type) := List (Int × α)

/-- Mirrors `Map.add`: insert or replace, keeping ascending order. -/
def IntMap.add {α : Type} (key : Int) (x : α) : IntMap α → IntMap α
  | [] => [(key, x)]
  | (k, y) :: rest =>
    if key < k then (key, x) :: (k, y) :: rest
    else if key == k then (key, x) :: rest
    else (k, y) :: IntMap.add key x rest

/-- Mirrors `Map.find_opt`. -/
def IntMap.find_opt {α : Type} (key : Int) (m : IntMap α) : Option α :=
  (m.find? fun (k, _) => k == key).map (·.2)

/-- Mirrors `Map.update` with a mapping function: an absent key stays absent. -/
def IntMap.update {α : Type} (key : Int) (f : α → α) : IntMap α → IntMap α
  | [] => []
  | (k, y) :: rest => if k == key then (k, f y) :: rest else (k, y) :: IntMap.update key f rest

/-- Mirrors the map's `to_yojson`: an object keyed by the decimal keys. -/
def IntMap.to_yojson {α : Type} (encode : α → Lean.Json) (m : IntMap α) : Lean.Json :=
  Lean.Json.mkObj (m.map fun (k, x) => (toString k, encode x))

/-- Mirrors the map's `of_yojson`; a key that is not an integer is a decoding error. -/
def IntMap.of_yojson {α : Type} (decode : Lean.Json → Except Error α) (json : Lean.Json) :
    Except Error (IntMap α) := do
  let .obj kvs := json | throw .decode
  let mut result : IntMap α := []
  for (k, v) in kvs.toArray do
    let some key := k.toInt? | throw .decode
    result := IntMap.add key (← decode v) result
  pure result

/-- Mirrors `group`. -/
structure group where
  /-- The group identifier. -/
  id : mgid
  /-- The handles of its nodes, most recently associated first. -/
  node_handles : List handle
  deriving BEq, Repr

/-- Mirrors `group_to_yojson`. -/
def group_to_yojson (g : group) : Lean.Json := Lean.Json.mkObj
  [("id", Lean.toJson g.id), ("node_handles", Lean.toJson g.node_handles)]

/-- Mirrors `group_of_yojson`. -/
def group_of_yojson (json : Lean.Json) : Except Error group := do
  let handles ← (← fieldOf json "node_handles").getArr?.mapError fun _ => .decode
  pure { id := ← intOf (← fieldOf json "id"), node_handles := ← handles.toList.mapM intOf }

/-- Mirrors `node`. -/
structure node where
  /-- The output port. -/
  port : port
  /-- The replication identifier. -/
  rid : rid
  deriving BEq, Repr

/-- Mirrors `node_to_yojson`. -/
def node_to_yojson (n : node) : Lean.Json := Lean.Json.mkObj
  [("port", Lean.toJson n.port), ("rid", Lean.toJson n.rid)]

/-- Mirrors `node_of_yojson`. -/
def node_of_yojson (json : Lean.Json) : Except Error node := do
  pure { port := ← intOf (← fieldOf json "port"), rid := ← intOf (← fieldOf json "rid") }

/-! Mirrors `State`. -/
namespace State

/-- Mirrors `t`. -/
structure t where
  /-- The next node handle. -/
  next_handle : handle
  /-- Groups by identifier. -/
  groups : IntMap group
  /-- Nodes by handle. -/
  nodes : IntMap (List node)
  deriving Repr

/-- Mirrors `empty`. -/
def empty : t := { next_handle := 0, groups := [], nodes := [] }

/-- Mirrors `to_yojson`. -/
def to_yojson (s : t) : Lean.Json := Lean.Json.mkObj
  [("next_handle", Lean.toJson s.next_handle),
   ("groups", IntMap.to_yojson group_to_yojson s.groups),
   ("nodes", IntMap.to_yojson (fun ns => .arr (ns.map node_to_yojson).toArray) s.nodes)]

/-- Mirrors `of_yojson`. -/
def of_yojson (json : Lean.Json) : Except Error t := do
  pure { next_handle := ← intOf (← fieldOf json "next_handle"),
         groups := ← IntMap.of_yojson group_of_yojson (← fieldOf json "groups"),
         nodes := ← IntMap.of_yojson (fun j => do
           (← j.getArr?.mapError fun _ => .decode).toList.mapM node_of_yojson)
           (← fieldOf json "nodes") }

/-- Mirrors `group_create`. -/
def group_create (id : mgid) (s : t) : t :=
  { s with groups := IntMap.add id { id, node_handles := [] } s.groups }

/-- Mirrors `node_create`. -/
def node_create (rid : rid) (ports : List port) (s : t) : t :=
  let handle := s.next_handle
  { s with next_handle := handle + 1,
           nodes := IntMap.add handle (ports.map fun port => { port, rid }) s.nodes }

/-- Mirrors `node_associate`. -/
def node_associate (id : mgid) (handle : handle) (s : t) : t :=
  let groups := IntMap.update id (fun g => { g with node_handles := handle :: g.node_handles })
    s.groups
  { s with groups }

end State

end P4SpecTec.BackendSim.V1Model.Multicast
