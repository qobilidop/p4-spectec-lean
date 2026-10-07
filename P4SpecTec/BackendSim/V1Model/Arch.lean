import P4SpecTec.BackendSim.V1Model.Multicast

/-!
Port of `p4spec/lib/backend-sim/v1model/{mirror,scheduler,arch}.ml`: the mirror table
(sessions to ports), the packet queue (upstream's single-list deque) and the architecture
state record with its conversion to and from the `archState` extern value, whose payload
is the record's JSON.
-/

namespace P4SpecTec.BackendSim.V1Model

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.BackendSim.SpecImpl
open P4SpecTec.BackendSim.Core.Object (Error)
open P4SpecTec.BackendSim.V1Model.Packet (intOf fieldOf)

/-! Mirrors `Mirror.Table`: sessions to ports. -/
namespace Mirror.Table

/-- Mirrors `t`. -/
abbrev t := Multicast.IntMap Int

/-- Mirrors `empty`. -/
def empty : t := []

/-- Mirrors `add`. -/
def add (session port : Int) (table : t) : t := Multicast.IntMap.add session port table

/-- Mirrors `find_opt`. -/
def find_opt (session : Int) (table : t) : Option Int := Multicast.IntMap.find_opt session table

/-- Mirrors `to_yojson`. -/
def to_yojson (table : t) : Lean.Json := Multicast.IntMap.to_yojson Lean.toJson table

/-- Mirrors `of_yojson`. -/
def of_yojson (json : Lean.Json) : Except Error t := Multicast.IntMap.of_yojson intOf json

end Mirror.Table

/-! Mirrors `Scheduler`, upstream's deque as one list. -/
namespace Scheduler

/-- Mirrors `t`. -/
abbrev t := List Packet.t

/-- Mirrors `empty`. -/
def empty : t := []

/-- Mirrors `push_back`. -/
def push_back (x : Packet.t) (q : t) : t := q ++ [x]

/-- Mirrors `push_front`. -/
def push_front (x : Packet.t) (q : t) : t := x :: q

/-- Mirrors `pop_front_opt`. -/
def pop_front_opt : t → Option (Packet.t × t)
  | [] => none
  | hd :: tl => some (hd, tl)

/-- Mirrors `to_yojson`. -/
def to_yojson (q : t) : Lean.Json := .arr (q.map Packet.to_yojson).toArray

/-- Mirrors `of_yojson`. -/
def of_yojson (json : Lean.Json) : Except Error t := do
  (← json.getArr?.mapError fun _ => .decode).toList.mapM Packet.of_yojson

end Scheduler

/-! Mirrors `Arch`. -/
namespace Arch

/-- Mirrors `t`. -/
structure t where
  /-- The scheduled packets. -/
  queue : Scheduler.t
  /-- The mirror sessions. -/
  mirrortable : Mirror.Table.t
  /-- The multicast state. -/
  multicast : Multicast.State.t
  /-- The current packet's requests. -/
  action : Packet.action

/-- Mirrors `empty`. -/
def empty : t :=
  { queue := Scheduler.empty, mirrortable := Mirror.Table.empty,
    multicast := Multicast.State.empty, action := Packet.empty_action }

/-- Mirrors `reset`: forget the current packet's requests. -/
def reset (a : t) : t := { a with action := Packet.empty_action }

/-- Mirrors `to_yojson`. -/
def to_yojson (a : t) : Lean.Json := Lean.Json.mkObj
  [("queue", Scheduler.to_yojson a.queue), ("mirrortable", Mirror.Table.to_yojson a.mirrortable),
   ("multicast", Multicast.State.to_yojson a.multicast),
   ("action", Packet.action_to_yojson a.action)]

/-- Mirrors `of_yojson`. -/
def of_yojson (json : Lean.Json) : Except Error t := do
  pure { queue := ← Scheduler.of_yojson (← fieldOf json "queue"),
         mirrortable := ← Mirror.Table.of_yojson (← fieldOf json "mirrortable"),
         multicast := ← Multicast.State.of_yojson (← fieldOf json "multicast"),
         action := ← Packet.action_of_yojson (← fieldOf json "action") }

/-- Mirrors `to_value`. -/
def to_value (a : t) : value := Pack.archState (to_yojson a)

/-- Mirrors `of_value` followed by `Result.get_ok`: a value that is not a well-formed
architecture state raises upstream. -/
def of_value (v : value) : Except Error t := do
  let some json := Value.Get.extern v | throw .decode
  of_yojson json

/-- Mirrors `with_queue`. -/
def with_queue (queue : Scheduler.t) (a : t) : t := { a with queue }

/-- Mirrors `with_mirrortable`. -/
def with_mirrortable (mirrortable : Mirror.Table.t) (a : t) : t := { a with mirrortable }

/-- Mirrors `with_multicast`. -/
def with_multicast (multicast : Multicast.State.t) (a : t) : t := { a with multicast }

/-- Mirrors `with_clone`. -/
def with_clone (clone : Packet.CloneInfo.t) (a : t) : t :=
  { a with action := { a.action with clone_opt := some clone } }

/-- Mirrors `with_resubmit`. -/
def with_resubmit (resubmit : Packet.ResubmitInfo.t) (a : t) : t :=
  { a with action := { a.action with resubmit_opt := some resubmit } }

/-- Mirrors `with_recirculate`. -/
def with_recirculate (recirculate : Packet.RecirculateInfo.t) (a : t) : t :=
  { a with action := { a.action with recirculate_opt := some recirculate } }

end Arch

end P4SpecTec.BackendSim.V1Model
