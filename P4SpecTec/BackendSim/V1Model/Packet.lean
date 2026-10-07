import P4SpecTec.BackendSim.Core.Object
import P4SpecTec.Lang.Il.Encode

/-!
Port of `p4spec/lib/backend-sim/v1model/packet.ml`: clone, resubmit and recirculate
requests, the per-packet action record and the scheduled packet, with the JSON
representations `[@@deriving yojson]` gives them (a variant is a list headed by its
constructor name, a tuple a list, an option `null` or the value, a record an object). A
scheduled packet carries an IL context, encoded with `Lang.Il.Encode`.
-/

namespace P4SpecTec.BackendSim.V1Model.Packet

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.BackendSim.SpecImpl
open P4SpecTec.BackendSim.Core.Object (Error)

/-- Decode a JSON integer, as `int_of_yojson`. -/
def intOf (json : Lean.Json) : Except Error Int := json.getInt?.mapError fun _ => .decode

/-- Decode an option, as `option_of_yojson`. -/
def optOf {α : Type} (decode : Lean.Json → Except Error α) : Lean.Json → Except Error (Option α)
  | .null => pure none
  | json => some <$> decode json

/-- Encode an option, as `option_to_yojson`. -/
def optTo {α : Type} (encode : α → Lean.Json) : Option α → Lean.Json
  | none => .null
  | some x => encode x

/-- A field of a JSON object. -/
def fieldOf (json : Lean.Json) (name : String) : Except Error Lean.Json :=
  (json.getObjVal? name).mapError fun _ => .decode

/-! Mirrors `CloneInfo`. -/
namespace CloneInfo

/-- Mirrors `clone_type`. -/
inductive clone_type where
  /-- Ingress to egress. -/
  | I2E
  /-- Egress to egress. -/
  | E2E
  deriving BEq, Repr

/-- Mirrors `t`: the clone type, session and field-list index. -/
abbrev t := clone_type × Int × Int

/-- Mirrors `clone_type_to_yojson`. -/
def clone_type_to_yojson : clone_type → Lean.Json
  | .I2E => .arr #[.str "I2E"]
  | .E2E => .arr #[.str "E2E"]

/-- Mirrors `clone_type_of_yojson`. -/
def clone_type_of_yojson : Lean.Json → Except Error clone_type
  | .arr #[.str "I2E"] => pure .I2E
  | .arr #[.str "E2E"] => pure .E2E
  | _ => throw .decode

/-- Mirrors `to_yojson`. -/
def to_yojson (c : t) : Lean.Json :=
  .arr #[clone_type_to_yojson c.1, Lean.toJson c.2.1, Lean.toJson c.2.2]

/-- Mirrors `of_yojson`. -/
def of_yojson : Lean.Json → Except Error t
  | .arr #[ct, session, index] => do
    pure (← clone_type_of_yojson ct, ← intOf session, ← intOf index)
  | _ => throw .decode

/-- Mirrors `of_value`: the enum member, the session and the index; an unknown member or
a malformed value raises upstream. -/
def of_value (value_clone_type value_session value_index : value) : Option t := do
  let (_, name) ← Unpack.unpack_p4_enum value_clone_type
  let clone_type ← if name == ByteText.ofString "I2E" then some .I2E
    else if name == ByteText.ofString "E2E" then some .E2E else none
  let (_, session) ← Unpack.unpack_p4_fixedBit value_session
  let (_, index) ← Unpack.unpack_p4_fixedBit value_index
  pure (clone_type, session, index)

/-- Mirrors `to_value`. -/
def to_value (c : t) : value × value × value :=
  let name := match c.1 with | .I2E => "I2E" | .E2E => "E2E"
  (Pack.pack_p4_enum (ByteText.ofString "CloneType") (ByteText.ofString name),
    Pack.pack_p4_fixedBit 32 c.2.1, Pack.pack_p4_fixedBit 8 c.2.2)

end CloneInfo

/-! Mirrors `ResubmitInfo`: a field-list index. -/
namespace ResubmitInfo

/-- Mirrors `t`. -/
abbrev t := Int

/-- Mirrors `of_value`. -/
def of_value (value_index : value) : Option t := (Unpack.unpack_p4_fixedBit value_index).map (·.2)

/-- Mirrors `to_value`. -/
def to_value (index : t) : value := Pack.pack_p4_fixedBit 8 index

end ResubmitInfo

/-! Mirrors `RecirculateInfo`: a field-list index. -/
namespace RecirculateInfo

/-- Mirrors `t`. -/
abbrev t := Int

/-- Mirrors `of_value`. -/
def of_value (value_index : value) : Option t := (Unpack.unpack_p4_fixedBit value_index).map (·.2)

/-- Mirrors `to_value`. -/
def to_value (index : t) : value := Pack.pack_p4_fixedBit 8 index

end RecirculateInfo

/-- Mirrors `action`: the requests a packet made during ingress or egress. -/
structure action where
  /-- A clone request. -/
  clone_opt : Option CloneInfo.t
  /-- A resubmit request. -/
  resubmit_opt : Option ResubmitInfo.t
  /-- A recirculate request. -/
  recirculate_opt : Option RecirculateInfo.t
  deriving BEq, Repr

/-- Mirrors `empty_action`. -/
def empty_action : action := { clone_opt := none, resubmit_opt := none, recirculate_opt := none }

/-- Mirrors `action_to_yojson`. -/
def action_to_yojson (a : action) : Lean.Json := Lean.Json.mkObj
  [("clone_opt", optTo CloneInfo.to_yojson a.clone_opt),
   ("resubmit_opt", optTo Lean.toJson a.resubmit_opt),
   ("recirculate_opt", optTo Lean.toJson a.recirculate_opt)]

/-- Mirrors `action_of_yojson`. -/
def action_of_yojson (json : Lean.Json) : Except Error action := do
  pure { clone_opt := ← optOf CloneInfo.of_yojson (← fieldOf json "clone_opt"),
         resubmit_opt := ← optOf intOf (← fieldOf json "resubmit_opt"),
         recirculate_opt := ← optOf intOf (← fieldOf json "recirculate_opt") }

/-- Mirrors `entrypoint`: where a scheduled packet resumes. -/
inductive entrypoint where
  /-- At the ingress block. -/
  | Ingress
  /-- At the egress block. -/
  | Egress
  deriving BEq, Repr

/-- Mirrors `entrypoint_to_yojson`. -/
def entrypoint_to_yojson : entrypoint → Lean.Json
  | .Ingress => .arr #[.str "Ingress"]
  | .Egress => .arr #[.str "Egress"]

/-- Mirrors `entrypoint_of_yojson`. -/
def entrypoint_of_yojson : Lean.Json → Except Error entrypoint
  | .arr #[.str "Ingress"] => pure .Ingress
  | .arr #[.str "Egress"] => pure .Egress
  | _ => throw .decode

/-- Mirrors `t`: a scheduled packet. -/
structure t where
  /-- The evaluation context. -/
  value_ctx : value
  /-- The packet input. -/
  packet_in : Core.Object.PacketIn.t
  /-- Which block the packet begins processing at, after the parser and verify blocks. -/
  entrypoint : entrypoint

/-- Mirrors `to_yojson`. -/
def to_yojson (p : t) : Lean.Json := Lean.Json.mkObj
  [("value_ctx", Lang.Il.Encode.value p.value_ctx),
   ("packet_in", Core.Object.PacketIn.to_yojson p.packet_in),
   ("entrypoint", entrypoint_to_yojson p.entrypoint)]

/-- Mirrors `of_yojson`. -/
def of_yojson (json : Lean.Json) : Except Error t := do
  pure { value_ctx := ← (Lang.Il.Json.value (← fieldOf json "value_ctx")).mapError fun _ => .decode,
         packet_in := ← Core.Object.PacketIn.of_yojson (← fieldOf json "packet_in"),
         entrypoint := ← entrypoint_of_yojson (← fieldOf json "entrypoint") }

end P4SpecTec.BackendSim.V1Model.Packet
