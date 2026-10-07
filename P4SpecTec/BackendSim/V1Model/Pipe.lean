import P4SpecTec.BackendSim.V1Model.Func
import P4SpecTec.BackendSim.V1Model.Object
import P4SpecTec.BackendSim.Core.Func
import P4SpecTec.BackendSim.State
import P4SpecTec.Interp.InterpAl.Interp

/-!
Port of `p4spec/lib/backend-sim/v1model/pipe.ml`: the v1model simulator's extern
dispatch, control-plane interfaces and packet pipeline, over the explicit spec trampolines
(`Make.Spec`) and the driver state monad (`BackendSim.State`). Every operation is generic
in the effect carrier: `StateEval` for full P4, whose fresh identifiers every spec callback
consumes. Upstream's `error` and failed getters are the hard error `Fail.err`; a failed
callback is a mismatch of the extern call, as upstream's registered trampolines make it
(`Make.call_func`, `Make.call_rel`).

The STF transformation (`transform_stf_stmt`) and the pipeline initializer that parses a
program file are in `BackendSim/Stf/`; `init_pipe` here takes the parsed program value.
-/

namespace P4SpecTec.BackendSim.V1Model.Pipe

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.Util.Source
open P4SpecTec.BackendSim P4SpecTec.BackendSim.SpecImpl P4SpecTec.BackendSim.State
open P4SpecTec.BackendSim.Core.Object (Error)

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Mirrors `init_arch_state`. -/
def init_arch_state : value := Arch.to_value Arch.empty

/-- Mirrors `object_state`: the v1model extern objects. -/
inductive object_state where
  /-- The input packet. -/
  | PacketIn (pkt : Core.Object.PacketIn.t)
  /-- The output packet. -/
  | PacketOut (pkt : Core.Object.PacketOut.t)
  /-- A counter array. -/
  | Counter (counter : Object.Counter.t)
  /-- A register array. -/
  | Register (reg : Object.Register.t)
  /-- A direct counter. -/
  | DirectCounter (counter : Object.DirectCounter.t)
  /-- A direct meter. -/
  | DirectMeter (meter : Object.DirectMeter.t)

/-- Mirrors `object_state_to_yojson`. -/
def object_state_to_yojson : object_state → Lean.Json
  | .PacketIn pkt => .arr #[.str "PacketIn", Core.Object.PacketIn.to_yojson pkt]
  | .PacketOut pkt => .arr #[.str "PacketOut", Lean.Json.mkObj
      [("bits", Core.Object.bits_to_yojson pkt.bits)]]
  | .Counter c => .arr #[.str "Counter", Object.Counter.to_yojson c]
  | .Register r => .arr #[.str "Register", Object.Register.to_yojson r]
  | .DirectCounter c => .arr #[.str "DirectCounter", Object.DirectCounter.to_yojson c]
  | .DirectMeter d => .arr #[.str "DirectMeter", Object.DirectMeter.to_yojson d]

/-- Mirrors `object_state_of_yojson`. -/
def object_state_of_yojson : Lean.Json → Except Error object_state
  | .arr #[.str "PacketIn", j] => .PacketIn <$> Core.Object.PacketIn.of_yojson j
  | .arr #[.str "PacketOut", j] => do
    let fields ← j.getObj?.mapError fun _ => .decode
    if fields.toList.length != 1 then throw .decode
    pure (.PacketOut { bits := ← Core.Object.bits_of_yojson (← Packet.fieldOf j "bits") })
  | .arr #[.str "Counter", j] => .Counter <$> Object.Counter.of_yojson j
  | .arr #[.str "Register", j] => .Register <$> Object.Register.of_yojson j
  | .arr #[.str "DirectCounter", j] => .DirectCounter <$> Object.DirectCounter.of_yojson j
  | .arr #[.str "DirectMeter", j] => .DirectMeter <$> Object.DirectMeter.of_yojson j
  | _ => throw .decode

/-- An object state as the `objectState` extern value. -/
def objectValue (obj : object_state) : value := Pack.objectState (object_state_to_yojson obj)

/-- Mirrors `get_object_state`: the extern payload of an object, decoded. -/
def get_object_state (spec : Make.Spec m) (value_arch value_objectId : value) :
    m object_state := do
  let json ← Func.required (Value.Get.extern
    (← Func.find_objectState_e spec.func value_arch value_objectId))
  Core.Object.Spec.checked (object_state_of_yojson json)

/-- The identifier of the `packet_in` object. -/
def packet_in_id : value := Pack.objectIdOf ["packet_in"]

/-- The identifier of the `packet_out` object. -/
def packet_out_id : value := Pack.objectIdOf ["packet_out"]

/-- Mirrors `get_packet_in`. -/
def get_packet_in (spec : Make.Spec m) (value_arch : value) : m Core.Object.PacketIn.t := do
  match ← get_object_state spec value_arch packet_in_id with
  | .PacketIn packet_in => pure packet_in
  | _ => throw .err

/-- Mirrors `get_packet_out`. -/
def get_packet_out (spec : Make.Spec m) (value_arch : value) : m Core.Object.PacketOut.t := do
  match ← get_object_state spec value_arch packet_out_id with
  | .PacketOut packet_out => pure packet_out
  | _ => throw .err

/-- Mirrors `get_arch_state` on an architecture value. -/
def arch_state (spec : Make.Spec m) (value_arch : value) : m Arch.t := do
  Core.Object.Spec.checked (Arch.of_value (← Func.find_archState_e spec.func value_arch))

/-- Mirrors `put_arch_state` on an architecture value. -/
def put_arch (spec : Make.Spec m) (value_arch : value) (a : Arch.t) : m value :=
  Func.update_archState_e spec.func value_arch (Arch.to_value a)

/-! ## Extern calls -/

/-- Mirrors `texts`: `Value.Get.list |> List.map Value.Get.text`. -/
def texts (v : value) : Option (List ByteText) := do (← Value.Get.list v).mapM Value.Get.text

/-- Whether the parameter names are the given ones. -/
def named (names_param : List ByteText) (expected : List String) : Bool :=
  names_param == expected.map ByteText.ofString

/-- Mirrors `eval_extern_init`: a counter, register, direct counter or direct meter is
constructed; any other extern starts with a null state. -/
def eval_extern_init (spec : Make.Spec m) (values_input : List value) : m value := do
  let [value_name, value_type_args, value_ids, value_args] := values_input | throw .err
  let name_extern ← Func.required (Value.Get.text value_name)
  if name_extern == ByteText.ofString "counter" then
    pure (objectValue (.Counter (← Object.Counter.init value_type_args value_ids value_args)))
  else if name_extern == ByteText.ofString "register" then
    pure (objectValue (.Register
      (← Object.Register.init spec value_type_args value_ids value_args)))
  else if name_extern == ByteText.ofString "direct_counter" then
    pure (objectValue (.DirectCounter
      (← Object.DirectCounter.init value_type_args value_ids value_args)))
  else if name_extern == ByteText.ofString "direct_meter" then
    pure (objectValue
      (.DirectMeter (← Object.DirectMeter.init value_type_args value_ids value_args)))
  else pure (Pack.objectState .null)

/-- Mirrors `eval_extern_func_lctk_call`: `static_assert` at compile time. -/
def eval_extern_func_lctk_call (spec : Make.Spec m) (values_input : List value) :
    m (List value) := do
  let [value_ctx, value_name_func, value_names_param] := values_input | throw .err
  let name_func ← Func.required (Value.Get.text value_name_func)
  let names_param ← Func.required (texts value_names_param)
  unless name_func == ByteText.ofString "static_assert" do throw .err
  if named names_param ["check", "message"] then
    pure [← Core.Func.static_assert spec.func true value_ctx]
  else if named names_param ["check"] then
    pure [← Core.Func.static_assert spec.func false value_ctx]
  else throw .err

/-- Mirrors `eval_extern_func_call`: dispatch on the function name and parameter names. -/
def eval_extern_func_call (spec : Make.Spec m) (values_input : List value) : m (List value) := do
  let [value_ctx, value_arch, value_name_func, value_names_param] := values_input | throw .err
  let name_func ← Func.required (Value.Get.text value_name_func)
  let names_param ← Func.required (texts value_names_param)
  let is := fun (name : String) (params : List String) =>
    name_func == ByteText.ofString name && named names_param params
  let checksum := ["condition", "data", "checksum", "algo"]
  let (value_ctx, value_arch, value_callResult) ←
    if is "verify" ["check", "toSignal"] then Core.Func.verify spec.func value_ctx value_arch
    else if is "digest" ["receiver", "data"] then Func.digest value_ctx value_arch
    else if is "mark_to_drop" ["standard_metadata"] then Func.mark_to_drop spec value_ctx value_arch
    else if is "verify_checksum" checksum then Func.verify_checksum spec value_ctx value_arch
    else if is "verify_checksum_with_payload" checksum then
      Func.verify_checksum_with_payload spec value_ctx value_arch (← get_packet_in spec value_arch)
    else if is "update_checksum" checksum then Func.update_checksum spec value_ctx value_arch
    else if is "update_checksum_with_payload" checksum then
      Func.update_checksum_with_payload spec value_ctx value_arch (← get_packet_in spec value_arch)
    else if is "clone_preserving_field_list" ["type", "session", "index"] then
      Func.clone_preserving_field_list spec value_ctx value_arch
    else if is "resubmit_preserving_field_list" ["index"] then
      Func.resubmit_preserving_field_list spec value_ctx value_arch
    else if is "recirculate_preserving_field_list" ["index"] then
      Func.recirculate_preserving_field_list spec value_ctx value_arch
    else if is "hash" ["result", "algo", "base", "data", "max"] then
      Func.hash spec value_ctx value_arch
    else if is "log_msg" ["msg"] then Func.log_msg spec value_ctx value_arch
    else if is "log_msg" ["msg", "data"] then Func.log_msg_format spec value_ctx value_arch
    else throw .err
  pure [value_ctx, value_arch, value_callResult]

/-- Mirrors `eval_extern_method_call`: dispatch on the object, method and parameters, then
write the object back. -/
def eval_extern_method_call (spec : Make.Spec m) (values_input : List value) :
    m (List value) := do
  let [value_ctx, value_arch, value_objectId, value_name_method, value_names_param] :=
    values_input | throw .err
  let obj ← get_object_state spec value_arch value_objectId
  let name_method ← Func.required (Value.Get.text value_name_method)
  let names_param ← Func.required (texts value_names_param)
  let is := fun (name : String) (params : List String) =>
    name_method == ByteText.ofString name && named names_param params
  let (obj, value_ctx, value_arch, value_callResult) ← match obj with
    | .PacketIn packet_in =>
      let wrap := fun (r : Core.Object.Spec.Outcome Core.Object.PacketIn.t) =>
        (object_state.PacketIn r.1, r.2)
      if is "extract" ["hdr"] then
        wrap <$> Core.Object.Spec.extract spec value_ctx value_arch packet_in
      else if is "extract" ["variableSizeHeader", "variableFieldSizeInBits"] then
        wrap <$> Core.Object.Spec.extract_varsize spec value_ctx value_arch packet_in
      else if is "lookahead" [] then
        wrap <$> Core.Object.Spec.lookahead spec value_ctx value_arch packet_in
      else if is "advance" ["sizeInBits"] then
        wrap <$> Core.Object.Spec.advance spec value_ctx value_arch packet_in
      else if is "length" [] then
        wrap <$> Core.Object.Spec.length value_ctx value_arch packet_in
      else throw .err
    | .PacketOut packet_out =>
      if is "emit" ["hdr"] then
        (fun (r : Core.Object.Spec.Outcome Core.Object.PacketOut.t) =>
          (object_state.PacketOut r.1, r.2)) <$>
          Core.Object.Spec.emit spec value_ctx value_arch packet_out
      else throw .err
    | .Counter counter =>
      if is "count" ["index"] then
        let packet_in ← get_packet_in spec value_arch
        (fun (r : Object.Outcome Object.Counter.t) => (object_state.Counter r.1, r.2)) <$>
          Object.Counter.count spec value_ctx value_arch packet_in counter
      else throw .err
    | .Register reg =>
      let wrap := fun (r : Object.Outcome Object.Register.t) => (object_state.Register r.1, r.2)
      if is "read" ["result", "index"] then
        wrap <$> Object.Register.read spec value_ctx value_arch reg
      else if is "write" ["index", "value"] then
        wrap <$> Object.Register.write spec value_ctx value_arch reg
      else throw .err
    | .DirectCounter counter =>
      if is "count" [] then
        let packet_in ← get_packet_in spec value_arch
        (fun (r : Object.Outcome Object.DirectCounter.t) =>
          (object_state.DirectCounter r.1, r.2)) <$>
          Object.DirectCounter.count value_ctx value_arch packet_in counter
      else throw .err
    | .DirectMeter meter =>
      if is "read" ["result"] then
        let packet_in ← get_packet_in spec value_arch
        (fun (r : Object.Outcome Object.DirectMeter.t) =>
          (object_state.DirectMeter r.1, r.2)) <$>
          Object.DirectMeter.read spec value_ctx value_arch packet_in meter
      else throw .err
  let value_arch ← Func.update_objectState_e spec.func value_arch value_objectId (objectValue obj)
  pure [value_ctx, value_arch, value_callResult]

/-! ## Mirror, multicast and register interfaces -/

/-- Mirrors `add_mirror_session`. -/
def add_mirror_session (spec : Make.Spec m) (value_arch : value) (session port : Int) : m value :=
  do put_arch spec value_arch (Arch.with_mirrortable
    (Mirror.Table.add session port (← arch_state spec value_arch).mirrortable)
    (← arch_state spec value_arch))

/-- Mirrors `mc_mgrp_create`. -/
def mc_mgrp_create (spec : Make.Spec m) (value_arch : value) (mgid : Int) : m value := do
  let a ← arch_state spec value_arch
  put_arch spec value_arch (Arch.with_multicast (Multicast.State.group_create mgid a.multicast) a)

/-- Mirrors `mc_node_create`. -/
def mc_node_create (spec : Make.Spec m) (value_arch : value) (rid : Int) (ports : List Int) :
    m value := do
  let a ← arch_state spec value_arch
  put_arch spec value_arch (Arch.with_multicast
    (Multicast.State.node_create rid ports a.multicast) a)

/-- Mirrors `mc_node_associate`. -/
def mc_node_associate (spec : Make.Spec m) (value_arch : value) (mgid handle : Int) :
    m value := do
  let a ← arch_state spec value_arch
  put_arch spec value_arch (Arch.with_multicast
    (Multicast.State.node_associate mgid handle a.multicast) a)

/-! ## Packet state, in the driver monad -/

/-- The driver monad over the carrier. -/
abbrev Driver (α : Type) := State m α

/-- Mirrors `get_arch_state`. -/
def get_arch_state (spec : Make.Spec m) : Driver (m := m) Arch.t := do
  let (_, value_arch, _) ← State.get
  State.lift (arch_state spec value_arch)

/-- Mirrors `put_arch_state`. -/
def put_arch_state (spec : Make.Spec m) (a : Arch.t) : Driver (m := m) Unit := do
  let (value_ctx, value_arch, txs) ← State.get
  let value_arch ← State.lift (put_arch spec value_arch a)
  State.put (value_ctx, value_arch, txs)

/-- Write an object's state into the architecture, in the driver. -/
def set_object (spec : Make.Spec m) (value_objectId : value) (obj : object_state) :
    Driver (m := m) Unit := do
  let (value_ctx, value_arch, txs) ← State.get
  let value_arch ← State.lift (Func.update_objectState_e spec.func value_arch value_objectId
    (objectValue obj))
  State.put (value_ctx, value_arch, txs)

/-- Mirrors `insert_packet`: the scheduled packet's input and context become current. -/
def insert_packet (spec : Make.Spec m) (packet : Packet.t) : Driver (m := m) Unit := do
  State.modify fun (_, value_arch, txs) => (packet.value_ctx, value_arch, txs)
  set_object spec packet_in_id (.PacketIn packet.packet_in)

/-- Mirrors `remove_packet_in`: rewind the input packet. -/
def remove_packet_in (spec : Make.Spec m) : Driver (m := m) Unit := do
  let (_, value_arch, _) ← State.get
  let packet_in ← State.lift (get_packet_in spec value_arch)
  set_object spec packet_in_id (.PacketIn (Core.Object.PacketIn.reset packet_in))

/-- Mirrors `remove_packet_out`: an empty output packet. -/
def remove_packet_out (spec : Make.Spec m) : Driver (m := m) Unit :=
  set_object spec packet_out_id (.PacketOut Core.Object.PacketOut.init)

/-- Read a field of `standard_metadata` as a fixed-width bit string. -/
def standard_metadata (spec : Make.Spec m) (field : String) : Driver (m := m) (Int × Int) := do
  let (value_ctx, value_arch, _) ← State.get
  State.lift do
    let v ← Rel.lvalue_read_dot_global spec.rel value_ctx value_arch
      (ByteText.ofString "standard_metadata") (ByteText.ofString field)
    Func.required (Unpack.unpack_p4_fixedBit v)

/-- Write a field of `standard_metadata`. -/
def write_standard_metadata (spec : Make.Spec m) (field : String) (v : value) :
    Driver (m := m) Unit := do
  let (value_ctx, value_arch, txs) ← State.get
  let value_ctx ← State.lift (Rel.lvalue_write_dot_global spec.rel value_ctx value_arch
    (ByteText.ofString "standard_metadata") (ByteText.ofString field) v)
  State.put (value_ctx, value_arch, txs)

/-- Mirrors `is_dropped`: `egress_spec` is the nine-bit 511. -/
def is_dropped (spec : Make.Spec m) : Driver (m := m) Bool := do
  let (width, n) ← standard_metadata spec "egress_spec"
  pure (width == 9 && n == 511)

/-- Mirrors `get_mcast_grp`. -/
def get_mcast_grp (spec : Make.Spec m) : Driver (m := m) Int := do
  pure (← standard_metadata spec "mcast_grp").2

/-! ## Pipeline initializer and driver -/

/-- Mirrors `init_pipe` after upstream parsing (`Spec.Pgm.v1model_init`), with `call_pgm`'s
result handling from `make.ml`: `V1Model_init` on the parsed program value; one output is
the context with the initial architecture state, two are the context and architecture. -/
def init_pipe (call : Rel.RelCall m) (value_program : value) : m (value × value) := do
  match ← call "V1Model_init" [value_program] with
  | [value_ctx] => pure (value_ctx, init_arch_state)
  | [value_ctx, value_arch] => pure (value_ctx, value_arch)
  | _ => throw .err

/-- Mirrors `setup_rx`: the packet objects and the globals for a received packet. -/
def setup_rx (spec : Make.Spec m) (rx : Runtime.Sim.Io.rx) : Driver (m := m) Unit := do
  let (port_in, packet_in) := rx
  let packet_in ← State.lift (Core.Object.Spec.checked (Core.Object.PacketIn.init packet_in))
  let value_packet_in_state := objectValue (.PacketIn packet_in)
  let (value_ctx, value_arch, _) ← State.get
  let (value_ctx, value_arch) ← State.lift
    (Rel.v1model_init_packet_in spec.rel value_ctx value_arch value_packet_in_state)
  let value_packet_out_state := objectValue (.PacketOut Core.Object.PacketOut.init)
  let (value_ctx, value_arch) ← State.lift
    (Rel.v1model_init_packet_out spec.rel value_ctx value_arch value_packet_out_state)
  let value_ctx ← State.lift (Rel.v1model_init_globals spec.rel value_ctx value_arch port_in)
  State.modify fun (_, _, txs) => (value_ctx, value_arch, txs)

/-- Mirrors `drive_p`: the parser; a rejection writes `parser_error`. -/
def drive_p (spec : Make.Spec m) : Driver (m := m) Unit := do
  let value_parser_result ← State.apply (Rel.v1model_parser spec.rel)
  match value_parser_result.it with
  | .CaseV (.Seq [.Atom reject, .Arg value_error]) =>
    if reject.it == .Keyword "REJECT" then
      write_standard_metadata spec "parser_error" value_error
  | _ => pure ()

/-- Mirrors `drive_vr`. -/
def drive_vr (spec : Make.Spec m) : Driver (m := m) value :=
  State.apply (Rel.v1model_verify spec.rel)

/-- Mirrors `drive_pipe_pre`: reset the requests, rewind the input, parse, verify. -/
def drive_pipe_pre (spec : Make.Spec m) : Driver (m := m) value := do
  let a ← get_arch_state spec
  put_arch_state spec (Arch.reset a)
  remove_packet_in spec
  drive_p spec
  drive_vr spec

/-- Mirrors `drive_ck`. -/
def drive_ck (spec : Make.Spec m) : Driver (m := m) value :=
  State.apply (Rel.v1model_check spec.rel)

/-- Mirrors `drive_dep`. -/
def drive_dep (spec : Make.Spec m) : Driver (m := m) value :=
  State.apply (Rel.v1model_deparse spec.rel)

/-- The output packet bytes: the emitted bits followed by the input's payload. -/
def output_packet (spec : Make.Spec m) (value_arch : value) : m ByteText := do
  let packet_in ← get_packet_in spec value_arch
  let packet_out ← get_packet_out spec value_arch
  Core.Object.Spec.checked (Core.Object.Spec.packet packet_in packet_out)

/-- Mirrors `drive_pipe_post`: checksum, deparse, and transmit to `egress_spec`. -/
def drive_pipe_post (spec : Make.Spec m) : Driver (m := m) value := do
  let _ ← drive_ck spec
  remove_packet_out spec
  let result ← drive_dep spec
  let (_, port) ← standard_metadata spec "egress_spec"
  let (_, value_arch, _) ← State.get
  let packet ← State.lift (output_packet spec value_arch)
  State.modify fun (value_ctx, value_arch, txs) => (value_ctx, value_arch, (port, packet) :: txs)
  pure result

/-- Set `instance_type`. -/
def set_instance_type (spec : Make.Spec m) (n : Int) : Driver (m := m) Unit :=
  write_standard_metadata spec "instance_type" (Pack.pack_p4_fixedBit 32 n)

/-- Mirrors `prepare_resubmit_ctx`. -/
def prepare_resubmit_ctx (spec : Make.Spec m) (index : Int) : Driver (m := m) Unit := do
  let (value_ctx, value_arch, txs) ← State.get
  let value_ctx ← State.lift (Rel.v1model_setup_preserved_meta_fields spec.rel value_ctx value_arch
    (Packet.ResubmitInfo.to_value index))
  State.put (value_ctx, value_arch, txs)
  set_instance_type spec 6

/-- Mirrors `prepare_clone_ctx`. -/
def prepare_clone_ctx (spec : Make.Spec m) (clone_type : Packet.CloneInfo.clone_type)
    (port index : Int) : Driver (m := m) Unit := do
  let (value_ctx, value_arch, txs) ← State.get
  let value_ctx ← State.lift (Rel.v1model_setup_preserved_meta_fields spec.rel value_ctx value_arch
    (Pack.pack_p4_fixedBit 8 index))
  State.put (value_ctx, value_arch, txs)
  set_instance_type spec (match clone_type with | .I2E => 1 | .E2E => 2)
  write_standard_metadata spec "egress_spec" (Pack.pack_p4_fixedBit 9 port)

/-- Mirrors `prepare_recirculate_ctx`. -/
def prepare_recirculate_ctx (spec : Make.Spec m) (index : Int) : Driver (m := m) Unit := do
  let (value_ctx, value_arch, txs) ← State.get
  let value_ctx ← State.lift (Rel.v1model_setup_preserved_meta_fields spec.rel value_ctx value_arch
    (Packet.RecirculateInfo.to_value index))
  State.put (value_ctx, value_arch, txs)
  set_instance_type spec 4

/-- Mirrors `prepare_multicast_ctx`. -/
def prepare_multicast_ctx (spec : Make.Spec m) (rid port : Int) : Driver (m := m) Unit := do
  write_standard_metadata spec "egress_rid" (Pack.pack_p4_fixedBit 16 rid)
  write_standard_metadata spec "egress_spec" (Pack.pack_p4_fixedBit 9 port)
  set_instance_type spec 5

/-- Mirrors `schedule_packet`: queue the current packet at the given entry point, ingress
at the front and egress at the back. -/
def schedule_packet (spec : Make.Spec m) (entrypoint : Packet.entrypoint) :
    Driver (m := m) Unit := do
  let (value_ctx, value_arch, _) ← State.get
  let packet_in ← State.lift (get_packet_in spec value_arch)
  let packet : Packet.t := { value_ctx, packet_in, entrypoint }
  let a ← get_arch_state spec
  let queue := match entrypoint with
    | .Ingress => Scheduler.push_front packet a.queue
    | .Egress => Scheduler.push_back packet a.queue
  put_arch_state spec (Arch.with_queue queue a)

/-- Restore the original context, keeping the architecture and transmissions. -/
def restore_ctx (value_ctx_original : value) : Driver (m := m) Unit :=
  State.modify fun (_, value_arch, txs) => (value_ctx_original, value_arch, txs)

/-- Mirrors `schedule_resubmit`. -/
def schedule_resubmit (spec : Make.Spec m) (a : Arch.t) : Driver (m := m) Bool := do
  match a.action.resubmit_opt with
  | none => pure false
  | some field_index =>
    let (value_ctx_original, _, _) ← State.get
    prepare_resubmit_ctx spec field_index
    let _ ← drive_pipe_pre spec
    schedule_packet spec .Ingress
    restore_ctx value_ctx_original
    pure true

/-- Mirrors `schedule_clone`. -/
def schedule_clone (spec : Make.Spec m) (a : Arch.t) : Driver (m := m) Bool := do
  match a.action.clone_opt with
  | none => pure false
  | some (clone_type, session, field_index) =>
    match Mirror.Table.find_opt session a.mirrortable with
    | some port =>
      let (value_ctx_original, _, _) ← State.get
      prepare_clone_ctx spec clone_type port field_index
      match clone_type with
      | .I2E => let _ ← drive_pipe_pre spec
      | .E2E => pure ()
      schedule_packet spec .Egress
      restore_ctx value_ctx_original
      pure true
    | none => pure false

/-- Mirrors `schedule_recirculate`: deparse, feed the output back as the input, parse. -/
def schedule_recirculate (spec : Make.Spec m) (a : Arch.t) : Driver (m := m) Bool := do
  match a.action.recirculate_opt with
  | none => pure false
  | some field_index =>
    let (value_ctx_original, _, _) ← State.get
    prepare_recirculate_ctx spec field_index
    let _ ← drive_ck spec
    remove_packet_out spec
    let _ ← drive_dep spec
    let (_, value_arch, _) ← State.get
    let packet ← State.lift (output_packet spec value_arch)
    let packet_in ← State.lift (Core.Object.Spec.checked (Core.Object.PacketIn.init packet))
    set_object spec packet_in_id (.PacketIn packet_in)
    let _ ← drive_pipe_pre spec
    schedule_packet spec .Ingress
    restore_ctx value_ctx_original
    pure true

/-- Mirrors `schedule_multicast`: one egress packet per node of the group. -/
def schedule_multicast (spec : Make.Spec m) (a : Arch.t) (mcast_grp : Int) :
    Driver (m := m) Bool := do
  match Multicast.IntMap.find_opt mcast_grp a.multicast.groups with
  | some group =>
    let nodes := (group.node_handles.filterMap fun handle =>
      Multicast.IntMap.find_opt handle a.multicast.nodes).flatten
    for node in nodes do
      prepare_multicast_ctx spec node.rid node.port
      schedule_packet spec .Egress
    pure true
  | none => pure false

/-- Mirrors `drive_ig`: ingress, then clone, resubmit, multicast, drop or egress. -/
def drive_ig (spec : Make.Spec m) : Driver (m := m) value := do
  let result ← State.apply (Rel.v1model_ingress spec.rel)
  let a ← get_arch_state spec
  let _ ← schedule_clone spec a
  let resubmitted ← schedule_resubmit spec a
  if resubmitted then pure result
  else
    let mcast_grp ← get_mcast_grp spec
    if mcast_grp != 0 then
      let _ ← schedule_multicast spec a mcast_grp
      pure result
    else
      let drop ← is_dropped spec
      if drop then pure result
      else
        schedule_packet spec .Egress
        pure result

/-- Mirrors `prepare_egress_ctx`: `egress_port` from `egress_spec`. -/
def prepare_egress_ctx (spec : Make.Spec m) : Driver (m := m) Unit := do
  let (value_ctx, value_arch, _) ← State.get
  let value_egress_spec ← State.lift (Rel.lvalue_read_dot_global spec.rel value_ctx value_arch
    (ByteText.ofString "standard_metadata") (ByteText.ofString "egress_spec"))
  write_standard_metadata spec "egress_port" value_egress_spec

/-- Mirrors `drive_eg`: egress, then clone, drop, recirculate. -/
def drive_eg (spec : Make.Spec m) : Driver (m := m) value := do
  prepare_egress_ctx spec
  let result ← State.apply (Rel.v1model_egress spec.rel)
  let a ← get_arch_state spec
  let _ ← schedule_clone spec a
  let drop ← is_dropped spec
  State.guard (!drop)
  let a ← get_arch_state spec
  let recirculated ← schedule_recirculate spec a
  if recirculated then State.empty else pure result

/-- Mirrors `drive_packet`. -/
def drive_packet (spec : Make.Spec m) (packet : Packet.t) : Driver (m := m) Unit := do
  match packet.entrypoint with
  | .Ingress =>
    insert_packet spec packet
    let _ ← drive_ig spec
  | .Egress =>
    insert_packet spec packet
    State.on_result (drive_eg spec) (fun _ => do let _ ← drive_pipe_post spec) (fun _ => pure ())

instance {α : Type} : Inhabited (State m α) := ⟨State.empty⟩

/-- Mirrors `run_scheduler`: process queued packets until the queue is empty; a program
that recirculates forever does not terminate, as upstream does not. -/
partial def run_scheduler (spec : Make.Spec m) : Driver (m := m) Unit := do
  let a ← get_arch_state spec
  match Scheduler.pop_front_opt a.queue with
  | none => State.empty
  | some (packet, queue) =>
    put_arch_state spec (Arch.with_queue queue (Arch.reset a))
    drive_packet spec packet
    run_scheduler spec

/-- Mirrors `drive_pipe`: a received packet through the pipeline, with every transmission
in order. -/
def drive_pipe (spec : Make.Spec m) (value_ctx value_arch : value) (rx : Runtime.Sim.Io.rx) :
    m (value × value × List Runtime.Sim.Io.tx) := do
  let pipe : Driver (m := m) Unit := do
    setup_rx spec rx
    let _ ← drive_pipe_pre spec
    schedule_packet spec .Ingress
    run_scheduler spec
  let (_, (value_ctx, value_arch, txs)) ← State.run pipe (value_ctx, value_arch, [])
  pure (value_ctx, value_arch, txs.reverse)

/-! ## The extern interface -/

/-- The extern relations, given the registered trampolines. -/
def eval_extern_rel (spec : Make.Spec m) (name : String) (args : List value) :
    m (List value) :=
  if name == "ExternFunctionCall_eval_lctk" then eval_extern_func_lctk_call spec args
  else if name == "ExternFunctionCall_eval" then eval_extern_func_call spec args
  else if name == "ExternMethodCall_eval" then eval_extern_method_call spec args
  else throw .err

/-- The extern functions. -/
def eval_extern_func (spec : Make.Spec m) (name : String) (args : List value) : m value :=
  if name == "init_objectState" then eval_extern_init spec args
  else if name == "init_archState" then pure init_arch_state
  else throw .err

/-- The dynamic extern interface for the reference interpreter. An extern relation call
receives the interpreter's function evaluator at the remaining fuel and uses it; an extern
function call (object initialization, which reads a type's default through the spec)
receives nothing, as upstream's does not, and uses the registered trampolines. Both are
registered through the failure-collapsing wrappers. -/
def externInterface (spec : Make.Spec m) : Interp_al.Interp.Extern m where
  eval_extern_rel := fun call =>
    eval_extern_rel { func := Make.call_func call, rel := Make.call_rel spec.rel }
  eval_extern_func := fun name _ args =>
    eval_extern_func { func := Make.call_func spec.func, rel := Make.call_rel spec.rel } name args

end P4SpecTec.BackendSim.V1Model.Pipe
