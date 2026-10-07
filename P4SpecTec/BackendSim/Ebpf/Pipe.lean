import P4SpecTec.BackendSim.Ebpf.Object
import P4SpecTec.BackendSim.Core.Func
import P4SpecTec.BackendSim.Core.Object
import P4SpecTec.Interp.InterpAl.Interp

/-!
Port of `p4spec/lib/backend-sim/ebpf/pipe.ml`: the eBPF simulator's extern dispatch and
packet pipeline, over the explicit spec trampolines (`Make.Spec`). The architecture state
is the unit value; the pipeline parses, filters, and transmits the input packet unchanged
when the filter accepts it. The mirror, multicast and register interfaces are not
implemented upstream and are the hard error here. Every operation is generic in the effect
carrier, as the v1model port is; upstream's `error` and failed getters are `Fail.err`.

The STF transformation and the statement runner are in `Ebpf/Stf.lean`; `init_pipe` here
takes the parsed program value, as the v1model port's does.
-/

namespace P4SpecTec.BackendSim.Ebpf.Pipe

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.Util.Source
open P4SpecTec.BackendSim P4SpecTec.BackendSim.SpecImpl
open P4SpecTec.BackendSim.Core.Object (Error)

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Mirrors `init_arch_state`: the unit state, `null`. -/
def init_arch_state : value := Pack.archState .null

/-- Mirrors `extern`: the eBPF extern objects. -/
inductive object_state where
  /-- The input packet. -/
  | PacketIn (pkt : Core.Object.PacketIn.t)
  /-- A counter array. -/
  | CounterArray (counters : Object.CounterArray.t)

/-- Mirrors `extern_to_yojson`. -/
def object_state_to_yojson : object_state → Lean.Json
  | .PacketIn pkt => .arr #[.str "PacketIn", Core.Object.PacketIn.to_yojson pkt]
  | .CounterArray c => .arr #[.str "CounterArray", Object.CounterArray.to_yojson c]

/-- Mirrors `extern_of_yojson`. -/
def object_state_of_yojson : Lean.Json → Except Error object_state
  | .arr #[.str "PacketIn", j] => .PacketIn <$> Core.Object.PacketIn.of_yojson j
  | .arr #[.str "CounterArray", j] => .CounterArray <$> Object.CounterArray.of_yojson j
  | _ => throw .decode

/-- An object state as the `objectState` extern value. -/
def objectValue (obj : object_state) : value := Pack.objectState (object_state_to_yojson obj)

/-- Mirrors `get_extern`: the extern payload of an object, decoded. -/
def get_extern (spec : Make.Spec m) (value_arch value_oid : value) : m object_state := do
  let json ← Func.required (Value.Get.extern
    (← Func.find_objectState_e spec.func value_arch value_oid))
  Core.Object.Spec.checked (object_state_of_yojson json)

/-- The identifier of the `packet_in` object. -/
def packet_in_id : value := Pack.objectIdOf ["packet_in"]

/-! ## Extern calls -/

/-- Mirrors `Value.Get.list |> List.map Value.Get.text`. -/
def texts (v : value) : Option (List ByteText) := do (← Value.Get.list v).mapM Value.Get.text

/-- Whether the parameter names are the given ones. -/
def named (names_param : List ByteText) (expected : List String) : Bool :=
  names_param == expected.map ByteText.ofString

/-- Mirrors `eval_extern_init`: a counter array is constructed; any other extern starts
with a null state. -/
def eval_extern_init (values_input : List value) : m value := do
  let [value_name, value_type_args, value_ids, value_args] := values_input | throw .err
  let name_extern ← Func.required (Value.Get.text value_name)
  if name_extern == ByteText.ofString "CounterArray" then
    pure (objectValue (.CounterArray
      (← Object.CounterArray.init value_type_args value_ids value_args)))
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

/-- Mirrors `eval_extern_func_call`: `verify` is the only extern function. -/
def eval_extern_func_call (spec : Make.Spec m) (values_input : List value) : m (List value) := do
  let [value_ctx, value_arch, value_name_func, value_names_param] := values_input | throw .err
  let name_func ← Func.required (Value.Get.text value_name_func)
  let names_param ← Func.required (texts value_names_param)
  unless name_func == ByteText.ofString "verify" && named names_param ["check", "toSignal"] do
    throw .err
  let (value_ctx, value_arch, value_callResult) ← Core.Func.verify spec.func value_ctx value_arch
  pure [value_ctx, value_arch, value_callResult]

/-- Mirrors `eval_extern_method_call`: dispatch on the object, method and parameters, then
write the object back. -/
def eval_extern_method_call (spec : Make.Spec m) (values_input : List value) :
    m (List value) := do
  let [value_ctx, value_arch, value_objectId, value_name_method, value_names_param] :=
    values_input | throw .err
  let obj ← get_extern spec value_arch value_objectId
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
    | .CounterArray counters =>
      let wrap := fun (r : Object.Outcome Object.CounterArray.t) =>
        (object_state.CounterArray r.1, r.2)
      if is "increment" ["index"] then
        wrap <$> Object.CounterArray.increment spec value_ctx value_arch counters
      else if is "add" ["index", "value"] then
        wrap <$> Object.CounterArray.add spec value_ctx value_arch counters
      else throw .err
  let value_arch ← Func.update_objectState_e spec.func value_arch value_objectId (objectValue obj)
  pure [value_ctx, value_arch, value_callResult]

/-! ## Pipeline initializer and driver -/

/-- Mirrors `init_pipe` after upstream parsing (`Spec.Pgm.ebpf_init`), with `call_pgm`'s
result handling from `make.ml`: `EBPF_init` on the parsed program value. -/
def init_pipe (call : Rel.RelCall m) (value_program : value) : m (value × value) := do
  match ← call "EBPF_init" [value_program] with
  | [value_ctx] => pure (value_ctx, init_arch_state)
  | [value_ctx, value_arch] => pure (value_ctx, value_arch)
  | _ => throw .err

/-- Mirrors `setup_rx`: the input packet object and the globals for a received packet. -/
def setup_rx (spec : Make.Spec m) (value_ctx value_arch : value) (rx : Runtime.Sim.Io.rx) :
    m (value × value) := do
  let (_, packet_in) := rx
  let packet_in ← Core.Object.Spec.checked (Core.Object.PacketIn.init packet_in)
  let value_packet_in_state := objectValue (.PacketIn packet_in)
  let (value_ctx, value_arch) ←
    Rel.ebpf_init_packet_in spec.rel value_ctx value_arch value_packet_in_state
  let value_ctx ← Rel.ebpf_init_globals spec.rel value_ctx value_arch
  pure (value_ctx, value_arch)

/-- Mirrors `drive_prs`: the parser; a rejection drops the packet. -/
def drive_prs (spec : Make.Spec m) (value_ctx value_arch : value) : m (value × value × Bool) := do
  let (value_ctx, value_arch, value_parse_result) ← Rel.ebpf_parse spec.rel value_ctx value_arch
  let drop := match value_parse_result.it with
    | .CaseV (.Seq [.Atom reject, .Arg _]) => reject.it == .Keyword "REJECT"
    | _ => false
  pure (value_ctx, value_arch, drop)

/-- Mirrors `drive_filt`. -/
def drive_filt (spec : Make.Spec m) (value_ctx value_arch : value) : m (value × value × value) :=
  Rel.ebpf_filter spec.rel value_ctx value_arch

/-- Mirrors `drive_pipe`: parse, filter, and transmit the received packet unchanged when
the filter's `accept` holds. -/
def drive_pipe (spec : Make.Spec m) (value_ctx value_arch : value) (rx : Runtime.Sim.Io.rx) :
    m (value × value × List Runtime.Sim.Io.tx) := do
  let (value_ctx, value_arch) ← setup_rx spec value_ctx value_arch rx
  let (value_ctx, value_arch, drop) ← drive_prs spec value_ctx value_arch
  if drop then pure (value_ctx, value_arch, [])
  else
    let (value_ctx, value_arch, _) ← drive_filt spec value_ctx value_arch
    let value_accept ← Rel.lvalue_read_var_global spec.rel value_ctx value_arch
      (ByteText.ofString "accept")
    let accept ← Func.required (Unpack.unpack_p4_bool value_accept)
    pure (value_ctx, value_arch, if accept then [rx] else [])

/-! ## The extern interface -/

/-- The extern relations, given the registered trampolines. -/
def eval_extern_rel (spec : Make.Spec m) (name : String) (args : List value) :
    m (List value) :=
  if name == "ExternFunctionCall_eval_lctk" then eval_extern_func_lctk_call spec args
  else if name == "ExternFunctionCall_eval" then eval_extern_func_call spec args
  else if name == "ExternMethodCall_eval" then eval_extern_method_call spec args
  else throw .err

/-- The extern functions. -/
def eval_extern_func (name : String) (args : List value) : m value :=
  if name == "init_objectState" then eval_extern_init args
  else if name == "init_archState" then pure init_arch_state
  else throw .err

/-- The dynamic extern interface for the reference interpreter, as the v1model port's: an
extern relation call uses the interpreter's function evaluator at the remaining fuel. -/
def externInterface (spec : Make.Spec m) : Interp_al.Interp.Extern m where
  eval_extern_rel := fun call =>
    eval_extern_rel { func := Make.call_func call, rel := Make.call_rel spec.rel }
  eval_extern_func := fun name _ args => eval_extern_func name args

end P4SpecTec.BackendSim.Ebpf.Pipe
