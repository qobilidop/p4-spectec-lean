import P4SpecTec.BackendSim.Core.Object
import P4SpecTec.BackendSim.Core.Func
import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTec.Runtime.Sim.Io

/-!
Partial dynamic port of `p4spec/lib/backend-sim/nano_switch/pipe.ml`:
PacketIn extract, initialization, packet driver and the extern dispatch boundary. Receiver
results remain raw objectState ExternV, exactly as at the pin, not repaired
PACKET values. This is not a generated typed NanoP4Spec.Externs instance.

Boot, STF handling, static_assert and other architecture interfaces are not ported.
The verify dispatch preserves upstream's full-P4 lookup ABI; the pinned Nano
grammar/AL has no extern-function path that can successfully invoke it.
Callbacks are explicit StateEval computations; their caller
owns interpreter fuel/configuration. This module introduces no hidden fuel,
resets, mutable trampoline or repeated evaluation of callback outcomes.
-/

namespace P4SpecTec.BackendSim.NanoSwitch.Pipe

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude
open P4SpecTec.Util.Source

/-- Mirrors the sole pinned Nano extern object variant. -/
inductive «extern» where
  /-- Input packet state. -/
  | PacketIn (pkt : Core.Object.PacketIn.t)
  deriving BEq, Repr

/-- Explicit substitute for the pinned mutable Spec.Func.call trampoline. -/
abbrev Call := SpecImpl.Func.Call

/-- Construct a named type note without inventing runtime state. -/
def varT (name : String) : typ' := .VarT (mkPhrase name) []

/-- Mirrors the variant's derived JSON representation. -/
def extern_to_yojson : «extern» → Lean.Json
  | .PacketIn pkt => .arr #[.str "PacketIn", Core.Object.PacketIn.to_yojson pkt]

/-- Checked counterpart of the variant decoder followed by Result.get_ok. -/
def extern_of_yojson (json : Lean.Json) : Except Core.Object.Error «extern» := do
  let .arr #[.str "PacketIn", packet] := json | throw .decode
  pure (.PacketIn (← Core.Object.PacketIn.of_yojson packet))

/-- Target-local malformed values are hard errors, never retryable mismatches. -/
def checked (result : Except ε α) : StateEval α :=
  match result with | .ok x => pure x | .error _ => throw .err

/-- Require a runtime value shape, matching upstream's raising Get accessors. -/
def required (result : Option α) : StateEval α :=
  match result with | some x => pure x | none => throw .err

/-- The initialized architecture state is the JSON representation of unit. -/
def init_arch_state : value := Value.Make.extern (varT "archState") .null

/-- Nano extern initialization validates arity then returns the pinned null object state. -/
def eval_extern_init (values_input : List value) : StateEval value := do
  let [_, _, _] := values_input | throw .err
  pure (Value.Make.extern (varT "objectState") .null)

/-- Dynamic function dispatch, preserving upstream getter order and verify's callback ABI. -/
def eval_extern_func_call (call : Call) (values_input : List value) :
    StateEval (List value) := do
  let [value_ctx, value_arch, value_name_func, value_names_param] := values_input
    | throw .err
  let name_func ← required (Value.Get.text value_name_func)
  let names_param ← required (Value.Get.list value_names_param)
  let names_param ← names_param.mapM fun v => required (Value.Get.text v)
  unless name_func == ByteText.ofString "verify" &&
      names_param == [ByteText.ofString "check", ByteText.ofString "toSignal"] do throw .err
  let (value_ctx, value_arch, value_callResult) ← Core.Func.verify call value_ctx value_arch
  pure [value_ctx, value_arch, value_callResult]

/-- Dynamic extract, preserving callback order, all callback outcomes and raw result shape. -/
def eval_extern_method_call (call : Call) (values_input : List value) :
    StateEval (List value) := do
  let [value_ctx, value_extern, value_name_method, value_names_param] := values_input
    | throw .err
  let .CaseV (.Seq [.Atom packet, .Arg _, .Arg state]) := value_extern.it | throw .err
  unless packet.it == .Keyword "PACKET" do throw .err
  let json ← required (Value.Get.extern state)
  let .PacketIn pkt ← checked (extern_of_yojson json)
  let name_method ← required (Value.Get.text value_name_method)
  let names_param ← required (Value.Get.list value_names_param)
  let names_param ← names_param.mapM fun v => required (Value.Get.text v)
  unless name_method == ByteText.ofString "extract" &&
      names_param == [ByteText.ofString "hdr"] do throw .err
  let (pkt, value_ctx) ← if Core.Object.hostAdd pkt.idx 24 > pkt.len then
      pure (pkt, value_ctx)
    else do
      let (pkt, bits) ← checked (Core.Object.PacketIn.parse pkt 24)
      let value_scope_local := Value.Make.case (varT "scope")
        (.Atom (mkPhrase (.Keyword "LOCAL")))
      let hdr := Value.Make.text (ByteText.ofString "hdr")
      let value_hdr ← call "find_var_e" [] [value_scope_local, value_ctx, hdr]
      let typ_bits : typ' := .IterT (mkPhrase (varT "bit")) .List
      let value_bits := Value.Make.list typ_bits (bits.toList.map Value.Make.bool)
      let value_hdr' ← call "write_value_from_bits" [] [value_hdr, value_bits]
      let value_ctx ← call "update_var_e" [] [value_scope_local, value_ctx, hdr, value_hdr']
      pure (pkt, value_ctx)
  let value_extern := Value.Make.extern (varT "objectState") (extern_to_yojson (.PacketIn pkt))
  pure [value_extern, value_ctx]

/-- Explicit substitute for the pinned mutable Spec.Rel.call trampoline. -/
abbrev RelCall := String → List value → StateEval (List value)

/-- Mirrors drive_pipe, including optional FORWARD matching and byte-preserving output.
The caller supplies the relation evaluator and its fuel/configuration. Unsupported
host integers, invalid hex and wrong relation arity are hard errors; relation
failures retain their post-state. Malformed decisions drop, as upstream's |>>? does. -/
def drive_pipe (call : RelCall) (value_ctx value_arch : value) (rx : Runtime.Sim.Io.rx) :
    StateEval (value × value × List Runtime.Sim.Io.tx) := do
  let (port_in, packet_bytes) := rx
  unless Core.Object.hostInt port_in do throw .err
  let packet_in := «extern».PacketIn (← checked (Core.Object.PacketIn.init packet_bytes))
  let value_packet_in_state := Value.Make.extern (varT "objectState") (extern_to_yojson packet_in)
  let [value_forwarding_decision, value_ctx] ←
    call "NanoSwitch_drive" [value_ctx, value_packet_in_state] | throw .err
  let forward := match value_forwarding_decision.it with
    | .CaseV decision => Domain.Mixfix.eq_mixop decision
      (.Atom (mkPhrase (.Keyword "FORWARD")) : Domain.Mixfix.t Unit)
    | _ => false
  pure (value_ctx, value_arch, if forward then [(port_in, packet_bytes)] else [])

/-- Bounded dynamic extern interface; unported functions are explicit hard errors.
Verify is a direct dynamic API, not a claim of Nano source-level reachability. -/
def externInterface (call : Call) : Interp_al.Interp.Extern StateEval where
  eval_extern_rel := fun name args =>
    if name == "ExternFunctionCall_eval" then eval_extern_func_call call args
    else if name == "ExternMethodCall_eval" then eval_extern_method_call call args
    else throw .err
  eval_extern_func := fun name _ args =>
    if name == "init_objectState" then eval_extern_init args
    else if name == "init_archState" then pure init_arch_state
    else throw .err

end P4SpecTec.BackendSim.NanoSwitch.Pipe
