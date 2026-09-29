import P4SpecTec.BackendSim.Core.Object
import P4SpecTec.BackendSim.Core.Func
import P4SpecTec.BackendSim.Make
import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTec.Runtime.Sim.Io
import Lean.Data.Json.Parser

/-!
Partial dynamic port of `p4spec/lib/backend-sim/nano_switch/pipe.ml`:
PacketIn extract, initialization, packet driver and the extern dispatch boundary. Receiver
results remain raw objectState ExternV, exactly as at the pin, not repaired
PACKET values. The typed generated `NanoP4Spec.Externs` instance is a separate module.

Boot, STF handling, static_assert and other architecture interfaces are not ported.
The verify dispatch preserves upstream's full-P4 lookup ABI; the pinned Nano
grammar/AL has no extern-function path that can successfully invoke it.
Every operation is generic in the effect carrier: the pure `Eval` for certification, or
`StateEval` when a fresh counter is observed. Callbacks are explicit computations; the
interpreter supplies its own function evaluator at the remaining fuel, which
`externInterface` registers through `Make.call_func`, as upstream registers `call_func`.
This module introduces no hidden fuel, resets or repeated evaluation of callback outcomes.
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
abbrev Call (m : Type → Type) := SpecImpl.Func.Call m

/-- Construct a named type note without inventing runtime state. -/
def varT (name : String) : typ' := .VarT (mkPhrase name) []

/-- Mirrors the variant's derived JSON representation. -/
def extern_to_yojson : «extern» → Lean.Json
  | .PacketIn pkt => .arr #[.str "PacketIn", Core.Object.PacketIn.to_yojson pkt]

/-- Checked counterpart of the variant decoder followed by Result.get_ok. -/
def extern_of_yojson (json : Lean.Json) : Except Core.Object.Error «extern» := do
  let .arr #[.str "PacketIn", packet] := json | throw .decode
  pure (.PacketIn (← Core.Object.PacketIn.of_yojson packet))

/-- Decode an extern payload's canonical text. The port identifies extern payloads by their
compressed JSON text (runtime value equality, design section 5.3), so the target decodes that
text: payloads that equality identifies are indistinguishable to it. -/
def extern_of_text (text : String) : Except Core.Object.Error «extern» := do
  extern_of_yojson (← (Lean.Json.parse text).mapError fun _ => .decode)

/-- Decode an extern payload through its canonical compressed text. -/
def extern_of_payload (json : Lean.Json) : Except Core.Object.Error «extern» :=
  extern_of_text json.compress

/-- Mirrors `Value.Get.(value_extern |>> "PACKET typeId objectState" |> two |> snd |> extern)`;
a malformed receiver is `none`, where upstream's getters raise. -/
def packet_state (value_extern : value) : Option Lean.Json := do
  let .CaseV (.Seq [.Atom packet, .Arg _, .Arg state]) := value_extern.it | none
  unless packet.it == .Keyword "PACKET" do none
  Value.Get.extern state

/-- Mirrors `Value.Get.list |> List.map Value.Get.text`; a malformed list is `none`. -/
def texts (v : value) : Option (List ByteText) := do
  (← Value.Get.list v).mapM Value.Get.text

/-- The only pinned method: `extract` with the single parameter `hdr`. -/
def is_extract_hdr (name_method : ByteText) (names_param : List ByteText) : Bool :=
  name_method == ByteText.ofString "extract" && names_param == [ByteText.ofString "hdr"]

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Target-local malformed values are hard errors, never retryable mismatches. -/
def checked (result : Except ε α) : m α :=
  match result with | .ok x => pure x | .error _ => throw .err

/-- Require a runtime value shape, matching upstream's raising Get accessors. -/
def required (result : Option α) : m α :=
  match result with | some x => pure x | none => throw .err

/-- The initialized architecture state is the JSON representation of unit. -/
def init_arch_state : value := Value.Make.extern (varT "archState") .null

/-- Nano extern initialization validates arity then returns the pinned null object state. -/
def eval_extern_init (values_input : List value) : m value := do
  let [_, _, _] := values_input | throw .err
  pure (Value.Make.extern (varT "objectState") .null)

/-- Dynamic function dispatch, preserving upstream getter order and verify's callback ABI. -/
def eval_extern_func_call (call : Call m) (values_input : List value) :
    m (List value) := do
  let [value_ctx, value_arch, value_name_func, value_names_param] := values_input
    | throw .err
  let name_func ← required (Value.Get.text value_name_func)
  let names_param ← required (texts value_names_param)
  unless name_func == ByteText.ofString "verify" &&
      names_param == [ByteText.ofString "check", ByteText.ofString "toSignal"] do throw .err
  let (value_ctx, value_arch, value_callResult) ← Core.Func.verify call value_ctx value_arch
  pure [value_ctx, value_arch, value_callResult]

/-- The `PacketIn pkt, "extract", ["hdr"]` branch: a short packet and its context are
returned unchanged; otherwise the header bits are written through the trampoline. -/
def extract (call : Call m) (pkt : Core.Object.PacketIn.t) (value_ctx : value) :
    m (Core.Object.PacketIn.t × value) :=
  if Core.Object.hostAdd pkt.idx 24 > pkt.len then
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

/-- Dynamic extract, preserving callback order, all callback outcomes and raw result shape. -/
def eval_extern_method_call (call : Call m) (values_input : List value) :
    m (List value) := do
  let [value_ctx, value_extern, value_name_method, value_names_param] := values_input
    | throw .err
  let json ← required (packet_state value_extern)
  let .PacketIn pkt ← checked (extern_of_payload json)
  let name_method ← required (Value.Get.text value_name_method)
  let names_param ← required (texts value_names_param)
  unless is_extract_hdr name_method names_param do throw .err
  let (pkt, value_ctx) ← extract call pkt value_ctx
  let value_extern := Value.Make.extern (varT "objectState") (extern_to_yojson (.PacketIn pkt))
  pure [value_extern, value_ctx]

/-- Explicit substitute for the pinned mutable Spec.Rel.call trampoline. -/
abbrev RelCall (m : Type → Type) := String → List value → m (List value)

/-- Mirrors drive_pipe, including optional FORWARD matching and byte-preserving output.
The caller supplies the relation evaluator and its fuel/configuration. Unsupported
host integers, invalid hex and wrong relation arity are hard errors; relation
failures retain their post-state. Malformed decisions drop, as upstream's |>>? does. -/
def drive_pipe (call : RelCall m) (value_ctx value_arch : value) (rx : Runtime.Sim.Io.rx) :
    m (value × value × List Runtime.Sim.Io.tx) := do
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

/-- The extern relations, given the registered trampoline. Unported names are hard errors. -/
def eval_extern_rel (call : Call m) (name : String) (args : List value) : m (List value) :=
  if name == "ExternFunctionCall_eval" then eval_extern_func_call call args
  else if name == "ExternMethodCall_eval" then eval_extern_method_call call args
  else throw .err

/-- Bounded dynamic extern interface; unported functions are explicit hard errors. The
interpreter's callback is registered through `call_func`, collapsing callee failures.
Verify is a direct dynamic API, not a claim of Nano source-level reachability. -/
def externInterface : Interp_al.Interp.Extern m where
  eval_extern_rel := fun call => eval_extern_rel (Make.call_func call)
  eval_extern_func := fun name _ args =>
    if name == "init_objectState" then eval_extern_init args
    else if name == "init_archState" then pure init_arch_state
    else throw .err

end P4SpecTec.BackendSim.NanoSwitch.Pipe
