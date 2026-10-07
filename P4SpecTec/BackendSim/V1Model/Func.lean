import P4SpecTec.BackendSim.V1Model.Arch
import P4SpecTec.BackendSim.Hash

/-!
Port of `p4spec/lib/backend-sim/v1model/func.ml`: the v1model extern functions, over the
spec trampolines. Each returns the context, the architecture and the void call result,
as upstream does. `log_msg` prints upstream; here the message is still unpacked and its
format string still checked against its arguments (an error either way), but nothing is
printed, since diagnostics are outside the comparison profile. `random`, `clone`,
`truncate`, `assert` and `assume` raise upstream and are hard errors here.
-/

namespace P4SpecTec.BackendSim.V1Model.Func

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.BackendSim.SpecImpl
open P4SpecTec.BackendSim

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- A function's three results: the context, the architecture and the call result. -/
abbrev Outcome := value × value × value

/-- The void result in a context and architecture. -/
def void (value_ctx value_arch : value) : m Outcome := pure (value_ctx, value_arch, Pack.returnVoid)

/-- Mirrors `digest`: a no-op. -/
def digest (value_ctx value_sto : value) : m Outcome := void value_ctx value_sto

/-- Mirrors `mark_to_drop`: `egress_spec` to 511 and `mcast_grp` to 0. -/
def mark_to_drop (spec : Make.Spec m) (value_ctx value_sto : value) : m Outcome := do
  let value_ctx ← Rel.lvalue_write_dot_local spec.rel value_ctx value_sto
    (ByteText.ofString "standard_metadata") (ByteText.ofString "egress_spec")
    (Pack.pack_p4_fixedBit 9 511)
  let value_ctx ← Rel.lvalue_write_dot_local spec.rel value_ctx value_sto
    (ByteText.ofString "standard_metadata") (ByteText.ofString "mcast_grp")
    (Pack.pack_p4_fixedBit 16 0)
  void value_ctx value_sto

/-- The `HashAlgorithm` member of the local `algo` argument. -/
def algorithm (spec : Make.Spec m) (value_ctx : value) : m ByteText := do
  let (id_enum, id_enum_field) ← Func.required (Unpack.unpack_p4_enum
    (← Func.find_var_e_local spec.func value_ctx "algo"))
  unless id_enum == ByteText.ofString "HashAlgorithm" do throw .err
  pure id_enum_field

/-- Mirrors `hash`: `void hash<O, T, D, M>(out O result, in HashAlgorithm algo, in T base,
in D data, in M max)`. -/
def hash (spec : Make.Spec m) (value_ctx value_sto : value) : m Outcome := do
  let base ← Func.required ((Unpack.unpack_p4_fixedBit
    (← Func.find_var_e_local spec.func value_ctx "base")).map (·.2))
  let max ← Func.required ((Unpack.unpack_p4_fixedBit
    (← Func.find_var_e_local spec.func value_ctx "max")).map (·.2))
  let values ← Func.required (Unpack.unpack_p4_tuple
    (← Func.find_var_e_local spec.func value_ctx "data"))
  let algo ← algorithm spec value_ctx
  let result ← Func.required (do Hash.adjust base max (← Hash.compute_checksum algo values))
  let value_typ_O ← Func.find_type_e_local spec.func value_ctx (ByteText.ofString "O")
  let result ← Func.cast_op spec.func value_typ_O (Pack.pack_p4_arbitraryInt result)
  let value_ctx ← Rel.lvalue_write_var_local spec.rel value_ctx value_sto
    (ByteText.ofString "result") result
  void value_ctx value_sto

/-- The payload bytes of a packet as eight-bit P4 values. -/
def payloadValues (payload : Option Core.Object.PacketIn.t) : m (List value) := do
  match payload with
  | some packet_in =>
    let bytes ← Core.Object.Spec.checked (Core.Object.PacketIn.payload_bytes packet_in)
    pure (bytes.toList.map fun byte => Pack.pack_p4_fixedBit 8 byte)
  | none => pure []

/-- Mirrors `do_verify_checksum`: set `checksum_error` when the data's checksum differs
from the expected one. -/
def do_verify_checksum (spec : Make.Spec m) (payload : Option Core.Object.PacketIn.t)
    (value_ctx value_sto : value) : m Outcome := do
  let values ← Func.required (Unpack.unpack_p4_tuple
    (← Func.find_var_e_local spec.func value_ctx "data"))
  let values_payload ← payloadValues payload
  let checksum_expect ← Func.required ((Unpack.unpack_p4_fixedBit
    (← Func.find_var_e_local spec.func value_ctx "checksum")).map (·.2))
  let algo ← algorithm spec value_ctx
  let checksum_actual ← Func.required (Hash.compute_checksum algo (values ++ values_payload))
  let value_ctx ← (if checksum_expect == checksum_actual then pure value_ctx
    else (Rel.lvalue_write_dot_global spec.rel value_ctx value_sto
      (ByteText.ofString "standard_metadata") (ByteText.ofString "checksum_error")
      (Pack.pack_p4_fixedBit 1 1)))
  void value_ctx value_sto

/-- The local `condition` argument. -/
def condition (spec : Make.Spec m) (value_ctx : value) : m Bool := do
  Func.required (Unpack.unpack_p4_bool (← Func.find_var_e_local spec.func value_ctx "condition"))

/-- Mirrors `verify_checksum`. -/
def verify_checksum (spec : Make.Spec m) (value_ctx value_sto : value) : m Outcome := do
  if ← condition spec value_ctx then do_verify_checksum spec none value_ctx value_sto
  else void value_ctx value_sto

/-- Mirrors `verify_checksum_with_payload`. -/
def verify_checksum_with_payload (spec : Make.Spec m) (value_ctx value_sto : value)
    (packet_in : Core.Object.PacketIn.t) : m Outcome := do
  if ← condition spec value_ctx then do_verify_checksum spec (some packet_in) value_ctx value_sto
  else void value_ctx value_sto

/-- Mirrors `do_update_checksum`: write the data's checksum, cast to `O`. -/
def do_update_checksum (spec : Make.Spec m) (payload : Option Core.Object.PacketIn.t)
    (value_ctx value_sto : value) : m Outcome := do
  let values ← Func.required (Unpack.unpack_p4_tuple
    (← Func.find_var_e_local spec.func value_ctx "data"))
  let values_payload ← payloadValues payload
  let algo ← algorithm spec value_ctx
  let checksum ← Func.required (Hash.compute_checksum algo (values ++ values_payload))
  let value_typ_O ← Func.find_type_e_local spec.func value_ctx (ByteText.ofString "O")
  let value_checksum ← Func.cast_op spec.func value_typ_O (Pack.pack_p4_arbitraryInt checksum)
  let value_ctx ← Rel.lvalue_write_var_local spec.rel value_ctx value_sto
    (ByteText.ofString "checksum") value_checksum
  void value_ctx value_sto

/-- Mirrors `update_checksum`. -/
def update_checksum (spec : Make.Spec m) (value_ctx value_sto : value) : m Outcome := do
  if ← condition spec value_ctx then do_update_checksum spec none value_ctx value_sto
  else void value_ctx value_sto

/-- Mirrors `update_checksum_with_payload`. -/
def update_checksum_with_payload (spec : Make.Spec m) (value_ctx value_sto : value)
    (packet_in : Core.Object.PacketIn.t) : m Outcome := do
  if ← condition spec value_ctx then do_update_checksum spec (some packet_in) value_ctx value_sto
  else void value_ctx value_sto

/-- Read the architecture state, change it, and write it back. -/
def updateArch (spec : Make.Spec m) (value_sto : value) (f : Arch.t → Arch.t) : m value := do
  let arch_state ← Core.Object.Spec.checked (Arch.of_value
    (← Func.find_archState_e spec.func value_sto))
  Func.update_archState_e spec.func value_sto (Arch.to_value (f arch_state))

/-- Mirrors `resubmit_preserving_field_list`. -/
def resubmit_preserving_field_list (spec : Make.Spec m) (value_ctx value_sto : value) :
    m Outcome := do
  let value_index ← Func.find_var_e_local spec.func value_ctx "index"
  let index ← Func.required (Packet.ResubmitInfo.of_value value_index)
  let value_sto ← updateArch spec value_sto (Arch.with_resubmit index)
  void value_ctx value_sto

/-- Mirrors `recirculate_preserving_field_list`. -/
def recirculate_preserving_field_list (spec : Make.Spec m) (value_ctx value_arch : value) :
    m Outcome := do
  let value_index ← Func.find_var_e_local spec.func value_ctx "index"
  let index ← Func.required (Packet.RecirculateInfo.of_value value_index)
  let value_arch ← updateArch spec value_arch (Arch.with_recirculate index)
  void value_ctx value_arch

/-- Mirrors `clone_preserving_field_list`. -/
def clone_preserving_field_list (spec : Make.Spec m) (value_ctx value_sto : value) :
    m Outcome := do
  let arch_state ← Core.Object.Spec.checked (Arch.of_value
    (← Func.find_archState_e spec.func value_sto))
  let value_type ← Func.find_var_e_local spec.func value_ctx "type"
  let value_session ← Func.find_var_e_local spec.func value_ctx "session"
  let value_index ← Func.find_var_e_local spec.func value_ctx "index"
  let packet_clone ← Func.required (Packet.CloneInfo.of_value value_type value_session value_index)
  let value_sto ← Func.update_archState_e spec.func value_sto
    (Arch.to_value (Arch.with_clone packet_clone arch_state))
  void value_ctx value_sto

/-- Mirrors `format_braces` on the argument count only: `{{` and `}}` are literal braces,
`{}` consumes one argument, and a count mismatch raises upstream. -/
def format_braces (fmt : ByteText) (args : Nat) : Bool := Id.run do
  let bytes := fmt.bytes
  let n := bytes.size
  let mut i := 0
  let mut remaining := args
  let mut ok := true
  while i < n do
    let c := bytes.get! i
    if c == 123 && i + 1 < n && bytes.get! (i + 1) == 123 then i := i + 2
    else if c == 125 && i + 1 < n && bytes.get! (i + 1) == 125 then i := i + 2
    else if c == 123 && i + 1 < n && bytes.get! (i + 1) == 125 then
      if remaining == 0 then ok := false
      remaining := remaining - 1
      i := i + 2
    else i := i + 1
  pure (ok && remaining == 0)

/-- Mirrors `log_msg`: `extern void log_msg(string msg)`, without printing. -/
def log_msg (spec : Make.Spec m) (value_ctx value_sto : value) : m Outcome := do
  let _ ← Func.required (Unpack.unpack_p4_string
    (← Func.find_var_e_local spec.func value_ctx "msg"))
  void value_ctx value_sto

/-- Mirrors `log_msg_format`: `extern void log_msg<T>(string msg, in T data)`, without
printing; the argument count is still checked. -/
def log_msg_format (spec : Make.Spec m) (value_ctx value_sto : value) : m Outcome := do
  let msg ← Func.required (Unpack.unpack_p4_string
    (← Func.find_var_e_local spec.func value_ctx "msg"))
  let data ← Func.required (Unpack.unpack_p4_tuple
    (← Func.find_var_e_local spec.func value_ctx "data"))
  unless format_braces msg data.length do throw .err
  void value_ctx value_sto

end P4SpecTec.BackendSim.V1Model.Func
