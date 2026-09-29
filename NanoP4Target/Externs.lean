import NanoP4Spec
import P4SpecTec.BackendSim.NanoSwitch.Pipe

/-!
# NanoP4Target.Externs

The concrete NanoSwitch extern relation over the generated Nano model; not an upstream
mirror. It is the typed counterpart of `eval_extern_method_call` in
`P4SpecTec.BackendSim.NanoSwitch.Pipe` (`p4spec/lib/backend-sim/nano_switch/pipe.ml`):
the same target-local checks, packet operations and result, with the three trampoline
calls replaced by the generated `find_var_e`, `write_value_from_bits` and `update_var_e`.
A failed callee of either kind is a mismatch of the extern call, as upstream's registered
`call_func` makes it (`P4SpecTec.BackendSim.Make.call_func`). The receiver result is the
runtime-only raw extern carrier, exactly as upstream writes it, not a repaired PACKET.

`NanoP4Target.Contract` proves that this instance discharges `NanoP4Spec.externsContract`
against the reference target registered in the interpreter configuration.
-/

namespace NanoP4Target

open P4SpecTec P4SpecTec.Prelude P4SpecTec.BackendSim P4SpecTec.BackendSim.NanoSwitch

/-- A generated callee through the registered trampoline: either failure kind of the callee
becomes a mismatch of the extern call, as `Make.call_func` does for the reference. -/
def callee {α : Type} (result : Option (Except Fail α)) : Eval α :=
  tryCatch (ExceptT.mk result) fun _ => throw .unmatch

/-- The Nano header variable written by extract. -/
def hdr : NanoP4Spec.nameIR := ByteText.ofString "hdr"

/-- Extract on a decoded packet: a short packet is returned unchanged with its context;
otherwise the header bits are parsed and written into the local `hdr` variable. -/
def extract (ctx : NanoP4Spec.evalContext) (pkt : Core.Object.PacketIn.t) :
    Eval (Core.Object.PacketIn.t × NanoP4Spec.evalContext) :=
  if Core.Object.hostAdd pkt.idx 24 > pkt.len then pure (pkt, ctx)
  else do
    let (pkt, bits) ← Pipe.checked (Core.Object.PacketIn.parse pkt 24)
    let value_hdr ← callee (NanoP4Spec.«$find_var_e» .LOCAL ctx hdr)
    let value_hdr' ← callee (NanoP4Spec.«$write_value_from_bits» value_hdr bits.toList)
    let ctx ← callee (NanoP4Spec.«$update_var_e» .LOCAL ctx hdr value_hdr')
    pure (pkt, ctx)

/-- The typed extern method call. Every receiver other than a PACKET, an undecodable
payload, and every method other than `extract(hdr)` is a target error. -/
def externMethodCall (ctx : NanoP4Spec.evalContext) (receiver : NanoP4Spec.value)
    (method : NanoP4Spec.callableId) (params : List NanoP4Spec.nameIR) :
    Eval (NanoP4Spec.value × NanoP4Spec.evalContext) := do
  let .PACKET _ state := receiver | throw .err
  let .PacketIn pkt ← Pipe.checked (Pipe.extern_of_payload state.json)
  unless Pipe.is_extract_hdr method params do throw .err
  let (pkt, ctx) ← extract ctx pkt
  pure (.runtimeExtern ⟨Pipe.extern_to_yojson (.PacketIn pkt)⟩, ctx)

/-- The concrete NanoSwitch extern instance for the generated Nano model. -/
instance externs : NanoP4Spec.Externs where
  ExternMethodCall_eval ctx receiver method params :=
    (externMethodCall ctx receiver method params).run

end NanoP4Target
