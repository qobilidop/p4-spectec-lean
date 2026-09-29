import NanoP4Target.Externs

/-! Typed NanoSwitch extern instance: target-local rejections and the short-packet branch, for
arbitrary generated contexts. Callback paths are covered by `NanoP4Target.Contract` and the
pinned packet replay. -/

namespace P4SpecTecTest.NanoP4TargetExterns

open P4SpecTec P4SpecTec.Prelude P4SpecTec.BackendSim P4SpecTec.BackendSim.NanoSwitch
open NanoP4Target

private def extractName : NanoP4Spec.callableId := ByteText.ofString "extract"

private def state (pkt : Core.Object.PacketIn.t) : NanoP4Spec.objectState :=
  ⟨Pipe.extern_to_yojson (.PacketIn pkt)⟩

-- Non-PACKET receivers, including the raw extern extract writes back, are target errors.
example (ctx : NanoP4Spec.evalContext) :
    externMethodCall ctx (.W 8 1) extractName [hdr] = throw .err := rfl
example (ctx : NanoP4Spec.evalContext) (s : ExternValue) :
    externMethodCall ctx (.runtimeExtern s) extractName [hdr] = throw .err := by
  simp [externMethodCall]
-- An undecodable payload is a target error.
#guard match Pipe.extern_of_payload .null with | .error _ => true | .ok _ => false
example (ctx : NanoP4Spec.evalContext) (t : ByteText) (json : Lean.Json)
    (h : Pipe.extern_of_payload json = .error .decode) :
    externMethodCall ctx (.PACKET t ⟨json⟩) extractName [hdr] = throw .err := by
  simp [externMethodCall, Pipe.checked, h]

-- A short packet's raw serialized state decodes back unchanged; the short branch returns it
-- with the context and calls no callee (`NanoP4Target.Contract` covers the full branch).
private def short : Core.Object.PacketIn.t := { bits := #[true], idx := 0, len := 1 }

#guard match Pipe.extern_of_payload (state short).json with
  | .ok (.PacketIn pkt) => pkt == short
  | .error _ => false

end P4SpecTecTest.NanoP4TargetExterns
