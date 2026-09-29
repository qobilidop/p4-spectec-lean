import P4SpecTec.BackendSim.NanoSwitch.Pipe

/-!
Reusable contracts for the bounded dynamic NanoSwitch target; not an upstream mirror.
These branch facts preserve callback and fresh-state behavior. They do not discharge
the generated Nano extern contract or establish whole-program target composition.
-/

namespace P4SpecTec.BackendSim.NanoSwitch.Pipe

open P4SpecTec.Prelude

/-- A raw extern receiver is rejected before any callback, preserving the fresh counter. -/
theorem rawReceiverHandlerError (call : Call)
    (ctx method names : Lang.Il.value) (note : Lang.Il.typ') (json : Lean.Json)
    (state : FreshState) :
    StateEval.run (eval_extern_method_call call
      [ctx, Runtime.Value.Make.extern note json, method, names]) state =
      some (.error .err, state) := by
  rfl

/-- info: 'P4SpecTec.BackendSim.NanoSwitch.Pipe.rawReceiverHandlerError'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rawReceiverHandlerError

open P4SpecTec.Runtime P4SpecTec.Util.Source

/-- Short-packet extract returns the raw serialized receiver and original context without
calling the callback or changing the fresh counter. The guard uses signed host addition. -/
theorem shortPacketExtract (call : Call) (ctx typeId : Lang.Il.value)
    (json : Lean.Json) (pkt : Core.Object.PacketIn.t) (state : FreshState)
    (decoded : extern_of_yojson json = .ok (.PacketIn pkt))
    (short : Core.Object.hostAdd pkt.idx 24 > pkt.len) :
    StateEval.run (eval_extern_method_call call
      [ctx, Value.Make.case (varT "value")
        (.Seq [.Atom (mkPhrase (.Keyword "PACKET")), .Arg typeId,
          .Arg (Value.Make.extern (varT "objectState") json)]),
       Value.Make.text (ByteText.ofString "extract"),
       Value.Make.list (.IterT (mkPhrase (varT "nameIR")) .List)
         [Value.Make.text (ByteText.ofString "hdr")]]) state =
      some (.ok [Value.Make.extern (varT "objectState")
        (extern_to_yojson (.PacketIn pkt)), ctx], state) := by
  simp [eval_extern_method_call, Value.Make.case, Value.Make.extern, Value.Make.text,
    Value.Make.list, Value.Make.mk, Value.Get.extern, Value.Get.text, Value.Get.list,
    required, checked, decoded, short, StateEval.run, List.mapM]
  rfl

/-- info: 'P4SpecTec.BackendSim.NanoSwitch.Pipe.shortPacketExtract'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shortPacketExtract

end P4SpecTec.BackendSim.NanoSwitch.Pipe
