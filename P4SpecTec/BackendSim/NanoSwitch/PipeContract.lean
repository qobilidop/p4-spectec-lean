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

end P4SpecTec.BackendSim.NanoSwitch.Pipe
