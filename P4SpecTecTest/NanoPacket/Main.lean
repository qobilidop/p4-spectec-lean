import P4SpecTec.BackendSim.NanoSwitch.Pipe
import P4SpecTec.Lang.Al.Json

/-!
Replay actual pinned NanoSwitch_drive observations through the Lean AL interpreter.
This harness is not a simulator port: initialization inputs are captured from
upstream. It compares all semantic relation outputs and exact fresh counters.
Explicit interpreter and callback-depth fuel bound the otherwise mutable callback
trampoline; exhaustion is never accepted as an upstream failure.
-/

namespace P4SpecTecTest.NanoPacket

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Interp_al
open P4SpecTec.BackendSim.NanoSwitch.Pipe

private inductive Mutation where
  | none | localSequence | restoredPacket
  deriving BEq

private def mutateArgs (mutation : Mutation) (args : List Lang.Il.value) : List Lang.Il.value :=
  if mutation == .localSequence then args.map fun v => match v.it with
    | .CaseV (.Atom a) => { v with it := .CaseV (.Seq [.Atom a]) }
    | _ => v
  else args

private def targetExtern (call : Call) (mutation : Mutation) : Interp.Extern StateEval :=
  let target := externInterface call
  { target with eval_extern_rel := fun name args => do
      let outputs ← target.eval_extern_rel name args
      if mutation == .restoredPacket then
        match args, outputs with
        | [_, receiver, _, _], [state, ctx] =>
          let .CaseV (.Seq [a, b, .Arg _]) := receiver.it | throw .err
          pure [{ receiver with it := .CaseV (.Seq [a, b, .Arg state]) }, ctx]
        | _, _ => throw .err
      else pure outputs }

private def config (g : Ctx.global) (base : Interp.Config StateEval)
    (fuel : Nat) (mutation : Mutation := .none) : Nat → Interp.Config StateEval
  | 0 => { base with extern := targetExtern (fun _ _ _ => ExceptT.mk fun _ => none) mutation }
  | n + 1 => { base with extern := targetExtern (fun name typs args =>
      Interp.do_eval_func fuel (config g base fuel mutation n) g name typs
        (mutateArgs mutation args)) mutation }

private def field := Lean.Json.getObjVal?
private def str (j : Lean.Json) (key : String) : Except String String := do
  (← field j key).getStr?
private def int (j : Lean.Json) (key : String) : Except String Int := do
  (← field j key).getInt?

private def checkEvent (g : Ctx.global) (cfg : Interp.Config StateEval)
    (event : Lean.Json) : Except String String := do
  let inputs ← Util.Yojson.list Lang.Il.Json.value (← field event "inputs")
  let before ← int event "counterBefore"
  let after ← int event "counterAfter"
  unless (FreshState.ofInt before).counter == before do throw "out-of-range initial counter"
  let some (actual, state) := Interp.evalRelState 1000000 cfg g "NanoSwitch_drive" inputs
    (FreshState.ofInt before) | throw "fuel exhausted"
  unless state.counter == after do throw "fresh counter differs"
  match (← str event "class"), actual with
  | "pass", .ok got =>
    let expected ← Util.Yojson.list Lang.Il.Json.value (← field event "outputs")
    unless got.length == expected.length &&
        (got.zip expected).all (fun (a, b) => Runtime.Value.eq a b) do
      throw "semantic outputs differ"
    pure "pass"
  -- The upstream public runner collapses Err and Unmatch. Report, do not erase,
  -- the Lean tag; this check does not claim equality of internal failure kinds.
  | "runtimeFail", .error e => pure s!"runtimeFail (Lean {if e == .err then "err" else "unmatch"})"
  | "pass", .error e => throw s!"Lean failed: {if e == .err then "err" else "unmatch"}"
  | _, _ => throw "outcome differs"

private def rejects (label needle : String) (r : Except String String) : Except String Unit :=
  match r with
  | .ok _ => throw s!"{label}: mutation accepted"
  | .error e => unless (e.splitOn needle).length > 1 do
      throw s!"{label}: wrong rejection {e}"

private def sensitivity (g : Ctx.global) (base : Interp.Config StateEval)
    (event : Lean.Json) : Except String Unit := do
  let cfg := config g base 1000000 .none 100
  let outputs ← (← field event "outputs").getArr?
  let some first := outputs[0]? | throw "missing mutation output"
  let changed := first.setObjVal! "it" (.arr #[.str "BoolV", .bool false])
  rejects "output" "semantic outputs differ" (checkEvent g cfg
    (event.setObjVal! "outputs" (.arr (outputs.set! 0 changed))))
  rejects "counter" "fresh counter differs" (checkEvent g cfg
    (event.setObjVal! "counterAfter" (Lean.toJson ((← int event "counterAfter") + 1))))
  rejects "LOCAL sequence" "Lean failed" (checkEvent g
    (config g base 1000000 .localSequence 100) event)
  let inputs ← (← field event "inputs").getArr?
  let packet := inputs[1]!
  let payload ← (← field packet "it").getArr?
  let variant ← payload[1]!.getArr?
  let record := variant[1]!
  let bits ← (← field record "bits").getArr?
  let bit ← bits[8]!.getBool?
  let record := record.setObjVal! "bits" (.arr (bits.set! 8 (.bool (!bit))))
  let packet := packet.setObjVal! "it"
    (.arr (payload.set! 1 (.arr (variant.set! 1 record))))
  rejects "source header bit" "semantic outputs differ" (checkEvent g cfg
    (event.setObjVal! "inputs" (.arr (inputs.set! 1 packet))))

/-- Replay the supplied observation bundle; fixture provenance is checked by its Python driver. -/
def run (path : String) : IO UInt32 := do
  let debug := (← IO.getEnv "P4SPECTEC_PACKET_DEBUG").isSome
  let spec ← Lang.Al.Json.readSpec "exports/nano-p4.al.json"
  let g ← IO.ofExcept (Interp.init spec)
  let bundle ← Util.Yojson.readFile path
  let cases ← IO.ofExcept ((← IO.ofExcept (field bundle "cases")).getArr?)
  for c in cases do
    let name ← IO.ofExcept (str c "program")
    let guard ← IO.ofExcept ((← IO.ofExcept (field c "guard")).getBool?)
    let base ← IO.ofExcept (Interp.Config.withPrintHints
      ({ guard, debug } : Interp.Config StateEval) spec)
    let cfg := config g base 1000000 .none 100
    let observation ← IO.ofExcept (field c "observation")
    let events ← IO.ofExcept ((← IO.ofExcept (field observation "events")).getArr?)
    unless !events.isEmpty do throw (IO.userError "empty packet observation")
    for i in [:events.size] do
      IO.println s!"[nano-packet] checking {name} guard={guard} event={i}"
      match checkEvent g cfg events[i]! with
      | .error e => IO.eprintln s!"{name}/{i}: {e}"; return 1
      | .ok result => IO.println s!"[nano-packet] event result: {result}"
    IO.println s!"[nano-packet] {name} guard={guard}: {events.size} events match"
    if name == "nano-p4/testdata/positive/field-access.p4" && !guard then
      IO.ofExcept (sensitivity g base events[0]!)
      IO.println "[nano-packet] four semantic/state mutations rejected"
    if guard then
      IO.ofExcept (rejects "restored PACKET" "outcome differs" (checkEvent g
        (config g base 1000000 .restoredPacket 100) events[0]!))
      IO.println "[nano-packet] restored-PACKET guarded mutation rejected"
  return 0

end P4SpecTecTest.NanoPacket

/-- Entry point; accepts only one explicitly supplied packet fixture. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => P4SpecTecTest.NanoPacket.run path
  | _ => IO.eprintln "usage: check-nano-packet OBSERVATIONS.json" *> pure 1
