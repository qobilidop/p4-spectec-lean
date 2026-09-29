import P4SpecTec.BackendSim.NanoSwitch.Pipe
import P4SpecTec.Lang.Al.Json
import NanoP4Spec.Refinement.Spec

/-!
Replay actual pinned NanoSwitch_drive and original drive_pipe observations
through the Lean AL interpreter and partial dynamic driver. Initialization
inputs are captured from upstream; this is not a boot or STF parser port.
It compares semantic context/architecture outputs, transmissions and fresh counters.
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

private def targetExtern (mutation : Mutation) : Interp.Extern StateEval :=
  let target : Interp.Extern StateEval := externInterface
  { target with eval_extern_rel := fun call name args => do
      let call' : Interp.FuncCall StateEval := fun name typs args =>
        call name typs (mutateArgs mutation args)
      let outputs ← target.eval_extern_rel call' name args
      if mutation == .restoredPacket then
        match args, outputs with
        | [_, receiver, _, _], [state, ctx] =>
          let .CaseV (.Seq [a, b, .Arg _]) := receiver.it | throw .err
          pure [{ receiver with it := .CaseV (.Seq [a, b, .Arg state]) }, ctx]
        | _, _ => throw .err
      else pure outputs }

private def config (base : Interp.Config StateEval) (mutation : Mutation := .none) :
    Interp.Config StateEval :=
  { base with extern := targetExtern mutation }

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

private def packet (j : Lean.Json) : Except String Runtime.Sim.Io.rx := do
  let a ← j.getArr?
  unless a.size == 2 do throw "wrong packet arity"
  pure (← a[0]!.getInt?, ByteText.ofString (← a[1]!.getStr?))

private def checkDriver (g : Ctx.global) (cfg : Interp.Config StateEval)
    (event : Lean.Json) : Except String String := do
  let [ctx, arch] ← Util.Yojson.list Lang.Il.Json.value (← field event "inputs")
    | throw "wrong driver input arity"
  let rx ← packet (← field event "rx")
  let before ← int event "counterBefore"
  let after ← int event "counterAfter"
  unless (FreshState.ofInt before).counter == before do throw "out-of-range initial counter"
  let some (actual, state) := StateEval.run
    (drive_pipe (fun name args => Interp.do_eval_rel 1000000 cfg g name args) ctx arch rx)
    (FreshState.ofInt before) | throw "driver fuel exhausted"
  unless state.counter == after do throw "driver fresh counter differs"
  match (← str event "class"), actual with
  | "pass", .ok (ctx', arch', txs) =>
    let [expectedCtx, expectedArch] ←
      Util.Yojson.list Lang.Il.Json.value (← field event "outputs")
      | throw "wrong driver output arity"
    unless Runtime.Value.eq ctx' expectedCtx && Runtime.Value.eq arch' expectedArch do
      throw "driver semantic outputs differ"
    let expectedTxs ← Util.Yojson.list packet (← field event "txs")
    unless txs == expectedTxs do throw "driver transmissions differ"
    pure "pass"
  | "runtimeFail", .error e => pure s!"runtimeFail (Lean {if e == .err then "err" else "unmatch"})"
  | "pass", .error _ => throw "driver failed"
  | _, _ => throw "driver outcome differs"

private def sensitivity (g : Ctx.global) (base : Interp.Config StateEval)
    (event : Lean.Json) : Except String Unit := do
  let cfg := config base .none
  let outputs ← (← field event "outputs").getArr?
  let some first := outputs[0]? | throw "missing mutation output"
  let changed := first.setObjVal! "it" (.arr #[.str "BoolV", .bool false])
  rejects "output" "semantic outputs differ" (checkEvent g cfg
    (event.setObjVal! "outputs" (.arr (outputs.set! 0 changed))))
  rejects "counter" "fresh counter differs" (checkEvent g cfg
    (event.setObjVal! "counterAfter" (Lean.toJson ((← int event "counterAfter") + 1))))
  rejects "LOCAL sequence" "Lean failed" (checkEvent g
    (config base .localSequence) event)
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

private def succeeded (label : String) (r : Option (Except Fail α × FreshState)) :
    Except String (α × FreshState) :=
  match r with
  | none => throw s!"{label}: fuel exhausted"
  | some (.error e, _) => throw s!"{label}: {if e == .err then "err" else "unmatch"}"
  | some (.ok output, state) => pure (output, state)

private def failedAs (label : String) (expected : Fail) (state : FreshState)
    (r : Option (Except Fail α × FreshState)) : Except String Unit := do
  let some (.error actual, final) := r | throw s!"{label}: expected failure absent"
  unless actual == expected && final == state do throw s!"{label}: failure/state differs"

private def generatedResult (label : String) (r : Option (Except Fail α)) : Except String α :=
  match r with
  | some (.ok x) => pure x
  | some (.error e) => throw s!"{label}: {if e == .err then "err" else "unmatch"}"
  | none => throw s!"{label}: diverged"

private def decodeRuntime (α : Type) [OfValue α] (label : String) (v : Lang.Il.value) :
    Except String α :=
  match OfValue.ofValue 10000 v with
  | some x => pure x
  | none => throw s!"{label}: runtime decoding failed"

-- Re-run the actual extern branch with generated copy-in/out and receiver write.
-- The handler still calls the quoted Nano definitions with guards disabled.
private def generatedContinuation (g : Ctx.global) (cfg : Interp.Config StateEval)
    (ctx callee args : Lang.Il.value) (state : FreshState) :
    Except String (NanoP4Spec.evalContext × FreshState) := do
  let caller ← decodeRuntime NanoP4Spec.evalContext "caller" ctx
  let selected ← decodeRuntime NanoP4Spec.callee "callee" callee
  let arguments ← decodeRuntime (List NanoP4Spec.argument) "arguments" args
  let .EXTERN_METHOD_dot_lparen_rparen receiverLvalue method parameters := selected
    | throw "generated continuation: expected extern method"
  let receiver ← generatedResult "generated receiver lookup"
    (NanoP4Spec.Lvalue_eval.run .LOCAL caller receiverLvalue)
  let calleeContext ← generatedResult "generated inherit"
    (NanoP4Spec.«$inherit_e» .GLOBAL caller)
  let (calleeContext, lvalues) ← generatedResult "generated Copy_in"
    (NanoP4Spec.Copy_in.run .LOCAL caller parameters .LOCAL calleeContext arguments)
  let names := parameters.map fun (.mk _ _ name) => name
  let ([raw, calleeAfter], finalState) ← succeeded "actual extract callback" (StateEval.run
    (eval_extern_method_call (fun name ts vs => Interp.do_eval_func 1000000 cfg g name ts vs)
      [ToValue.toValue calleeContext, ToValue.toValue receiver, ToValue.toValue method,
        ToValue.toValue names]) state)
    | throw "generated continuation: wrong callback output arity"
  let receiverAfter ← decodeRuntime NanoP4Spec.value "raw callback receiver" raw
  let .runtimeExtern _ := receiverAfter
    | throw "generated continuation: callback result was repaired"
  let calleeAfter ← decodeRuntime NanoP4Spec.evalContext "callee after callback" calleeAfter
  let copied ← generatedResult "generated Copy_out"
    (NanoP4Spec.Copy_out.run .LOCAL caller parameters .LOCAL calleeAfter lvalues)
  let written ← generatedResult "generated Lvalue_write"
    (NanoP4Spec.Lvalue_write.run .LOCAL copied receiverLvalue receiverAfter)
  pure (written, finalState)

private def extractReceiver (size : Nat) : Lang.Il.value :=
  let packet : BackendSim.Core.Object.PacketIn.t :=
    { bits := Array.replicate size true, idx := 0, len := size }
  Runtime.Value.Make.case (varT "value")
    (.Seq [.Atom (Util.Source.mkPhrase (.Keyword "PACKET")),
      .Arg (Runtime.Value.Make.text (ByteText.ofString "packet_in")),
      .Arg (Runtime.Value.Make.extern (varT "objectState")
        (extern_to_yojson (.PacketIn packet)))])

private def extractHeaderType : NanoP4Spec.typeIR :=
  .HEADER_lbrace_rbrace (ByteText.ofString "Nanonet")
    [.semi .BOOL (ByteText.ofString "drop"),
     .semi (.BIT_langle_rangle 7) (ByteText.ofString "packetType"),
     .semi (.BIT_langle_rangle 8) (ByteText.ofString "src"),
     .semi (.BIT_langle_rangle 8) (ByteText.ofString "dst")]

private def copiedHeader (size : Nat) : NanoP4Spec.value :=
  .HEADER_lbrace_rbrace (ByteText.ofString "Nanonet")
    [.semi (._B (size == 24)) (ByteText.ofString "drop"),
     .semi (.W 7 (if size == 24 then 127 else 0)) (ByteText.ofString "packetType"),
     .semi (.W 8 (if size == 24 then 255 else 0)) (ByteText.ofString "src"),
     .semi (.W 8 (if size == 24 then 255 else 0)) (ByteText.ofString "dst")]

-- Exercise the actual quoted callback, Copy_out and receiver-write continuation.
-- The initial context comes from the existing checked upstream fixture.
private def extractContinuation (base : Interp.Config StateEval) (event : Lean.Json) :
    Except String Unit := do
  let g ← Interp.init NanoP4Spec.spec
  let cfg := config { base with guard := false } .none
  let [initialContext, _] ← Util.Yojson.list Lang.Il.Json.value (← field event "inputs")
    | throw "extract continuation: wrong driver input arity"
  let initialState := FreshState.ofInt (← int event "counterBefore")
  let localScope := NanoP4Spec.scope.toValue .LOCAL
  let text := fun s => Runtime.Value.Make.text (ByteText.ofString s)
  let call := fun name args => Interp.do_eval_func 1000000 cfg g name [] args
  let expression := NanoP4Spec.lvalue.toValue
    (.dot (._ID (ByteText.ofString "pkt")) (._ID (ByteText.ofString "extract")))
  let args := Runtime.Value.Make.list
    (.IterT (Util.Source.mkPhrase (varT "argument")) .List)
    [NanoP4Spec.expression.toValue (._ID (ByteText.ofString "outHdr"))]
  for size in [8, 24] do
    let (ctx, state0) ← succeeded "extract preparation" (StateEval.run (do
      let header ← call "default" [NanoP4Spec.typeIR.toValue extractHeaderType]
      let ctx ← call "add_var_e" [localScope, initialContext, text "pkt", extractReceiver size]
      call "add_var_e" [localScope, ctx, text "outHdr", header]) initialState)
    let ([callee], state1) ← succeeded "initial Callee_eval" (StateEval.run
      (Interp.do_eval_rel 1000000 cfg g "Callee_eval" [localScope, ctx, expression]) state0)
      | throw "initial Callee_eval: wrong output arity"
    let ([after], state2) ← succeeded "Call_eval" (StateEval.run
      (Interp.do_eval_rel 1000000 cfg g "Call_eval" [localScope, ctx, callee, args]) state1)
      | throw "Call_eval: wrong output arity"
    let ((receiver, header), state3) ← succeeded "post-call lookup" (StateEval.run (do
      let receiver ← call "find_var_e" [localScope, after, text "pkt"]
      let header ← call "find_var_e" [localScope, after, text "outHdr"]
      pure (receiver, header)) state2)
    unless [state0, state1, state2, state3].all (· == initialState) do
      throw "extract continuation: fresh counter changed"
    let .ExternV raw := receiver.it | throw "extract continuation: receiver is not raw ExternV"
    let .ok (.PacketIn packet) := extern_of_yojson raw
      | throw "extract continuation: receiver objectState cannot decode"
    unless packet.idx == (if size == 24 then 24 else 0) &&
        packet.len == size && packet.bits == Array.replicate size true do
      throw "extract continuation: packet state differs"
    let represented ← decodeRuntime NanoP4Spec.value "raw post-call receiver" receiver
    let .runtimeExtern _ := represented
      | throw "extract continuation: raw receiver decoded into source constructor"
    unless Runtime.Value.eq receiver (ToValue.toValue represented) do
      throw "extract continuation: raw receiver roundtrip differs"
    let (generatedAfter, generatedState) ← generatedContinuation g cfg ctx callee args state1
    unless Runtime.Value.eq after (ToValue.toValue generatedAfter) && generatedState == state2 do
      throw "extract continuation: generated full context/state differs"
    let typedExpression ← decodeRuntime NanoP4Spec.lvalue "receiver expression" expression
    let some (.error .unmatch) :=
      NanoP4Spec.Callee_eval.run .LOCAL generatedAfter typedExpression
      | throw "extract continuation: generated receiver reuse did not mismatch"
    unless Runtime.Value.eq header (copiedHeader size).toValue do
      throw "extract continuation: header Copy_out differs"
    failedAs "subsequent Callee_eval" .unmatch state3 (StateEval.run
      (Interp.do_eval_rel 1000000 cfg g "Callee_eval" [localScope, after, expression]) state3)
    failedAs "direct handler on raw receiver" .err state3 (StateEval.run
      (eval_extern_method_call (fun name ts vs => Interp.do_eval_func 1000000 cfg g name ts vs)
        [after, receiver, text "extract", Runtime.Value.Make.list
          (.IterT (Util.Source.mkPhrase (varT "nameIR")) .List) [text "hdr"]]) state3)
    -- Deliberate PACKET-rewrap mutation, used only to distinguish the failed
    -- continuation above. The normal path always preserves the raw receiver.
    let original := extractReceiver size
    let .CaseV (.Seq [tag, typeId, .Arg _]) := original.it
      | throw "PACKET-rewrap mutation: original receiver shape differs"
    let wrapped := { original with it := .CaseV (.Seq [tag, typeId, .Arg receiver]) }
    let (mutated, state4) ← succeeded "PACKET-rewrap source update" (StateEval.run
      (call "update_var_e" [localScope, after, text "pkt", wrapped]) state3)
    let ([restoredCallee], state5) ← succeeded "PACKET-rewrap subsequent Callee_eval"
      (StateEval.run (Interp.do_eval_rel 1000000 cfg g "Callee_eval"
        [localScope, mutated, expression]) state4)
      | throw "PACKET-rewrap mutation: wrong callee arity"
    unless Runtime.Value.eq restoredCallee callee && state4 == initialState &&
        state5 == initialState do throw "PACKET-rewrap mutation: restored callee/state differs"

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
    let cfg := config base .none
    let observation ← IO.ofExcept (field c "observation")
    let events ← IO.ofExcept ((← IO.ofExcept (field observation "events")).getArr?)
    unless !events.isEmpty do throw (IO.userError "empty packet observation")
    for i in [:events.size] do
      IO.println s!"[nano-packet] checking {name} guard={guard} event={i}"
      match checkEvent g cfg events[i]! with
      | .error e => IO.eprintln s!"{name}/{i}: {e}"; return 1
      | .ok result => IO.println s!"[nano-packet] event result: {result}"
    IO.println s!"[nano-packet] {name} guard={guard}: {events.size} events match"
    let drivers ← IO.ofExcept ((← IO.ofExcept (field observation "driverEvents")).getArr?)
    unless drivers.size == events.size do throw (IO.userError "driver event count differs")
    for i in [:drivers.size] do
      match checkDriver g cfg drivers[i]! with
      | .error e => IO.eprintln s!"{name}/driver/{i}: {e}"; return 1
      | .ok result => IO.println s!"[nano-packet] driver {i}: {result}"
    if name == "nano-p4/testdata/positive/free-pass.p4" then
      let event := drivers[0]!
      IO.ofExcept (extractContinuation base event)
      IO.println "[nano-packet] short/full extract continuations and PACKET-rewrap mutation checked"
      IO.ofExcept (rejects "driver transmissions" "transmissions differ" (checkDriver g cfg
        (event.setObjVal! "txs" (.arr #[]))))
      IO.ofExcept (rejects "driver counter" "fresh counter differs" (checkDriver g cfg
        (event.setObjVal! "counterAfter" (Lean.toJson ((← IO.ofExcept
          (int event "counterAfter")) + 1)))))
    if name == "nano-p4/testdata/positive/field-access.p4" && !guard then
      IO.ofExcept (sensitivity g base events[0]!)
      IO.println "[nano-packet] four semantic/state mutations rejected"
    if guard then
      IO.ofExcept (rejects "restored PACKET" "outcome differs" (checkEvent g
        (config base .restoredPacket) events[0]!))
      IO.println "[nano-packet] restored-PACKET guarded mutation rejected"
  return 0

end P4SpecTecTest.NanoPacket

/-- Entry point; accepts only one explicitly supplied packet fixture. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => P4SpecTecTest.NanoPacket.run path
  | _ => IO.eprintln "usage: check-nano-packet OBSERVATIONS.json" *> pure 1
