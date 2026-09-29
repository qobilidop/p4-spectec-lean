import NanoP4Target.Session
import P4SpecTec.Lang.Il.Json
import P4SpecTec.Lang.Al.Json

/-!
Replay every pinned Nano STF session through both Lean execution paths and compare them with
the pinned upstream AL simulator: the reference AL interpreter with the registered NanoSwitch
externs, and the generated model with the typed extern instance. Both start from the exported
parsed program and perform semantic initialization in Lean; STF parsing stays upstream.

Each session compares the initialization outcome, context and architecture state, then every
driven packet's outcome, transmissions, forwarding decision, context and architecture state,
and finally the whole-session compositions against the stepwise results. A mismatch, a
program that does not decode and exhausted fuel are all failures; nothing is skipped. One
`SESSION <id> match` line reports each matching session for the completion checker.
-/

namespace P4SpecTecTest.NanoSessions

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Interp_al
open P4SpecTec.BackendSim P4SpecTec.BackendSim.NanoSwitch NanoP4Target

/-- Interpreter fuel and decoder fuel; exhaustion is a harness failure, never an outcome. -/
def fuel : Nat := 1000000

private def field := Lean.Json.getObjVal?
private def str (j : Lean.Json) (key : String) : Except String String := do
  (← field j key).getStr?
private def nat (j : Lean.Json) (key : String) : Except String Nat := do
  (← field j key).getNat?

private def packet (j : Lean.Json) : Except String Runtime.Sim.Io.rx := do
  let #[port, payload] ← j.getArr? | throw "malformed packet"
  pure (← port.getInt?, ByteText.ofString (← payload.getStr?))

private def packets (j : Lean.Json) : Except String (List Runtime.Sim.Io.tx) := do
  (← j.getArr?).toList.mapM packet

private def NanoSwitch_drive (ctx : NanoP4Spec.evalContext) (state : NanoP4Spec.objectState) :=
  NanoP4Spec.NanoSwitch_drive.run ctx state

private def failure : Fail → String
  | .err => "err"
  | .unmatch => "unmatch"

/-- One session's replay: an error message names the first disagreement. -/
def checkSession (g : Ctx.global) (cfg : Interp.Config) (values : Array Lang.Il.value)
    (entry : Lean.Json) : ExceptT String IO Unit := do
  let id ← str entry "id"
  let fail := fun (msg : String) => (throw s!"{id}: {msg}" : ExceptT String IO Unit)
  let value := fun (key : String) (j : Lean.Json) => do
    let some v := values[← nat j key]? | throw s!"{id}: value index out of range"
    pure v
  let bytes ← IO.FS.readBinFile (← str entry "export")
  let program ← ExceptT.mk (pure (Util.Yojson.parseBytes bytes >>= Lang.Il.Json.value))
  let some typed := NanoP4Spec.program.ofValue fuel program
    | throw s!"{id}: exported program does not decode into the generated model"
  let call := relCall cfg g fuel
  let init ← field entry "init"
  let drives ← (← field entry "drives").getArr?
  let reference := (Pipe.init_pipe call program).run
  let generated := (ExceptT.mk (NanoP4Spec.NanoSwitch_init.run typed) : Eval _).run
  match ← str init "class", reference, generated with
  | "runtimeFail", some (.error r), some (.error q) =>
    unless r == q do fail s!"initialization failure kinds differ: {failure r} and {failure q}"
    unless drives.isEmpty do fail "failed initialization has driven packets"
    return
  | "pass", some (.ok (ctx, arch)), some (.ok typedCtx) =>
    let ctx0 ← value "ctx" init
    let arch0 ← value "arch" init
    unless Runtime.Value.eq ctx ctx0 && Runtime.Value.eq arch arch0 do
      fail "reference initialization differs from upstream"
    unless Runtime.Value.eq (toValue typedCtx) ctx0 do
      fail "generated initialization differs from upstream"
    let mut state := (ctx, arch, typedCtx)
    let mut rxs := []
    let mut transmitted := []
    let mut ended := false
    for drive in drives do
      if ended then fail "a failing packet does not end its session"
      let rx ← packet (← field drive "rx")
      rxs := rxs ++ [rx]
      let (ctx, arch, typedCtx) := state
      let reference := (Pipe.drive_pipe call ctx arch rx).run
      let generated := (NanoP4Target.drive typedCtx rx).run
      match ← str drive "class", reference, generated with
      | "runtimeFail", some (.error r), some (.error q) =>
        unless r == q do fail s!"failure kinds differ: {failure r} and {failure q}"
        ended := true
      | "pass", some (.ok (ctx', arch', txs)), some (.ok (typedCtx', typedTxs)) =>
        let expected ← packets (← field drive "txs")
        unless Runtime.Value.eq ctx' (← value "ctx" drive) &&
            Runtime.Value.eq arch' (← value "arch" drive) && txs == expected do
          fail "reference packet processing differs from upstream"
        unless Runtime.Value.eq (toValue typedCtx') (← value "ctx" drive) &&
            typedTxs == expected do
          fail "generated packet processing differs from upstream"
        -- The forwarding decision itself, from both paths' NanoSwitch_drive on the same state.
        let decision ← value "decision" drive
        let .ok packetIn := Core.Object.PacketIn.init rx.2
          | fail "passing packet does not initialize"
        let packetState := Pipe.extern_to_yojson (.PacketIn packetIn)
        match (Interp.do_eval_rel fuel cfg g "NanoSwitch_drive"
            [ctx, Runtime.Value.Make.extern (Pipe.varT "objectState") packetState]).run,
          NanoSwitch_drive typedCtx ⟨packetState⟩ with
        | some (.ok [d, _]), some (.ok (typedDecision, _)) =>
          unless Runtime.Value.eq d decision && Runtime.Value.eq (toValue typedDecision) decision do
            fail "forwarding decision differs from upstream"
        | _, _ => fail "forwarding decision could not be recomputed"
        unless Pipe.is_forward decision == !expected.isEmpty do
          fail "upstream decision and transmissions disagree"
        state := (ctx', arch', typedCtx')
        transmitted := transmitted ++ [txs]
      | _, none, _ | _, _, none => fail "fuel exhausted"
      | c, _, _ => fail s!"packet outcome differs from upstream {c}"
    -- The session compositions agree with the stepwise replay.
    if drives.all (fun d => (str d "class").toOption == some "pass") then
      let (ctx, arch, typedCtx) := state
      match (referenceSession call program rxs).run, (NanoP4Target.session typed rxs).run with
      | some (.ok (c, a, t)), some (.ok (c', t')) =>
        unless Runtime.Value.eq c ctx && Runtime.Value.eq a arch && t == transmitted &&
            Runtime.Value.eq (toValue c') (toValue typedCtx) && t' == transmitted do
          fail "session composition differs from stepwise replay"
      | _, _ => fail "session composition failed where every step passed"
  | "pass", _, _ | "runtimeFail", _, _ => fail "initialization outcome differs from upstream"
  | c, _, _ => fail s!"unknown initialization class {c}"

/-- Replay the supplied session bundle; its provenance is checked by the Python driver. -/
def run (path : String) : IO UInt32 := do
  let g ← IO.ofExcept (Interp.init NanoP4Spec.spec)
  let cfg : Interp.Config := { guard := false, extern := Pipe.externInterface }
  -- The reference configuration uses the pinned print hints, which are empty for Nano.
  let spec ← Lang.Al.Json.readSpec "exports/nano-p4.al.json"
  let pinned ← IO.ofExcept (cfg.withPrintHints spec)
  unless pinned.printHints.isEmpty do
    throw (IO.userError "pinned Nano print hints are not empty")
  let bundle ← Util.Yojson.readFile path
  let values ← IO.ofExcept ((← IO.ofExcept (field bundle "values")).getArr?)
  let values ← IO.ofExcept (values.mapM Lang.Il.Json.value)
  let sessions ← IO.ofExcept ((← IO.ofExcept (field bundle "sessions")).getArr?)
  let mut failed := 0
  for session in sessions do
    match ← (checkSession g cfg values session).run with
    | .ok () => IO.println s!"SESSION {← IO.ofExcept (str session "id")} match"
    | .error message =>
      IO.eprintln s!"[nano-sessions] MISMATCH {message}"
      failed := failed + 1
  IO.println s!"[nano-sessions] {sessions.size - failed} of {sessions.size} sessions match"
  return if failed == 0 then 0 else 1

end P4SpecTecTest.NanoSessions

/-- Entry point; accepts only one explicitly supplied session bundle. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | [path] => P4SpecTecTest.NanoSessions.run path
  | _ => IO.eprintln "usage: check-nano-sessions SESSIONS.json" *> pure 1
