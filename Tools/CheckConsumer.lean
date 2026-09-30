import Lean.Util.Path
import P4SpecTec.Codegen.Coverage.Check
import P4SpecTec.Lang.Il.Json
import P4SpecTec.Util.Yojson
import ExampleProofs.NanoP4SrcAddrFilter.Evaluation

/-!
Validation of the whole-program consumer certificate (`ExampleProofs.NanoP4SrcAddrFilter`):

* source identity: the quoted typed program's encoding is canonically the decoded export;
* observation: the proven initialization context and the proven STF session outcome (its
  transmissions and final context, which holds the raw extern receiver of the last extract)
  equal the pinned upstream simulator's recorded session;
* claims: each named theorem exists with exactly the expected closed type and only the allowed
  axioms, checked through Lean's ordinary frontend.

The completion checker binds the consumer obligation to these claims only after all succeed.
-/

open Lean Elab Term
open P4SpecTec P4SpecTec.Codegen.Coverage

namespace P4SpecTec.Tools.CheckConsumer

/-- The export the program is quoted from. -/
def exportPath : String := "exports/programs/nano-p4/positive/src-addr-filter.json"

/-- The recorded session of the program's STF file. -/
def sessionId : String := "corpus:packet:positive/src-addr-filter"

/-- The consumer claims with their exact expected types; every name is fully qualified. -/
def consumerClaims : List Claim :=
  [{ name := "ExampleProofs.NanoP4SrcAddrFilter.initialized", kind := "consumer"
     direction := "initialization"
     expectedType := "NanoP4Spec.NanoSwitch_init.run " ++ program ++ " = " ++
       "ExampleProofs.NanoP4SrcAddrFilter.initialOutcome" },
   { name := "ExampleProofs.NanoP4SrcAddrFilter.filterGenerated", kind := "consumer"
     direction := "generatedFilter"
     expectedType := "NanoP4Target.PacketStateText → " ++ packet ++
       "NanoP4Target.Transmits " ++ program ++ " [(port, NanoP4Target.hexText [b0, s, d])] " ++
       filtered },
   { name := "ExampleProofs.NanoP4SrcAddrFilter.shortGenerated", kind := "consumer"
     direction := "generatedShortDrop"
     expectedType := "NanoP4Target.PacketStateText → ∀ (port : Int), " ++
       "P4SpecTec.BackendSim.Core.Object.hostInt port = true → ∀ (bs : List UInt8), " ++
       "bs.length < 3 → NanoP4Target.Transmits " ++ program ++
       " [(port, NanoP4Target.hexText bs)] [[]]" },
   { name := "ExampleProofs.NanoP4SrcAddrFilter.stfSession", kind := "consumer"
     direction := "stfOutcome"
     expectedType := "NanoP4Target.PacketStateText → (NanoP4Target.session " ++ program ++
       " ExampleProofs.NanoP4SrcAddrFilter.stfPackets).run = " ++
       "ExampleProofs.NanoP4SrcAddrFilter.stfOutcome" },
   { name := "ExampleProofs.NanoP4SrcAddrFilter.stfTransmits", kind := "consumer"
     direction := "stfTransmissions"
     expectedType := "NanoP4Target.PacketStateText → NanoP4Target.Transmits " ++ program ++
       " [(0, NanoP4Target.hexText [0, 1, 0]), (0, NanoP4Target.hexText [0, 3, 0]), " ++
       "(0, NanoP4Target.hexText [0, 10, 0])] [[(0, NanoP4Target.hexText [0, 1, 0])], [], []]" },
   { name := "ExampleProofs.NanoP4SrcAddrFilter.referenceFilter", kind := "consumer"
     direction := "referenceFilter"
     expectedType := "NanoP4Target.PacketStateText → " ++
       "∀ {cfg : P4SpecTec.Interp_al.Interp.Config}, NanoP4Target.Reference cfg → " ++
       "cfg.printHints = [] → ∀ {vprogram : P4SpecTec.Lang.Il.value}, " ++
       "P4SpecTec.Refine.Rel vprogram " ++ program ++ " → " ++ packet ++
       "NanoP4Target.ReferenceTransmits cfg vprogram " ++
       "[(port, NanoP4Target.hexText [b0, s, d])] " ++ filtered },
   { name := "ExampleProofs.NanoP4SrcAddrFilter.programRel", kind := "consumer"
     direction := "programValue"
     expectedType := "P4SpecTec.Refine.Rel (P4SpecTec.Prelude.toValue " ++ program ++ ") " ++
       program }]
where
  /-- The quoted program. -/
  program : String := "ExampleProofs.NanoP4SrcAddrFilter.program"
  /-- A host-range port and three header bytes. -/
  packet : String := "∀ (port : Int), P4SpecTec.BackendSim.Core.Object.hostInt port = true → " ++
    "∀ (b0 s d : UInt8), "
  /-- The filter's transmissions, spelled out. -/
  filtered : String := "(if s.toNat = 1 ∨ s.toNat = 2 then " ++
    "[[(port, NanoP4Target.hexText [b0, s, d])]] else [[]])"

/-- Check every consumer claim in the elaborated environment. -/
def runClaimChecks (env : Environment) : IO Unit := do
  Check.inEnvironment env "ExampleProofs.NanoP4SrcAddrFilter"
    (consumerClaims.forM Check.checkClaim)
  for claim in consumerClaims do
    IO.println s!"[consumer] claim {claim.name}"
  IO.println s!"[consumer] {consumerClaims.length} claims checked"

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key

/-- A recorded transmission list. -/
private def txs (j : Json) : Except String (List Runtime.Sim.Io.tx) := do
  (← j.getArr?).toList.mapM fun tx => do
    let #[port, payload] ← tx.getArr? | throw "malformed transmission"
    pure (← port.getInt?, ByteText.ofString (← payload.getStr?))

/-- Source identity and upstream observation, in compiled code. -/
def runRuntimeChecks (bundlePath : String) : ExceptT String IO Unit := do
  let program := ExampleProofs.NanoP4SrcAddrFilter.program
  let bytes ← IO.FS.readBinFile exportPath
  let exported ← ExceptT.mk (pure (Util.Yojson.parseBytes bytes >>= Lang.Il.Json.value))
  unless Runtime.Value.eq exported (Prelude.toValue program) do
    throw s!"the quoted program differs from the decoded export {exportPath}"
  IO.println s!"[consumer] identity: the quoted program is the decoded {exportPath}"
  let bundle ← (Util.Yojson.readFile bundlePath : IO Json)
  let values ← ExceptT.mk (pure do
    (← (← field bundle "values").getArr?).mapM Lang.Il.Json.value)
  let sessions ← ExceptT.mk (pure do (← field bundle "sessions").getArr?)
  let some session := sessions.find? fun s =>
      ((field s "id").toOption.bind (·.getStr?.toOption)) == some sessionId
    | throw s!"no recorded session {sessionId}"
  let value := fun (j : Json) => do
    let some v := values[← (← field j "ctx").getNat?]? | throw "value index out of range"
    pure v
  -- initialization
  let initCtx ← ExceptT.mk (pure (field session "init" >>= value))
  let .some (.ok ctx) := ExampleProofs.NanoP4SrcAddrFilter.initialOutcome
    | throw "the proven initialization outcome is not a context"
  unless Runtime.Value.eq (Prelude.toValue ctx) initCtx do
    throw "the proven initialization context differs from upstream's"
  -- the session's transmissions and final context
  let drives ← ExceptT.mk (pure do (← field session "drives").getArr?)
  let recorded ← ExceptT.mk (pure (drives.toList.mapM fun d => field d "txs" >>= txs))
  let some last := drives.back? | throw "the recorded session has no packets"
  let finalCtx ← ExceptT.mk (pure (value last))
  let .some (.ok (ctx, transmitted)) := ExampleProofs.NanoP4SrcAddrFilter.stfOutcome
    | throw "the proven STF outcome is not a success"
  unless transmitted == recorded do
    throw "the proven STF transmissions differ from upstream's"
  unless Runtime.Value.eq (Prelude.toValue ctx) finalCtx do
    throw "the proven final STF context differs from upstream's"
  IO.println s!"[consumer] observation: proven initialization and STF outcome equal {sessionId}"

end P4SpecTec.Tools.CheckConsumer

/-- `check-consumer SESSIONS.json`: runtime checks, then claims through the frontend. -/
def main (args : List String) : IO UInt32 := do
  let [bundle] := args | do
    IO.eprintln "usage: check-consumer SESSIONS.json"
    return 2
  match ← (P4SpecTec.Tools.CheckConsumer.runRuntimeChecks bundle).run with
  | .error e =>
    IO.eprintln s!"[consumer] {e}"
    return 1
  | .ok () => pure ()
  try
    -- Use Lean's ordinary frontend to initialize notation and elaborator extensions.
    let source := "import Tools.CheckConsumer\n" ++
      "import ExampleProofs.NanoP4SrcAddrFilter.Certificate\n" ++
      "run_cmd do\n  P4SpecTec.Tools.CheckConsumer.runClaimChecks (← Lean.getEnv)\n"
    let result ← IO.Process.output {
      cmd := ((← findSysroot) / "bin" / "lean").toString, args := #["--stdin"]
    } (some source)
    (← IO.getStdout).putStr result.stdout
    (← IO.getStderr).putStr result.stderr
    return result.exitCode
  catch error =>
    IO.eprintln s!"[consumer] {error}"
    return 1
