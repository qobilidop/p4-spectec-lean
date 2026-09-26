import P4SpecTec.BackendSim.NanoSwitch.Pipe
import P4SpecTec.Lang.Il.Json

/-! Exact-pin direct driver replay. Assertions map to hard errors; relation
failure kinds and post-state remain distinct. Regions and value-cache identities
are not compared, but callback type notes and semantic packet bytes are checked. -/

namespace P4SpecTecTest.NanoDriver

open Lean P4SpecTec P4SpecTec.Prelude P4SpecTec.Runtime P4SpecTec.Lang.Il
open P4SpecTec.Util.Source P4SpecTec.BackendSim.NanoSwitch.Pipe

private def field := Json.getObjVal?
private def str (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?

private def atom (name : String) : Domain.Mixfix.t value := .Atom (mkPhrase (.Keyword name))

private def callback (decision payload : String) : RelCall := fun name args => do
  unless name == "NanoSwitch_drive" do throw .err
  let [ctx, state] := args | throw .err
  unless Value.Get.bool ctx == some false do throw .err
  let .VarT typeName [] := state.note.typ | throw .err
  unless typeName.it == "objectState" do throw .err
  let pkt ← checked (BackendSim.Core.Object.PacketIn.init (ByteText.ofString payload))
  unless Value.Get.extern state == some (extern_to_yojson (.PacketIn pkt)) do throw .err
  let _ ← StateEval.freshTypeId
  let result ← match decision with
    | "forward" => pure (Value.Make.case (varT "decision") (atom "FORWARD"))
    | "drop" => pure (Value.Make.case (varT "decision") (atom "DROP"))
    | "noncase" | "arity" => pure (Value.Make.bool true)
    | "sequence" => pure (Value.Make.case (varT "decision") (.Seq [atom "FORWARD"]))
    | "unmatch" => throw .unmatch
    | _ => throw .err
  pure (if decision == "arity" then [result] else [result, Value.Make.bool true])

private def packet (j : Json) : Except String Sim.Io.rx := do
  let a ← j.getArr?
  unless a.size == 2 do throw "wrong packet arity"
  pure (← a[0]!.getInt?, ByteText.ofString (← a[1]!.getStr?))

private def check (request expected : Json) : Except String Unit := do
  let decision ← str request "decision"
  let payload ← str request "payload"
  let port ← (← field request "port").getInt?
  let some (actual, state) := StateEval.run (drive_pipe (callback decision payload)
    (Value.Make.bool false) (Value.Make.text (ByteText.ofString "arch"))
    (port, ByteText.ofString payload)) 0 | throw "unexpected divergence"
  unless state.counter == (← (← field expected "counterAfter").getInt?) do
    throw "counter differs"
  unless (state.counter == 1) == (← (← field expected "called").getBool?) do
    throw "callback occurrence differs"
  match (← str expected "class"), actual with
  | "pass", .ok (ctx, arch, txs) =>
    let [expectedCtx, expectedArch] ←
      Util.Yojson.list Lang.Il.Json.value (← field expected "outputs")
      | throw "wrong expected output arity"
    unless Value.eq ctx expectedCtx && Value.eq arch expectedArch do
      throw "driver values differ"
    let .BoolT := ctx.note.typ | throw "wrong context note"
    let .BoolT := expectedCtx.note.typ | throw "wrong expected context note"
    let .TextT := arch.note.typ | throw "wrong architecture note"
    let .TextT := expectedArch.note.typ | throw "wrong expected architecture note"
    unless txs == (← Util.Yojson.list packet (← field expected "txs")) do
      throw "transmissions differ"
  | "unmatch", .error .unmatch => pure ()
  | "abort", .error .err => pure ()
  | "assertion", .error .err => pure ()
  | _, _ => throw "driver outcome differs"

-- Unsupported host ports reject before callbacks rather than wrap into valid ports.
#guard match StateEval.run (drive_pipe (callback "forward" "AA")
    (Value.Make.bool false) (Value.Make.bool false) (2 ^ 62, ByteText.ofString "AA")) 5 with
  | some (.error .err, s) => s.counter == 5
  | _ => false

-- Callback fuel exhaustion is divergence, never a drop or a retryable mismatch.
#guard (StateEval.run (drive_pipe (fun _ _ => ExceptT.mk fun _ => none)
  (Value.Make.bool false) (Value.Make.bool false) (0, ByteText.ofString "AA")) 0).isNone

/-- Replay direct observations of the original pinned driver. -/
def main : IO UInt32 := do
  let fixture ← Util.Yojson.readFile "test/nano-target/driver-observed.json"
  let requests ← Util.Yojson.readFile "test/nano-target/driver-requests.json"
  let checked : Except String Nat := do
    unless (← str fixture "upstreamRevision") ==
        "8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3" &&
        (← str fixture "scope") == "dynamic-driver" do throw "wrong provenance"
    let cases ← (← field fixture "cases").getArr?
    let requests ← requests.getArr?
    unless cases.size == 11 && cases.size == requests.size do throw "wrong case count"
    for i in [:cases.size] do
      let request ← field cases[i]! "request"
      unless request == requests[i]! do throw s!"request {i} differs"
      check request (← field cases[i]! "result")
    pure cases.size
  match checked with
  | .error e => IO.eprintln e; return 1
  | .ok n => IO.println s!"[nano-driver] {n} exact-pin observations match"; return 0

end P4SpecTecTest.NanoDriver

/-- Command-line entry point. -/
def main : IO UInt32 := P4SpecTecTest.NanoDriver.main
