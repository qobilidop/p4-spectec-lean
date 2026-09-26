import P4SpecTec.BackendSim.NanoSwitch.Pipe
import P4SpecTec.Util.Yojson

/-!
Replay exact-pin data and direct dynamic-handler observations. Target-local
OCaml exceptions correspond to Lean hard errors, not retryable mismatches;
primitive exception categories remain distinct. This is not packet/STF replay.
-/

namespace P4SpecTecTest.NanoTargetOracle

open Lean P4SpecTec P4SpecTec.Prelude P4SpecTec.Runtime P4SpecTec.Lang.Il
open P4SpecTec.Util.Source P4SpecTec.BackendSim.Core.Object
open P4SpecTec.BackendSim.NanoSwitch.Pipe

private def pass (v : Json) : Json := Json.mkObj [("class", .str "pass"), ("value", v)]
private def failure (name : String) : Json := Json.mkObj [("class", .str name)]

private def observe : Except Error Json → Json
  | .ok v => pass v
  | .error .assertion => failure "assertion"
  | .error .invalidArgument => failure "invalidArgument"
  | .error .decode => failure "decode"
  | .error .hostRange => failure "unsupported-host-range"

private def field (j : Json) (key : String) : Except Error Json :=
  (j.getObjVal? key).mapError fun _ => .decode
private def text (j : Json) (key : String) : Except Error String := do
  (← field j key).getStr?.mapError fun _ => .decode
private def integer (j : Json) (key : String) : Except Error Int := do
  (← field j key).getInt?.mapError fun _ => .decode

private def primitive (op : String) (j : Json) : Except Error Json := do
  match op with
  | "hex" => pure (bits_to_yojson (← string_to_bits (ByteText.ofString (← text j "text"))))
  | "bits_string" =>
    pure (.str (String.fromUTF8! (bits_to_string (← bits_of_yojson (← field j "bits"))).bytes))
  | "signed" =>
    pure (.str (toString (← bits_to_int_signed (← bits_of_yojson (← field j "bits")))))
  | "unsigned" =>
    pure (.str (toString (bits_to_int_unsigned (← bits_of_yojson (← field j "bits")))))
  | "int_signed" | "int_unsigned" =>
    let some n := (← text j "value").toInt? | throw .decode
    let convert := if op == "int_signed" then int_to_bits_signed else int_to_bits_unsigned
    pure (bits_to_yojson (← convert n (← integer j "size")))
  | "init" => pure (PacketIn.to_yojson (← PacketIn.init (ByteText.ofString (← text j "text"))))
  | "decode" => pure (PacketIn.to_yojson (← PacketIn.of_yojson (← field j "packet")))
  | "parse" =>
    let (pkt, bs) ← PacketIn.parse (← PacketIn.of_yojson (← field j "packet"))
      (← integer j "size")
    pure (.arr #[PacketIn.to_yojson pkt, bits_to_yojson bs])
  | "payload" =>
    pure (bits_to_yojson (← PacketIn.payload (← PacketIn.of_yojson (← field j "packet"))))
  | "payload_bytes" =>
    let ns ← PacketIn.payload_bytes (← PacketIn.of_yojson (← field j "packet"))
    pure (.arr (ns.map fun n => .str (toString n)))
  | _ => throw .decode

private def isNat (v : value) (n : Nat) : Bool :=
  match v.it with | .NumV (.Nat actual) => actual == n | _ => false

private def callback : Call := fun name ts vs => do
  unless ts.isEmpty do throw .err
  let counter ← StateEval.freshTypeId
  match name, vs with
  | "find_var_e", [scope, ctx, hdr] =>
    let .CaseV (.Atom a) := scope.it | throw .err
    unless counter == "FRESH__0" && a.it == .Keyword "LOCAL" &&
        Value.Get.bool ctx == some false &&
        Value.Get.text hdr == some (ByteText.ofString "hdr") do throw .err
    pure (Value.Make.nat 10)
  | "write_value_from_bits", [hdr, bs] =>
    let some bs := Value.Get.list bs | throw .err
    unless counter == "FRESH__1" && isNat hdr 10 && bs.length == 24 &&
        bs.all (fun b => Value.Get.bool b == some true) do throw .err
    pure (Value.Make.nat 42)
  | "update_var_e", [scope, ctx, name, hdr] =>
    let .CaseV (.Atom a) := scope.it | throw .err
    unless counter == "FRESH__2" && Value.Get.bool ctx == some false &&
        a.it == .Keyword "LOCAL" && Value.Get.text name == some (ByteText.ofString "hdr") &&
        isNat hdr 42 do throw .err
    pure (Value.Make.bool true)
  | _, _ => throw .err

private def target (packet : Json) : Except String Json := do
  let receiver := Value.Make.case (varT "value") (.Seq
    [.Atom (mkPhrase (.Keyword "PACKET")),
     .Arg (Value.Make.text (ByteText.ofString "packet_in")),
     .Arg (Value.Make.extern (varT "objectState") (.arr #[.str "PacketIn", packet]))])
  let args := [Value.Make.bool false, receiver,
    Value.Make.text (ByteText.ofString "extract"),
    Value.Make.list (.IterT (mkPhrase (varT "nameIR")) .List)
      [Value.Make.text (ByteText.ofString "hdr")]]
  match StateEval.run (eval_extern_method_call callback args) 0 with
  | some (.ok [state, ctx], fresh) =>
    let .ExternV json := state.it | throw "target repaired raw ExternV"
    let some ctx := Value.Get.bool ctx | throw "unexpected context shape"
    let calls ← if fresh.counter == 0 then pure #[]
      else if fresh.counter == 3 then
        pure #[Json.str "find_var_e", .str "write_value_from_bits", .str "update_var_e"]
      else throw "unexpected callback state"
    pure (pass (Json.mkObj [("objectState", json), ("context", .bool ctx),
      ("callbacks", .arr calls)]))
  | some (.error .err, fresh) =>
    unless fresh.counter == 0 do throw "failed after callback effects"
    pure (failure "hard-error")
  | some (.error .unmatch, _) => throw "target produced a retryable mismatch"
  | some (.ok _, _) => throw "wrong target output arity"
  | none => throw "target exhausted fuel"

/-- Replay every recorded observation, comparing raw JSON rather than wrapping receiver values. -/
def main : IO UInt32 := do
  let fixture ← Util.Yojson.readFile "test/nano-target/observed.json"
  let requests ← Util.Yojson.readFile "test/nano-target/requests.json"
  let checked : Except String Nat := do
    unless (← (← fixture.getObjVal? "upstreamRevision").getStr?) ==
        "8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3" do throw "wrong upstream pin"
    unless (← (← fixture.getObjVal? "scope").getStr?) == "data-and-dynamic-handler" do
      throw "wrong observation scope"
    let cases ← (← fixture.getObjVal? "cases").getArr?
    unless cases.size == (← requests.getArr?).size && cases.size == 24 do
      throw "wrong case count"
    for i in [:cases.size] do
      let c := cases[i]!
      let request ← c.getObjVal? "request"
      unless request == (← requests.getArr?)[i]! do throw s!"request mismatch {i}"
      let expected ← c.getObjVal? "result"
      let op ← (← request.getObjVal? "op").getStr?
      let actual ← if op == "target" then target (← request.getObjVal? "packet")
        else pure (observe (primitive op request))
      -- Direct target array exceptions become Fail.err at the StateEval boundary.
      -- Never equate such an exception with .unmatch or a successful empty packet.
      let expected := if op == "target" && expected == failure "invalidArgument" then
          failure "hard-error" else expected
      unless actual == expected do
        throw s!"case {i}: {actual.compress} != {expected.compress}"
    pure cases.size
  match checked with
  | .error e => IO.eprintln e; return 1
  | .ok count => IO.println s!"[nano-target] {count} Lean observations match"; return 0

end P4SpecTecTest.NanoTargetOracle

/-- Command-line entry point for the bounded exact-pin replay. -/
def main : IO UInt32 := P4SpecTecTest.NanoTargetOracle.main
