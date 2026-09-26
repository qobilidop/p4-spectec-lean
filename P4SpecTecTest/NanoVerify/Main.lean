import P4SpecTec.BackendSim.NanoSwitch.Pipe
import P4SpecTecTest.Quote

/-! Direct pinned shared verify replay, including notes and callback order.
The real Nano AL check records absent function-call support, not successful
source-level verify execution. Cache identities and regions are not compared. -/

namespace P4SpecTecTest.NanoVerify

open Lean P4SpecTec P4SpecTec.Prelude P4SpecTec.Runtime P4SpecTec.Lang.Il
open P4SpecTec.Util.Source P4SpecTec.BackendSim.NanoSwitch.Pipe P4SpecTec.Interp_al

private def field := Json.getObjVal?
private def str (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?

private partial def notes (v : value) : List typ' :=
  v.note.typ :: match v.it with
    | .CaseV c => (Domain.Mixfix.args c).flatMap notes
    | .OptV (some v) => notes v
    | .ListV vs | .TupleV vs => vs.flatMap notes
    | .StructV fs => fs.flatMap fun (_, v) => notes v
    | _ => []

private def same (a b : value) : Bool := Value.eq a b && notes a == notes b
private def values (j : Json) := Util.Yojson.list Lang.Il.Json.value j
private def textV (s : String) := Value.Make.text (ByteText.ofString s)
private def signal := Value.Make.extern (varT "errorValue") (Json.mkObj [("raw", .str "signal")])
private def ctx := Value.Make.bool false
private def arch := Value.Make.extern (varT "archState") (Json.mkObj [("kept", .str "arch")])
private def params (xs : List String) :=
  Value.Make.list (.IterT (mkPhrase (varT "nameIR")) .List) (xs.map textV)

private def checkValue (kind : String) : value :=
  let b := Value.Make.bool (kind != "false")
  if kind == "bare" then b else
  Value.Make.case (varT "boolValue") (.Seq
    [.Atom (mkPhrase (if kind == "tag" then .Keyword "B" else .Tag "B")),
     .Arg (if kind == "inner" then Value.Make.nat 1 else b)])

private def callback (check failure : String) (calls : Array Json) : Call := fun name ts args => do
  let index := (← get).counter.toNat
  let some observed := calls[index]? | throw .err
  let expected ← checked (values (← checked (field observed "args")))
  unless name == (← checked (str observed "name")) && ts.isEmpty &&
      args.length == expected.length && (args.zip expected).all (fun (a,b) => same a b) do
    throw .err
  let _ ← StateEval.freshTypeId
  if failure == s!"unmatch{index + 1}" then throw .unmatch
  if failure == s!"abort{index + 1}" then throw .err
  pure (if index == 0 then checkValue check else signal)

private def args (shape : String) : List value :=
  match shape with
  | "arity" => []
  | "name" => [ctx, arch, Value.Make.bool false, params []]
  | "list" => [ctx, arch, textV "verify", Value.Make.bool false]
  | "element" => [ctx, arch, textV "verify",
      Value.Make.list (.IterT (mkPhrase (varT "nameIR")) .List) [Value.Make.bool false]]
  | "order" => [ctx, arch, textV "verify", params ["toSignal", "check"]]
  | "static_assert" => [ctx, arch, textV "static_assert", params ["check"]]
  | _ => [ctx, arch, textV "verify", params ["check", "toSignal"]]

private def checkCase (request expected : Json) : Except String Unit := do
  let calls ← (← field expected "calls").getArr?
  for call in calls do
    unless (← (← field call "types").getArr?).isEmpty do throw "nonempty observed types"
  let call := callback (← str request "check") (← str request "failure") calls
  let entry ← str request "entry"
  let shape ← str request "shape"
  let computation : StateEval (List value) := if entry == "core" then do
      let (c, a, r) ← BackendSim.Core.Func.verify call ctx arch
      pure [c, a, r]
    else if entry == "function" then eval_extern_func_call call (args shape)
    else (externInterface call).eval_extern_rel entry (args shape)
  let some (actual, state) := StateEval.run computation 0 | throw "unexpected divergence"
  unless state.counter == (← (← field expected "counterAfter").getInt?) &&
      state.counter == calls.size do throw "callback count or post-state differs"
  match (← str expected "class"), actual with
  | "pass", .ok outputs =>
    let expected ← values (← field expected "outputs")
    unless outputs.length == expected.length &&
        (outputs.zip expected).all (fun (a,b) => same a b) do throw "values or notes differ"
  | "unmatch", .error .unmatch => pure ()
  | "abort", .error .err => pure ()
  | "runtimeError", .error .err => pure ()
  | _, _ => throw "outcome differs"

private def rejects (label : String) (result : Except String Unit) : Except String Unit :=
  match result with
  | .ok _ => throw s!"accepted mutation: {label}"
  | .error _ => pure ()

private def sensitivity (c : Json) : Except String Unit := do
  let request ← field c "request"
  let expected ← field c "result"
  rejects "post-state" (checkCase request (expected.setObjVal! "counterAfter" (.num 3)))
  let calls ← (← field expected "calls").getArr?
  rejects "lookup order" (checkCase request
    (expected.setObjVal! "calls" (.arr #[calls[1]!, calls[0]!])) )
  let first := calls[0]!
  let arguments ← (← field first "args").getArr?
  let swapped := first.setObjVal! "args" (.arr #[arguments[1]!, arguments[0]!, arguments[2]!])
  rejects "lookup ABI" (checkCase request
    (expected.setObjVal! "calls" (.arr (calls.set! 0 swapped))))
  let outputs ← (← field expected "outputs").getArr?
  let changedNote := outputs[2]!.setObjVal! "note" (← field outputs[0]! "note")
  rejects "result note" (checkCase request
    (expected.setObjVal! "outputs" (.arr (outputs.set! 2 changedNote))))
  let changedCtx := outputs[0]!.setObjVal! "it" (.arr #[.str "BoolV", .bool true])
  rejects "preserved context" (checkCase request
    (expected.setObjVal! "outputs" (.arr (outputs.set! 0 changedCtx))))

-- Neither divergence in the first lookup nor in the second becomes RETURN.
#guard (StateEval.run (BackendSim.Core.Func.verify
  (fun _ _ _ => ExceptT.mk fun _ => none) ctx arch) 0).isNone
#guard (StateEval.run (BackendSim.Core.Func.verify (fun _ _ _ => do
  let n ← StateEval.freshTypeId
  if n == "FRESH__0" then pure (checkValue "true") else ExceptT.mk fun _ => none)
  ctx arch) 0).isNone

private def checkReachability (observed : Json) : IO Unit := do
  unless (← IO.ofExcept (str observed "mode")) == "AL" do
    throw (IO.userError "wrong interpreter mode")
  for key in ["cache", "det", "guard"] do
    unless (← IO.ofExcept ((← IO.ofExcept (field observed key)).getBool?)) == false do
      throw (IO.userError "wrong interpreter configuration")
  let spec ← Lang.Al.Json.readSpec "exports/nano-p4.al.json"
  let g ← IO.ofExcept (Interp.init spec)
  let externs := spec.filterMap fun d => match d.it with
    | .ExternRelD i .. => some i.it | _ => none
  let expected ← IO.ofExcept (Util.Yojson.list Json.getStr?
    (← IO.ofExcept (field observed "externRelations")))
  unless externs == expected && !externs.contains "ExternFunctionCall_eval" do
    throw (IO.userError "Nano extern declarations changed")
  let call : Call := fun name ts args =>
    Interp.do_eval_func 1000000 { guard := false } g name ts args
  let before ← IO.ofExcept ((← IO.ofExcept (field observed "counterBefore")).getInt?)
  unless before == 0 do throw (IO.userError "unexpected boundary seed")
  let some (result, state) := StateEval.run
    (BackendSim.SpecImpl.Func.find_var_e_local call ctx "check") 0
    | throw (IO.userError "Nano lookup exhausted fuel")
  let outcome := match result with
    | .ok _ => "pass" | .error .unmatch => "unmatch" | .error .err => "abort"
  unless outcome == (← IO.ofExcept (str observed "fullP4GetterAgainstNano")) &&
      outcome != "pass" && state.counter ==
        (← IO.ofExcept ((← IO.ofExcept (field observed "counterAfter")).getInt?)) do
    throw (IO.userError s!"Nano ABI boundary differs: {outcome}, counter {state.counter}")
  IO.println s!"[nano-verify] no Nano function relation; full-P4 getter gives {outcome}"

/-- Replay actual original-target observations with a finite explicit callback. -/
def main : IO UInt32 := do
  let fixture ← Util.Yojson.readFile "test/nano-verify/observed.json"
  let requests ← Util.Yojson.readFile "test/nano-verify/requests.json"
  let checked : Except String Nat := do
    unless (← str fixture "upstreamRevision") ==
        "8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3" &&
        (← str fixture "nanoSpecRevision") == "60dfd9912011bd5b1746ac88b26b58f7b3981991" &&
        (← str fixture "scope") == "shared-verify-and-nano-dispatch" do throw "wrong provenance"
    let cases ← (← field fixture "cases").getArr?
    let requests ← requests.getArr?
    unless cases.size == 19 && requests.size == cases.size do throw "wrong case count"
    for i in [:cases.size] do
      let request ← field cases[i]! "request"
      unless request == requests[i]! do throw "request identity differs"
      checkCase request (← field cases[i]! "result")
    sensitivity cases[0]!
    pure cases.size
  match checked with
  | .error e => IO.eprintln e; return 1
  | .ok n => IO.println s!"[nano-verify] {n} direct observations match; five mutations rejected"
  checkReachability (← IO.ofExcept (field fixture "nanoReachability"))
  return 0

end P4SpecTecTest.NanoVerify

/-- Command-line entry point. -/
def main : IO UInt32 := P4SpecTecTest.NanoVerify.main
