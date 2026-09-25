import P4SpecTec.Lang.Al.Json
import P4SpecTec.Interface.P4.Unparse
import P4SpecTec.Interface.Builtin.Call
import P4SpecTec.Interp.InterpAl.Interp

/-!
Compare note-aware printing with observations from the pinned upstream printer.
The executable reads fixtures on every invocation, independently of Lake's cache.
-/

namespace P4SpecTecTest.Print

open P4SpecTec

/-- Require oracle observations from the revision currently under test. -/
def checkRevision (json : Lean.Json) (pin : String) : Except String Unit := do
  let revision ← (← json.getObjVal? "upstreamRevision").getStr?
  if revision.length != 40 || revision != pin then
    throw "fixture revision differs from upstream HEAD"

#guard (checkRevision (Lean.Json.mkObj [("upstreamRevision", .str (String.ofList
  (List.replicate 40 'a')))]) (String.ofList (List.replicate 40 'a'))).isOk
#guard !(checkRevision (Lean.Json.mkObj [("upstreamRevision", .str (String.ofList
  (List.replicate 40 'a')))]) (String.ofList (List.replicate 40 'b'))).isOk

/-- A value shape that upstream's P4 printer explicitly rejects. -/
def unprintable : Lang.Il.value :=
  ⟨.StructV [], .mk 0 .TextT 0, Util.Source.no_region⟩

#guard !(P4.Unparse.printWithHints [] unprintable).isOk
#guard !(Builtin.Call.invokeWithHints [] "print_" [] [unprintable]).isOk

-- Printer exceptions are hard errors, never a retryable rule mismatch.
#guard match (Interp_al.Interp.invoke_builtin_func 1 { guard := false }
    ⟨{}, {}⟩ (Util.Source.mkPhrase "print_") [] [] [unprintable]
    (Util.Source.mkPhrase .TextT)).run with
  | some (.error .err) => true
  | _ => false

/-- Decode the actual upstream AST and value fixtures and compare exact output bytes. -/
def check (json : Lean.Json) : Except String Nat := do
  let revision ← (← json.getObjVal? "upstreamRevision").getStr?
  if revision.length != 40 then throw "print oracle has an invalid upstream revision"
  let cases ← (← json.getObjVal? "cases").getArr?
  if cases.isEmpty then throw "print oracle has no cases"
  for fixture in cases do
    let name ← (← fixture.getObjVal? "name").getStr?
    let spec ← Lang.Al.Json.spec (← fixture.getObjVal? "spec")
    let value ← Lang.Il.Json.value (← fixture.getObjVal? "value")
    let expected ← (← fixture.getObjVal? "output").getStr?
    let hints ← P4.Unparse.hints_of_spec_al spec
    let cfg ← Interp_al.Interp.Config.withPrintHints { guard := false } spec
    let actual ← P4.Unparse.printWithHints hints value
    if actual != expected then
      throw s!"print oracle {name}: expected {repr expected}, got {repr actual}"
    let dispatched ← Builtin.Call.invokeWithHints hints "print_" [] [value]
    match dispatched with
    | some ⟨.TextV text, _, _⟩ =>
      if text != ByteText.ofString expected then
        throw s!"print oracle {name}: builtin output differs"
    | _ => throw s!"print oracle {name}: builtin failed"
    match (Interp_al.Interp.invoke_builtin_func 1 cfg ⟨{}, {}⟩
        (Util.Source.mkPhrase "print_") [] [] [value] (Util.Source.mkPhrase .TextT)).run with
    | some (.ok ⟨.TextV text, _, _⟩) =>
      if text != ByteText.ofString expected then
        throw s!"print oracle {name}: interpreter output differs"
    | _ => throw s!"print oracle {name}: interpreter failed"
  pure cases.size

end P4SpecTecTest.Print

/-- Recheck the current fixture file rather than a cached compile-time evaluation. -/
def main (args : List String) : IO UInt32 := do
  let path ← match args with
    | [] => pure "test/print/observed.json"
    | [path] => pure path
    | _ => throw (IO.userError "usage: check-print [fixture.json]")
  let json ← P4SpecTec.Util.Yojson.readFile path
  let pin ← IO.Process.output { cmd := "git", args := #["-C", "upstream/p4-spectec",
    "rev-parse", "HEAD"] }
  if pin.exitCode != 0 then
    IO.eprintln "[print-oracle] cannot read upstream HEAD"; return 1
  let .ok () := P4SpecTecTest.Print.checkRevision json pin.stdout.trimAscii.toString
    | IO.eprintln "[print-oracle] fixture revision differs from upstream HEAD"; return 1
  let result := P4SpecTecTest.Print.check json
  match result with
  | .error e => IO.eprintln s!"[print-oracle] {e}"; return 1
  | .ok n => IO.println s!"[print-oracle] {n} outputs match pinned upstream"; return 0
