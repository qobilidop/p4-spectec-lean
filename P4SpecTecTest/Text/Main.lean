import Lean.Elab.Command
import P4SpecTec.Codegen.Funcs
import P4SpecTec.Interface.Builtin.Call
import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTec.Util.Yojson
import NanoP4Spec.«0-stdlib»

/-!
Compare the Lean text builtin dispatcher, interpreter and available generated
Nano-P4 wrapper against byte-level observations from pinned upstream OCaml.
The executable reads the fixture and checks the upstream revision at runtime.
-/

namespace P4SpecTecTest.Text.Generated

open P4SpecTec P4SpecTec.Prelude
open P4SpecTec.Util.Source P4SpecTec.Lang.Il P4SpecTec.Codegen

/-- The simple text signatures used to exercise the production builtin emitter. -/
def signatures : List (String × List typ' × typ') := [
  ("text_to_int", [.TextT], .NumT .IntT),
  ("int_to_text", [.NumT .IntT], .TextT),
  ("split_text", [.TextT, .TextT], .IterT (mkPhrase .TextT) .List),
  ("strip_prefix", [.TextT, .TextT], .TextT),
  ("strip_suffix", [.TextT, .TextT], .TextT),
  ("strip_all_whitespace", [.TextT], .TextT)]

/-- A synthetic spec with exactly the declarations whose wrappers are tested. -/
def spec : P4SpecTec.Lang.Al.spec := signatures.map fun (name, params, ret) =>
  mkPhrase (.BuiltinDecD (mkPhrase name) []
    (params.map fun t => mkPhrase (.ExpP (mkPhrase t))) (mkPhrase ret) [])

/-- Resolve text and integer types as the production emitter does. -/
def env : Env := Env.ofSpec "P4SpecTecTest.Text.Generated" spec

open Lean Elab Command in
run_cmd do
  for (name, params, ret) in signatures do
    let params := params.map fun t => Lang.Il.param'.ExpP (mkPhrase t)
    let source ← match Funcs.builtinDecl env name [] params ret with
      | .ok fmt => pure (Codegen.render fmt)
      | .error err => throwError "{name}: builtin emission failed: {err}"
    let stx ← match Lean.Parser.runParserCategory (← getEnv) `command source with
      | .ok stx => pure stx
      | .error err => throwError "{name}: generated command did not parse:\n{source}\n{err}"
    Lean.Elab.Command.elabCommand stx

end P4SpecTecTest.Text.Generated

namespace P4SpecTecTest.Text

open P4SpecTec
open P4SpecTec.Util.Source
open P4SpecTec.Lang.Il
open P4SpecTec.Runtime.Value

/-- Decode one hexadecimal digit, rejecting non-ASCII and non-hex characters. -/
def hexDigit (c : Char) : Except String Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then pure (n - 48)
  else if 97 ≤ n && n ≤ 102 then pure (n - 97 + 10)
  else if 65 ≤ n && n ≤ 70 then pure (n - 65 + 10)
  else .error s!"invalid hex digit {repr c}"

/-- Strictly decode even-length hexadecimal text to arbitrary bytes. -/
def hexBytes : List Char → Except String (List UInt8)
  | [] => pure []
  | high :: low :: rest => do
    let h ← hexDigit high
    let l ← hexDigit low
    pure (UInt8.ofNat (16 * h + l) :: (← hexBytes rest))
  | [_] => .error "odd-length hex string"

/-- Decode a fixture hex string without a UTF-8 conversion. -/
def decodeHex (s : String) : Except String ByteText := do
  pure (ByteText.ofBytes (← hexBytes s.toList).toByteArray)

#guard (decodeHex "00ffa9").isOk
#guard !(decodeHex "f").isOk
#guard !(decodeHex "fg").isOk
#guard !(decodeHex "é0").isOk

/-- Decode one fixture argument as a text or integer IL value. -/
def argument (json : Lean.Json) : Except String value := do
  if let .ok field := json.getObjVal? "textHex" then
    pure (Make.text (← decodeHex (← field.getStr?)))
  else if let .ok field := json.getObjVal? "intDecimal" then
    let s ← field.getStr?
    let some n := s.toInt? | throw s!"invalid decimal integer {repr s}"
    pure (Make.int n)
  else
    throw "fixture argument has neither textHex nor intDecimal"

/-- Decode one expected result, comparing values by payload rather than notes. -/
def expectedValue (json : Lean.Json) : Except String value := do
  if let .ok field := json.getObjVal? "textHex" then
    pure (Make.text (← decodeHex (← field.getStr?)))
  else if let .ok field := json.getObjVal? "intDecimal" then
    let s ← field.getStr?
    let some n := s.toInt? | throw s!"invalid decimal integer {repr s}"
    pure (Make.int n)
  else if let .ok field := json.getObjVal? "textsHex" then
    let hexes ← field.getArr?
    let texts ← hexes.toList.mapM fun item => do decodeHex (← item.getStr?)
    pure (Make.list (.IterT (mkPhrase .BoolT) .List) (texts.map Make.text))
  else
    throw "fixture result has no recognized payload"

/-- The output type expected by the interpreter's builtin call. -/
def outputType (operation : String) : Except String typ :=
  match operation with
  | "text_to_int" => pure (mkPhrase (.NumT .IntT))
  | "split_text" => pure (mkPhrase (.IterT (mkPhrase .BoolT) .List))
  | "int_to_text" | "strip_prefix" | "strip_suffix" | "strip_all_whitespace" =>
      pure (mkPhrase .TextT)
  | _ => .error s!"unknown text builtin {operation}"

/-- Re-embed a generated wrapper result as an IL value, preserving failure tags. -/
def embed {α : Type} (make : α → value) :
    Option (Except Prelude.Fail α) → Option (Except Prelude.Fail value)
  | some (.ok result) => some (.ok (make result))
  | some (.error failure) => some (.error failure)
  | none => none

/-- Dispatch to the declarations emitted and elaborated above, never handwritten substitutes. -/
def generated (operation : String) (inputs : List value) :
    Option (Except Prelude.Fail value) := do
  match operation, inputs with
  | "text_to_int", [input] =>
      embed Make.int (Generated.«$text_to_int» (← Get.text input))
  | "int_to_text", [input] =>
      let .Int n ← Get.num input | none
      embed Make.text (Generated.«$int_to_text» n)
  | "split_text", [input, separator] =>
      embed (Make.list (.IterT (mkPhrase .TextT) .List) ∘ List.map Make.text)
        (Generated.«$split_text» (← Get.text input) (← Get.text separator))
  | "strip_prefix", [input, part] =>
      embed Make.text (Generated.«$strip_prefix»
        (← Get.text input) (← Get.text part))
  | "strip_suffix", [input, suffix] =>
      embed Make.text (Generated.«$strip_suffix»
        (← Get.text input) (← Get.text suffix))
  | "strip_all_whitespace", [input] =>
      embed Make.text (Generated.«$strip_all_whitespace» (← Get.text input))
  | _, _ => none

/-- The upstream wrapper's observable result or exact exception category. -/
inductive Expected where
  /-- A returned upstream value. -/
  | ok (value : value)
  /-- A caught, retryable upstream `BuiltinError`. -/
  | builtinError
  /-- An uncaught upstream exception, represented by Lean as `Fail.err`. -/
  | hardError

/-- Compare one fixture with both semantic implementations and its generated wrapper, if present. -/
def checkCase (fixture : Lean.Json) : Except String Bool := do
  let name ← (← fixture.getObjVal? "name").getStr?
  let operation ← (← fixture.getObjVal? "operation").getStr?
  let typ ← outputType operation
  let args ← (← fixture.getObjVal? "args").getArr?
  let inputs ← args.toList.mapM argument
  let additions ← (← fixture.getObjVal? "additions").getNat?
  let result ← fixture.getObjVal? "result"
  let status ← (← result.getObjVal? "status").getStr?
  let expected ← match status with
    | "ok" => pure (Expected.ok (← expectedValue (← result.getObjVal? "value")))
    | "builtin_error" => pure Expected.builtinError
    | "assert_failure" | "invalid_argument" | "failure" => pure Expected.hardError
    | "other" => throw s!"{name}: unexpected upstream exception class"
    | _ => throw s!"{name}: unknown status {status}"
  let expectedAdditions := match expected with
    | .ok _ => 1
    | _ => 0
  if additions != expectedAdditions then
    throw s!"{name}: unexpected upstream callback count {additions}"
  let dispatched := Builtin.Call.invokeWithHints [] operation [] inputs
  match expected, dispatched with
  | .ok wanted, .ok (some actual) =>
      unless Runtime.Value.eq wanted actual do
        throw s!"{name}: dispatcher payload differs from upstream"
  | .builtinError, .ok none => pure ()
  | .hardError, .error _ => pure ()
  | _, _ => throw s!"{name}: dispatcher success/failure differs from upstream"
  let interpreted := (Interp_al.Interp.invoke_builtin_func 1 { guard := false }
    ⟨{}, {}⟩ (mkPhrase operation) [] [] inputs typ).run
  match expected, interpreted with
  | .ok wanted, some (.ok actual) =>
      unless Runtime.Value.eq wanted actual do
        throw s!"{name}: interpreter payload differs from upstream"
  | .builtinError, some (.error .unmatch) => pure ()
  | .hardError, some (.error .err) => pure ()
  | _, _ => throw s!"{name}: interpreter result differs from upstream"
  match expected, generated operation inputs with
  | .ok wanted, some (.ok actual) =>
      unless Runtime.Value.eq wanted actual do
        throw s!"{name}: emitted wrapper payload differs from upstream"
  | .builtinError, some (.error .unmatch) => pure ()
  | .hardError, some (.error .err) => pure ()
  | _, _ => throw s!"{name}: emitted wrapper result differs from upstream"
  if operation == "strip_all_whitespace" then
    let [input] := inputs | throw s!"{name}: generated wrapper needs one argument"
    let some text := Get.text input | throw s!"{name}: generated wrapper needs text"
    match expected, NanoP4Spec.«$strip_all_whitespace» text with
    | .ok wanted, some (.ok actual) =>
        unless Runtime.Value.eq wanted (Make.text actual) do
          throw s!"{name}: generated wrapper payload differs from upstream"
    | _, _ => throw s!"{name}: generated wrapper result differs from upstream"
    pure true
  else
    pure false

/-- Check every observation, requiring a nonempty fixture and no skipped cases. -/
def check (json : Lean.Json) : Except String (Nat × Nat) := do
  let cases ← (← json.getObjVal? "cases").getArr?
  if cases.isEmpty then throw "text oracle has no cases"
  let mut wrappers := 0
  for fixture in cases do
    if ← checkCase fixture then wrappers := wrappers + 1
  pure (cases.size, wrappers)

/-- Read the indexed upstream submodule SHA from this repository. -/
def indexedRevision (line : String) : Except String String := do
  match line.trimAscii.toString.splitOn "\t" with
  | [metadata, "upstream/p4-spectec"] =>
      match metadata.splitOn " " with
      | ["160000", revision, "0"] =>
          if revision.length == 40 then pure revision
          else throw "upstream gitlink has an invalid revision"
      | _ => throw "upstream index entry is not a submodule gitlink"
  | _ => throw "cannot find indexed upstream submodule gitlink"

#guard (indexedRevision ("160000 " ++ String.ofList (List.replicate 40 'a') ++
  " 0\tupstream/p4-spectec\n")).isOk
#guard !(indexedRevision ("100644 " ++ String.ofList (List.replicate 40 'a') ++
  " 0\tupstream/p4-spectec\n")).isOk

/-- Require fixture, indexed gitlink and actual upstream checkout to agree. -/
def checkRevision (fixture : Lean.Json) (indexed actual : String) : Except String Unit := do
  let recorded ← (← fixture.getObjVal? "upstreamRevision").getStr?
  if indexed.length != 40 || actual != indexed || recorded != actual then
    throw "fixture revision, indexed gitlink and upstream HEAD differ"

#guard (checkRevision (Lean.Json.mkObj [("upstreamRevision", .str
  (String.ofList (List.replicate 40 'a')))])
  (String.ofList (List.replicate 40 'a'))
  (String.ofList (List.replicate 40 'a'))).isOk
#guard !(checkRevision (Lean.Json.mkObj [("upstreamRevision", .str
  (String.ofList (List.replicate 40 'a')))])
  (String.ofList (List.replicate 40 'a'))
  (String.ofList (List.replicate 40 'b'))).isOk

/-- Command-line form: an optional fixture path and an optional absolute upstream override. -/
def arguments (args : List String) (root : String) : Except String (String × String) :=
  match args with
  | [] => pure ("test/text/observed.json", root ++ "/upstream/p4-spectec")
  | [path] => pure (path, root ++ "/upstream/p4-spectec")
  | ["--upstream", upstream] =>
      if upstream.startsWith "/" then pure ("test/text/observed.json", upstream)
      else .error "--upstream must be an absolute path"
  | [path, "--upstream", upstream] =>
      if upstream.startsWith "/" then pure (path, upstream)
      else .error "--upstream must be an absolute path"
  | _ => .error "usage: check-text-builtins [fixture.json] [--upstream /absolute/path]"

end P4SpecTecTest.Text

/-- Recheck the fixture and actual submodule HEAD on every executable invocation. -/
def main (args : List String) : IO UInt32 := do
  let root := (← IO.currentDir).toString
  let .ok (fixturePath, upstream) := P4SpecTecTest.Text.arguments args root
    | IO.eprintln "[text-oracle] invalid command line"; return 1
  let fixture ← P4SpecTec.Util.Yojson.readFile fixturePath
  let index ← IO.Process.output { cmd := "git", args := #["-C", root, "ls-files", "--stage",
    "--", "upstream/p4-spectec"] }
  let .ok indexed := P4SpecTecTest.Text.indexedRevision index.stdout
    | IO.eprintln "[text-oracle] cannot read indexed upstream gitlink"; return 1
  let repoPrefix ← IO.Process.output { cmd := "git", args := #["-C", upstream,
    "rev-parse", "--show-prefix"] }
  if repoPrefix.exitCode != 0 || !repoPrefix.stdout.trimAscii.toString.isEmpty then
    IO.eprintln "[text-oracle] upstream path is not its own repository root"; return 1
  let pin ← IO.Process.output { cmd := "git", args := #["-C", upstream,
    "rev-parse", "HEAD"] }
  if pin.exitCode != 0 then
    IO.eprintln "[text-oracle] cannot read upstream HEAD"; return 1
  let .ok () := P4SpecTecTest.Text.checkRevision fixture indexed pin.stdout.trimAscii.toString
    | IO.eprintln "[text-oracle] fixture, gitlink and HEAD revisions differ"; return 1
  match P4SpecTecTest.Text.check fixture with
  | .error e => IO.eprintln s!"[text-oracle] {e}"; return 1
  | .ok (count, wrappers) =>
      IO.println (s!"[text-oracle] {count} cases match dispatcher/interpreter/emitted wrappers; " ++
        s!"{wrappers} Nano wrapper checks")
      return 0
