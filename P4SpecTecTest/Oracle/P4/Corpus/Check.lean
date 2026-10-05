import P4SpecTec.Lang.Il.Json
import P4SpecTec.Prelude

/-!
Not a mirror. The corpus-v2 checks every Lean leg shares: strict validation of an
observation, then one verdict per relation from a leg's outcome. A leg runs one relation
on a booted program from a supplied fresh state; the reference interpreter and the
generated library each provide one. Nonzero Type.Fresh state is unsupported, not
alpha-normalized away. Verdicts retain Lean failure tags even where public upstream
collapses them.
-/

namespace P4SpecTecTest.Diff.P4Corpus

open Lean P4SpecTec P4SpecTec.Prelude

/-- Default maximum uncompressed bytes per case; a driver may state another bound. -/
def maxCaseBytes : Nat := 32 * 1024 * 1024

private def statedBound : List String → Option (Option Nat × List String)
  | [] => some (none, [])
  | "--max-case-bytes" :: n :: rest => do
    let bound ← n.toNat?
    let (none, others) ← statedBound rest | none
    pure (some bound, others)
  | arg :: rest => do
    let (bound, others) ← statedBound rest
    pure (bound, arg :: others)

/-- Worker options shared by every leg: `--max-case-bytes N` states the case bound, at most
once. Returns the bound and the remaining arguments, or `none` for a malformed option. -/
def caseBound (args : List String) : Option (Nat × List String) :=
  (statedBound args).map fun (bound, rest) => (bound.getD maxCaseBytes, rest)

/-- One relation of one Lean leg from an explicit state: an error when the leg cannot
represent the input, `none` when it does not terminate within its bound. -/
abbrev Leg := String → Lang.Il.value → FreshState →
  Except String (Option (Except Fail (List Lang.Il.value) × FreshState))

private def fields (j : Json) (keys : List String) : Except String Unit := do
  let obj ← j.getObj?
  let actual := obj.foldl (fun acc key _ => key :: acc) []
  unless actual.length == keys.length && actual.all keys.contains do
    throw "object fields differ from strict v2 schema"

private def field := Util.Yojson.field
private def strField (j : Json) (key : String) : Except String String := do
  (← field j key).getStr?

private def counter (j : Json) : Except String Int := do
  let n ← Util.Yojson.int j
  unless (FreshState.ofInt n).counter == n do throw "counter outside signed 63-bit range"
  pure n

private def position (j : Json) : Except String Unit := do
  fields j ["file", "line", "column"]
  let _ ← strField j "file"
  let _ ← counter (← field j "line")
  let _ ← counter (← field j "column")

private def region (j : Json) : Except String Unit := do
  fields j ["left", "right"]
  position (← field j "left")
  position (← field j "right")

private def phrase (j : Json) : Except String Json := do
  fields j ["it", "note", "at"]
  unless (← field j "note") == Json.null do throw "nonunit phrase note"
  region (← field j "at")
  field j "it"

private def id (j : Json) : Except String Unit := do
  let _ ← (← phrase j).getStr?

private def atom (j : Json) : Except String Unit := do
  let (name, args) ← Util.Yojson.variant (← phrase j)
  let arity := if ["Keyword", "Tag", "Operator"].contains name then 1 else 0
  let _ ← Util.Yojson.args name arity args
  let _ ← Lang.Il.Json.atom j

private def iterator (j : Json) : Except String Unit := do
  let (name, args) ← Util.Yojson.variant j
  let _ ← Util.Yojson.args name 0 args
  let _ ← Lang.Il.Json.iter j

mutual
private partial def strictType (j : Json) : Except String Unit := do
  let (name, args) ← Util.Yojson.variant j
  match name, args with
  | "BoolT", #[] | "TextT", #[] => pure ()
  | "NumT", #[t] =>
      let (tag, inner) ← Util.Yojson.variant t
      let _ ← Util.Yojson.args tag 0 inner
      let _ ← Lang.Il.Json.numtyp t
  | "VarT", #[i, ts] =>
      id i
      for t in ← ts.getArr? do strictTypePhrase t
  | "TupleT", #[ts] => for t in ← ts.getArr? do strictTypePhrase t
  | "IterT", #[t, iter] => strictTypePhrase t; iterator iter
  | "FuncT", #[ps, ts, result] =>
      for p in ← ps.getArr? do id p
      for t in ← ts.getArr? do strictTypePhrase t
      strictTypePhrase result
  | _, _ => throw "malformed recursive type constructor"

private partial def strictTypePhrase (j : Json) : Except String Unit := do
  strictType (← phrase j)
end

mutual
private partial def strictMixfix (j : Json) : Except String Unit := do
  let (name, args) ← Util.Yojson.variant j
  match name, args with
  | "Arg", #[v] => strictValue v
  | "Atom", #[a] => atom a
  | "Brack", #[l, inner, r] => atom l; strictMixfix inner; atom r
  | "Infix", #[l, a, r] => strictMixfix l; atom a; strictMixfix r
  | "Seq", #[xs] => for x in ← xs.getArr? do strictMixfix x
  | _, _ => throw "malformed recursive mixfix constructor"

private partial def strictValue (j : Json) : Except String Unit := do
  fields j ["it", "note", "at"]
  region (← field j "at")
  let note ← field j "note"
  fields note ["vid", "typ", "vhash"]
  let _ ← counter (← field note "vid")
  let _ ← counter (← field note "vhash")
  strictType (← field note "typ")
  let (name, args) ← Util.Yojson.variant (← field j "it")
  match name, args with
  | "BoolV", #[b] => let _ ← Util.Yojson.bool b; pure ()
  | "NumV", #[n] => let _ ← Lang.Il.Json.num n; pure ()
  | "TextV", #[s] => let _ ← s.getStr?; pure ()
  | "StructV", #[xs] =>
      for x in ← xs.getArr? do
        let .arr #[a, v] := x | throw "malformed struct pair"
        atom a; strictValue v
  | "CaseV", #[m] => strictMixfix m
  | "TupleV", #[xs] | "ListV", #[xs] => for x in ← xs.getArr? do strictValue x
  | "OptV", #[v] => if v != Json.null then strictValue v
  | "FuncV", #[i] => id i
  | "ExternV", #[_] => pure () -- Arbitrary semantic JSON, not IL constructors.
  | _, _ => throw "malformed recursive value constructor"
end

private def diagnostic (j : Json) : Except String Unit := do
  fields j ["source", "code", "message", "region"]
  let _ ← strField j "source"
  let _ ← strField j "message"
  let _ ← strField j "region"
  let code ← field j "code"
  unless code == Json.null || code.getStr?.isOk do throw "malformed diagnostic code"

private def envelope (name : String) (j : Json) : Except String (Int × Int × Bool) := do
  fields j ["relation", "mode", "cache", "det", "guard", "counterBefore",
    "counterAfterBoot", "counterAfter", "typeFresh", "result"]
  unless (← strField j "relation") == name && (← strField j "mode") == "AL" &&
      (← field j "cache") == Json.bool true && (← field j "det") == Json.bool false &&
      (← field j "guard") == Json.bool false do throw "wrong relation or configuration"
  unless (← counter (← field j "counterBefore")) == 0 do throw "session is not fresh"
  let afterBoot ← counter (← field j "counterAfterBoot")
  let after ← counter (← field j "counterAfter")
  let tick ← field j "typeFresh"
  let phases := ["beforeSpec", "afterSpec", "afterSetup", "afterBoot", "after"]
  fields tick phases
  let mut nonzero := false
  for phase in phases do
    if (← counter (← field tick phase)) != 0 then nonzero := true
  pure (afterBoot, after, nonzero)

private def resultShape (j : Json) : Except String String := do
  let cls ← strField j "class"
  if cls == "pass" then
    fields j ["class", "outputs"]
    for output in ← (← field j "outputs").getArr? do strictValue output
  else if ["syntax", "unmatch", "abort"].contains cls then
    fields j ["class", "diagnostic"]
    diagnostic (← field j "diagnostic")
  else throw "unsupported upstream result class"
  pure cls

private def verdict (status : String) (leanClass : String := "not-evaluated")
    (message : String := "") : Json :=
  Json.mkObj [("status", Json.str status), ("leanClass", Json.str leanClass),
    ("message", Json.str message)]

private def relation (leg : Leg) (boot : Lang.Il.value) (name : String) (j : Json) :
    Except String Json := do
  let (afterBoot, after, unsupported) ← envelope name j
  let result ← field j "result"
  let cls ← resultShape result
  if unsupported then return verdict "unsupported-type-fresh"
  if cls == "abort" then return verdict "unsupported-upstream-abort"
  if cls == "syntax" then throw "syntax result with nonnull boot"
  let (actual, state) ← match leg name boot (FreshState.ofInt afterBoot) with
    | .error message => return verdict "unrepresentable-input" "not-evaluated" message
    | .ok none => return verdict "exhausted" "exhausted"
    | .ok (some outcome) => pure outcome
  let leanClass := match actual with
    | .ok _ => "pass"
    | .error .err => "hard-error"
    | .error .unmatch => "unmatch"
  if state.counter != after then
    return verdict "counter-disagreement" leanClass s!"Lean {state.counter}, upstream {after}"
  match cls, actual with
  | "pass", .ok got =>
      let expected ← Util.Yojson.list Lang.Il.Json.value (← field result "outputs")
      if got.length == expected.length &&
          (got.zip expected).all (fun (a, b) => Runtime.Value.eq a b) then
        return verdict "matched" leanClass
      return verdict "output-disagreement" leanClass
  | "unmatch", .error _ => return verdict "matched-public-failure" leanClass
  | _, _ => return verdict "outcome-disagreement" leanClass

/-- Validate both sessions before evaluation, then return separate relation verdicts. -/
def check (leg : Leg) (j : Json) : Except String Json := do
  fields j ["schemaVersion", "name", "boot", "relations"]
  unless (← Util.Yojson.int (← field j "schemaVersion")) == 2 do
    throw "unsupported corpus schema"
  let name ← strField j "name"
  unless !name.isEmpty do throw "empty case identity"
  let runs ← field j "relations"
  fields runs ["Program_ok", "Program_inst"]
  let bootJson ← field j "boot"
  for relName in ["Program_ok", "Program_inst"] do
    let run ← field runs relName
    let _ ← envelope relName run
    let cls ← resultShape (← field run "result")
    unless (cls == "syntax") == (bootJson == Json.null) do
      throw "syntax class and boot nullness disagree"
  if bootJson == Json.null then
    let mut entries := []
    for relName in ["Program_ok", "Program_inst"] do
      let run ← field runs relName
      let (afterBoot, after, unsupported) ← envelope relName run
      unless (← strField (← field run "result") "class") == "syntax" &&
          afterBoot == 0 && after == 0 do throw "malformed syntax observation"
      entries := entries ++ [(relName,
        verdict (if unsupported then "unsupported-type-fresh" else "syntax-only"))]
    return Json.mkObj [("name", Json.str name), ("relations", Json.mkObj entries)]
  strictValue bootJson
  let boot ← Lang.Il.Json.value bootJson
  let ok ← relation leg boot "Program_ok" (← field runs "Program_ok")
  let inst ← relation leg boot "Program_inst" (← field runs "Program_inst")
  pure (Json.mkObj [("name", Json.str name),
    ("relations", Json.mkObj [("Program_ok", ok), ("Program_inst", inst)])])

end P4SpecTecTest.Diff.P4Corpus

namespace P4SpecTecTest.Diff.P4Corpus.Strict

open Std.Internal.Parsec Std.Internal.Parsec.String

/-! Reuse Lean's string/number token parsers but reject duplicate object keys
before Lean's ordinary JSON object map can silently keep the last value. -/
mutual
private partial def value : Parser Unit := do
  let c ← peek!
  if c == '{' then
    skip; ws
    if (← peek!) == '}' then skip; ws else object []
  else if c == '[' then
    skip; ws
    if (← peek!) == ']' then skip; ws else array
  else if c == '"' then
    skip
    let _ ← Lean.Json.Parser.str
    ws
  else if c == 't' then skipString "true"; ws
  else if c == 'f' then skipString "false"; ws
  else if c == 'n' then skipString "null"; ws
  else
    let _ ← Lean.Json.Parser.num
    ws

private partial def object (keys : List String) : Parser Unit := do
  Lean.Json.Parser.lookahead (· == '"') "object key"; skip
  let key ← Lean.Json.Parser.str
  if keys.contains key then fail "duplicate JSON object key"
  ws; Lean.Json.Parser.lookahead (· == ':') ":"; skip; ws
  value
  let c ← any
  if c == '}' then ws
  else if c == ',' then ws; object (key :: keys)
  else fail "invalid JSON object delimiter"

private partial def array : Parser Unit := do
  value
  let c ← any
  if c == ']' then ws
  else if c == ',' then ws; array
  else fail "invalid JSON array delimiter"
end

/-- Strict Unicode parsing plus duplicate-key rejection, including escaped keys. -/
def parse (bytes : ByteArray) : Except String Lean.Json := do
  let result ← P4SpecTec.Util.Yojson.parseBytes bytes
  let text := String.fromUTF8! bytes
  let _ ← Parser.run (do ws; value; eof) text
  pure result

end P4SpecTecTest.Diff.P4Corpus.Strict

/-- Answer bounded case-file paths from stdin, one structured line each, until EOF. -/
def P4SpecTecTest.Diff.P4Corpus.serve (leg : P4SpecTecTest.Diff.P4Corpus.Leg)
    (maxBytes : Nat := P4SpecTecTest.Diff.P4Corpus.maxCaseBytes) : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  output.putStrLn "{\"ready\":2}"
  output.flush
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let path := line.trimAscii.toString
    try
      let metadata ← System.FilePath.metadata path
      if metadata.byteSize.toNat > maxBytes then
        throw (IO.userError "case exceeds worker byte bound")
      let handle ← IO.FS.Handle.mk path IO.FS.Mode.read
      let bytes ← handle.read (maxBytes + 1).toUSize
      unless bytes.size == metadata.byteSize.toNat do
        throw (IO.userError "case changed or exceeds worker byte bound")
      let case ← IO.ofExcept (P4SpecTecTest.Diff.P4Corpus.Strict.parse bytes)
      match P4SpecTecTest.Diff.P4Corpus.check leg case with
      | .ok result => output.putStrLn result.compress
      | .error message => do
          output.putStrLn (Lean.Json.mkObj [("error", Lean.Json.str message)]).compress
    catch error => do
      output.putStrLn (Lean.Json.mkObj [("error", Lean.Json.str error.toString)]).compress
    output.flush
