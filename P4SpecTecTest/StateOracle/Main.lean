import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTec.Refine.Quote
import P4SpecTec.Util.Yojson

/-!
Compare stateful Lean AL evaluation with pinned upstream interpreter observations.
The upstream entrypoint collapses hard errors and mismatches into `Run.Fail`;
this executable checks success/failure, text payloads and exact counters.
-/

namespace P4SpecTecTest.StateOracle

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Interp_al P4SpecTec.Refine
open P4SpecTec.Lang.Il P4SpecTec.Lang.Al

private def textTyp := Q.t .TextT
private def fresh : exp := Q.e (.CallE (Q.i "fresh_typeId") [] []) .TextT
private def x : exp := Q.e (.VarE (Q.i "x")) .TextT
private def save : prem := Q.pr (.LetPr x fresh)
private def mismatch : prem := Q.pr (.IfPr (Q.e (.BoolE false) .BoolT))
private def hard : prem := Q.pr (.LetPr (Q.e (.BoolE true) .BoolT) x)

private def function (name : String) (prems : List prem) : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i name) [] [] textTyp
    [Q.cl [] fresh prems, Q.cl [] fresh []] none [])

private def negativeFunction (name target : String) : Lang.Al.def :=
  let tagged (tag : String) : exp :=
    Q.e (.CatE (Q.e (.TextE (ByteText.ofString tag)) .TextT) fresh) .TextT
  Q.d (.FuncDecD (Q.i name) [] [] textTyp
    [Q.cl [] (tagged "first:") [Q.pr (.IfNotHoldPr (Q.i target) (.Seq []))],
     Q.cl [] (tagged "fallback:") []] none [])

private def relation (name : String) (prems : List prem) : Lang.Al.def :=
  Q.d (.RelD (Q.i name) (Q.nt (.Seq [])) []
    [Q.rg "one" ([], [], []) [Q.rp "path" prems []]] none [])

private def spec : Lang.Al.spec :=
  [Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] textTyp []),
   function "allocate" [],
   Q.d (.ExternDecD (Q.i "externalFresh") [] [] textTyp []),
   function "externalRetry" [Q.pr (.LetPr x
     (Q.e (.CallE (Q.i "externalFresh") [] []) .TextT))],
   Q.d (.FuncDecD (Q.i "through") [] [Q.pm (.DefP (Q.i "f") [] [] textTyp)] textTyp
     [Q.cl [Q.ar (.DefA (Q.i "f"))] (Q.e (.CallE (Q.i "f") [] []) .TextT) []] none []),
   function "retry" [save, mismatch],
   function "stop" [save, hard],
   relation "fails" [save, mismatch],
   relation "holds" [save],
   relation "errors" [save, hard],
   negativeFunction "negative" "fails",
   negativeFunction "negativeSuccess" "holds",
   negativeFunction "negativeError" "errors",
   Q.d (.RelD (Q.i "shared") (Q.nt (.Arg textTyp)) []
     [Q.rg "group" ([], [], [save])
       [Q.rp "reject" [mismatch] [x], Q.rp "accept" [] [x]]] none [])]

#guard (Interp.init spec).isOk
private def globals : Ctx.global := (Interp.init spec).toOption.getD {}
private def cfg : Interp.Config StateEval := { guard := false }
private def externCfg : Interp.Config StateEval := { cfg with
  extern := {
    eval_extern_rel := fun _ _ => throw .unmatch
    eval_extern_func := fun _ _ _ => do
      let _ ← StateEval.freshTypeId
      throw .unmatch } }

private def observe (r : Option (Except Fail value × FreshState)) :
    Option (Except Fail (Option String) × Int) :=
  r.map fun (result, state) =>
    (result.map (fun v => Runtime.Value.Get.text v >>= ByteText.toString?), state.counter)

private def observeRel (r : Option (Except Fail (List value) × FreshState)) :
    Option (Except Fail (Option String) × Int) :=
  r.map fun (result, state) =>
    (result.map fun values => match values with
      | [v] => Runtime.Value.Get.text v >>= ByteText.toString?
      | _ => none, state.counter)

private def builtin (seed : Int) (targs : List typ) (args : List value) :=
  observe (StateEval.run
    (Interp.invoke_builtin_func 1 cfg (Ctx.empty globals) (Q.i "fresh_typeId")
      [] targs args textTyp) (FreshState.ofInt seed))

private def runCase (name : String) (seed : Int) :
    Except String (Option (Except Fail (Option String) × Int)) :=
  match name with
  | "fresh-valid" | "fresh-wrap-max" | "fresh-wrap-min" =>
      pure (builtin seed [] [])
  | "fresh-type-arity" => pure (builtin seed [textTyp] [])
  | "fresh-value-arity" =>
      pure (builtin seed [] [Runtime.Value.Make.text (ByteText.ofString "argument")])
  | "shared" =>
      pure (observeRel (Interp.evalRelState 100 cfg globals "shared" []
        (FreshState.ofInt seed)))
  | "callback" =>
      pure (observe (Interp.evalFuncState 100 cfg globals "through" []
        [Runtime.Value.Make.func (Q.i "allocate") [] [] textTyp] (FreshState.ofInt seed)))
  | "extern-retry" =>
      pure (observe (Interp.evalFuncState 100 externCfg globals "externalRetry" []
        [] (FreshState.ofInt seed)))
  | "resume-after-failure" => do
      let some (_, state) := Interp.evalFuncState 100 cfg globals "stop" [] []
        (FreshState.ofInt seed) | throw "first session call diverged"
      pure (observe (Interp.evalFuncState 100 cfg globals "allocate" [] [] state))
  | "negative-success" =>
      pure (observe (Interp.evalFuncState 100 cfg globals "negativeSuccess" [] []
        (FreshState.ofInt seed)))
  | "negative-error" =>
      pure (observe (Interp.evalFuncState 100 cfg globals "negativeError" [] []
        (FreshState.ofInt seed)))
  | "allocate" | "retry" | "stop" | "negative" =>
      pure (observe (Interp.evalFuncState 100 cfg globals name [] [] (FreshState.ofInt seed)))
  | _ => throw s!"unknown state oracle case {name}"

private def resultMatches (scope : String) (result : Lean.Json)
    (actual : Except Fail (Option String)) : Except String Bool := do
  let status ← (← result.getObjVal? "status").getStr?
  match status, actual with
  | "ok", .ok (some text) =>
      pure (text == (← (← result.getObjVal? "text").getStr?))
  | "unmatch", .error .unmatch => pure true
  | "unmatch", .error .err => pure (scope != "primitive")
  | "abort", _ => throw "unexpected upstream abort is not covered by this oracle"
  | "ok", _ => pure false
  | "unmatch", _ => pure false
  | _, _ => throw s!"unknown upstream result status {status}"

#guard match resultMatches "primitive" (Lean.Json.mkObj [("status", .str "unmatch")])
    (.error .err) with
  | .ok false => true
  | _ => false
#guard match resultMatches "primitive" (Lean.Json.mkObj [("status", .str "unmatch")])
    (.error .unmatch) with
  | .ok true => true
  | _ => false

private def checkCase (fixture : Lean.Json) : Except String Unit := do
  let name ← (← fixture.getObjVal? "name").getStr?
  let scope ← (← fixture.getObjVal? "scope").getStr?
  let expectedScope := if name.startsWith "fresh-" then "primitive"
    else if name == "resume-after-failure" then "full-al-session" else "full-al"
  unless scope == expectedScope do throw s!"{name}: unexpected oracle scope {scope}"
  if scope == "full-al" then
    let operation ← (← fixture.getObjVal? "operation").getStr?
    let expectedOperation := match name with
      | "extern-retry" => "externalRetry"
      | "callback" => "through"
      | "negative-success" => "negativeSuccess"
      | "negative-error" => "negativeError"
      | _ => name
    unless operation == expectedOperation do
      throw s!"{name}: unexpected upstream operation {operation}"
  let seed ← P4SpecTec.Util.Yojson.int (← fixture.getObjVal? "seed")
  let counter ← P4SpecTec.Util.Yojson.int (← fixture.getObjVal? "counter")
  let result ← fixture.getObjVal? "result"
  if scope == "full-al-session" then
    let first ← fixture.getObjVal? "first"
    let firstCounter ← P4SpecTec.Util.Yojson.int (← fixture.getObjVal? "firstCounter")
    let some (firstResult, firstState) :=
      observe (Interp.evalFuncState 100 cfg globals "stop" [] [] (FreshState.ofInt seed))
      | throw "first session call diverged"
    unless firstState == firstCounter && (← resultMatches scope first firstResult) do
      throw s!"{name}: first session result/counter differs from upstream"
  let some (actualResult, actualCounter) ← runCase name seed
    | throw s!"{name}: Lean evaluation diverged"
  unless actualCounter == counter && (← resultMatches scope result actualResult) do
    throw s!"{name}: result/counter differs from upstream"

private def check (fixture : Lean.Json) : Except String Nat := do
  let cases ← (← fixture.getObjVal? "cases").getArr?
  let names ← cases.toList.mapM fun item => do
    (← item.getObjVal? "name").getStr?
  let expectedNames := ["allocate", "extern-retry", "callback", "retry", "stop",
    "negative", "negative-success", "negative-error", "shared", "resume-after-failure",
    "fresh-valid", "fresh-type-arity", "fresh-value-arity", "fresh-wrap-max",
    "fresh-wrap-min"]
  unless names == expectedNames do
    throw "state oracle case list is missing, reordered or duplicated"
  for item in cases do checkCase item
  pure cases.size

private def indexedRevision (line : String) : Except String String := do
  match line.trimAscii.toString.splitOn "\t" with
  | [metadata, "upstream/p4-spectec"] =>
      match metadata.splitOn " " with
      | ["160000", revision, "0"] =>
          if revision.length == 40 then pure revision
          else throw "upstream gitlink has an invalid revision"
      | _ => throw "upstream index entry is not a submodule gitlink"
  | _ => throw "cannot find indexed upstream submodule gitlink"

private def arguments (args : List String) (root : String) : Except String (String × String) :=
  match args with
  | [] => pure ("test/state/observed.json", root ++ "/upstream/p4-spectec")
  | [path] => pure (path, root ++ "/upstream/p4-spectec")
  | ["--upstream", upstream] =>
      if upstream.startsWith "/" then pure ("test/state/observed.json", upstream)
      else .error "--upstream must be an absolute path"
  | [path, "--upstream", upstream] =>
      if upstream.startsWith "/" then pure (path, upstream)
      else .error "--upstream must be an absolute path"
  | _ => .error "usage: check-state-oracle [fixture.json] [--upstream /absolute/path]"

end P4SpecTecTest.StateOracle

/-- Compare the fixture with the pinned upstream checkout and the Lean port. -/
def main (args : List String) : IO UInt32 := do
  let root := (← IO.currentDir).toString
  let .ok (fixturePath, upstream) := P4SpecTecTest.StateOracle.arguments args root
    | IO.eprintln "[state-oracle] invalid command line"; return 1
  let fixture ← P4SpecTec.Util.Yojson.readFile fixturePath
  let index ← IO.Process.output { cmd := "git", args := #["-C", root, "ls-files", "--stage",
    "--", "upstream/p4-spectec"] }
  if index.exitCode != 0 then
    IO.eprintln "[state-oracle] cannot inspect indexed upstream gitlink"; return 1
  let .ok indexed := P4SpecTecTest.StateOracle.indexedRevision index.stdout
    | IO.eprintln "[state-oracle] cannot read indexed upstream gitlink"; return 1
  let repoPrefix ← IO.Process.output { cmd := "git", args := #["-C", upstream,
    "rev-parse", "--show-prefix"] }
  if repoPrefix.exitCode != 0 || !repoPrefix.stdout.trimAscii.toString.isEmpty then
    IO.eprintln "[state-oracle] upstream path is not its own repository root"; return 1
  let pin ← IO.Process.output { cmd := "git", args := #["-C", upstream,
    "rev-parse", "HEAD"] }
  let recorded := (fixture.getObjVal? "upstreamRevision").bind Lean.Json.getStr?
  let .ok revision := recorded
    | IO.eprintln "[state-oracle] missing fixture revision"; return 1
  if pin.exitCode != 0 || indexed != pin.stdout.trimAscii.toString ||
      revision != indexed then
    IO.eprintln "[state-oracle] fixture, gitlink and upstream HEAD differ"; return 1
  match P4SpecTecTest.StateOracle.check fixture with
  | .error message => IO.eprintln s!"[state-oracle] {message}"; return 1
  | .ok count => IO.println s!"[state-oracle] {count} pinned observations match"; return 0
