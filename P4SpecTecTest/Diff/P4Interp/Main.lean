import P4SpecTec.Lang.Al.Json
import P4SpecTec.Lang.Il.Json
import P4SpecTec.Interp.InterpAl.Interp

/-!
Replay four pinned full-P4 oracle cases through the Lean AL interpreter. The
Python driver validates source provenance and the fixed fixture before handing
this executable a typed JSON observation bundle. Successful relation outputs
are compared semantically, and every completed run checks the exact fresh
counter after boot and evaluation.
-/

namespace P4SpecTecTest.Diff.P4Interp

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Interp_al

/-- A bounded interpreter fuel, distinct from an upstream mismatch. -/
def fuel : Nat := 10000000

/-! The pinned `backend-sim/placeholder.ml` externs used by AL validation.
Other extern operations stay hard failures; this is not a P4 simulator. -/
private def placeholderExtern : Interp.Extern StateEval where
  eval_extern_rel := fun _ _ => throw .err
  eval_extern_func := fun name _ _ =>
    let typName := match name with
      | "init_objectState" => some "objectState"
      | "init_archState" => some "archState"
      | _ => none
    match typName with
    | some typ => pure (Runtime.Value.Make.extern
        (.VarT (P4SpecTec.Util.Source.mkPhrase typ) []) Lean.Json.null)
    | none => throw .err

private def field (j : Lean.Json) (key : String) : Except String Lean.Json :=
  j.getObjVal? key

private def stringField (j : Lean.Json) (key : String) : Except String String := do
  (← field j key).getStr?

private def intField (j : Lean.Json) (key : String) : Except String Int := do
  P4SpecTec.Util.Yojson.int (← field j key)

private def counterField (j : Lean.Json) (key : String) : Except String Int := do
  let n ← intField j key
  unless (FreshState.ofInt n).counter == n do
    throw s!"{key}: counter is outside the signed 63-bit OCaml range"
  pure n

private def envelope (name : String) (j : Lean.Json) : Except String (Int × Int) := do
  unless (← stringField j "relation") == name do
    throw s!"{name}: wrong relation identity"
  unless (← stringField j "mode") == "AL" do
    throw s!"{name}: wrong interpreter mode"
  unless (← field j "guard") == Lean.Json.bool false do
    throw s!"{name}: guard must be disabled"
  unless (← field j "cache") == Lean.Json.bool true &&
      (← field j "det") == Lean.Json.bool false do
    throw s!"{name}: wrong upstream cache/determinism setting"
  let before ← counterField j "counterBefore"
  let afterBoot ← counterField j "counterAfterBoot"
  let after ← counterField j "counterAfter"
  unless before == 0 do throw s!"{name}: upstream session did not start fresh"
  pure (afterBoot, after)

private def outputs (j : Lean.Json) : Except String (List Lang.Il.value) := do
  P4SpecTec.Util.Yojson.list Lang.Il.Json.value (← field j "outputs")

private def diagnostic (j : Lean.Json) : Except String Unit := do
  let d ← field j "diagnostic"
  let _ ← stringField d "source"
  let code ← field d "code"
  unless code == Lean.Json.null || code.getStr?.isOk do
    throw "malformed diagnostic code"
  let _ ← stringField d "message"
  let _ ← stringField d "region"

private def checkRelation (fuelLimit : Nat) (cfg : Interp.Config StateEval) (g : Ctx.global)
    (boot : Lang.Il.value) (name : String) (j : Lean.Json) : Except String Unit := do
  let (afterBoot, expectedCounter) ← envelope name j
  let result ← field j "result"
  let resultClass ← stringField result "class"
  unless ["pass", "unmatch", "abort"].contains resultClass do
    throw s!"{name}: malformed upstream result class {resultClass}"
  let some (actual, state) := Interp.evalRelState fuelLimit cfg g name [boot]
    (FreshState.ofInt afterBoot)
    | throw s!"{name}: Lean exhausted fuel (not an upstream unmatch)"
  unless state.counter == expectedCounter do
    throw s!"{name}: fresh counter differs: Lean {state.counter}, upstream {expectedCounter}"
  match resultClass, actual with
  | "pass", .ok got =>
      let expected ← outputs result
      unless got.length == expected.length &&
          (got.zip expected).all (fun (a, b) => Runtime.Value.eq a b) do
        throw s!"{name}: semantic outputs differ"
  | "unmatch", .error _ =>
      -- The public upstream AL entrypoint collapses Err and Unmatch.
      diagnostic result
      pure ()
  | "abort", _ => throw s!"{name}: upstream abort is outside this comparison"
  | "pass", .error error =>
      throw s!"{name}: Lean {if error == .err then "hard error" else "unmatch"} \
        but upstream passed"
  | "unmatch", _ => throw s!"{name}: Lean passed but upstream failed"
  | _, _ => throw s!"{name}: malformed upstream result class {resultClass}"

private def checkCase (cfg : Interp.Config StateEval) (g : Ctx.global)
    (j : Lean.Json) : Except String String := do
  let name ← stringField j "name"
  let relations ← field j "relations"
  let bootJson ← field j "boot"
  let ok ← field relations "Program_ok"
  let inst ← field relations "Program_inst"
  if name == "syntax-error" then
    unless bootJson == Lean.Json.null do
      throw "syntax-error: boot value must be null"
    for (relName, run) in [("Program_ok", ok), ("Program_inst", inst)] do
      let (afterBoot, after) ← envelope relName run
      unless (← stringField (← field run "result") "class") == "syntax" &&
          afterBoot == 0 && after == 0 do
        throw s!"{relName}: malformed syntax-only observation"
      diagnostic (← field run "result")
    return name ++ " syntax-only (no Lean AL evaluation)"
  let boot ← Lang.Il.Json.value bootJson
  match checkRelation fuel cfg g boot "Program_ok" ok with
  | .error e => throw s!"{name}: {e}"
  | .ok _ => pure ()
  match checkRelation fuel cfg g boot "Program_inst" inst with
  | .error e => throw s!"{name}: {e}"
  | .ok _ => pure ()
  pure (name ++ " matches")

private def check (cfg : Interp.Config StateEval) (g : Ctx.global)
    (bundle : Lean.Json) : Except String (List String) := do
  unless (← intField bundle "schemaVersion") == 1 do
    throw "unsupported replay schema"
  let cases ← (← field bundle "cases").getArr?
  let names ← cases.toList.mapM fun j => stringField j "name"
  unless names == ["basic-routing", "positive-regression", "negative-regression",
      "syntax-error"] do
    throw "replay cases are missing, duplicated or reordered"
  cases.toList.mapM (checkCase cfg g)

private def rejects (label : String) (result : Except String α) : Except String Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw s!"sensitivity mutation {label} was accepted"

private def rejectsWith (label needle : String)
    (result : Except String α) : Except String Unit :=
  match result with
  | .error message =>
      unless (message.splitOn needle).length > 1 do
        throw s!"sensitivity mutation {label} failed for wrong reason: {message}"
  | .ok _ => throw s!"sensitivity mutation {label} was accepted"

/-- Exercise malformed and changed observations against the actual Lean decoder
and AL runner, after the unmodified four-case bundle has passed. -/
def sensitivity (cfg : Interp.Config StateEval) (g : Ctx.global)
    (bundle : Lean.Json) : Except String Unit := do
  let cases ← (← field bundle "cases").getArr?
  let some positive := cases[1]? | throw "missing positive sensitivity case"
  let some syntaxCase := cases[3]? | throw "missing syntax sensitivity case"
  let relations ← field positive "relations"
  let ok ← field relations "Program_ok"
  let result ← field ok "result"
  let values ← (← field result "outputs").getArr?
  let some first := values[0]? | throw "positive case has no output"
  let changedValue := first.setObjVal! "it" (.arr #[.str "BoolV", .bool false])
  let withOk (run : Lean.Json) : Lean.Json :=
    positive.setObjVal! "relations" (relations.setObjVal! "Program_ok" run)
  rejectsWith "changed value" "semantic outputs differ" (checkCase cfg g (withOk
    (ok.setObjVal! "result" (result.setObjVal! "outputs" (.arr #[changedValue])))))
  rejectsWith "changed counter" "fresh counter differs" (checkCase cfg g (withOk
    (ok.setObjVal! "counterAfter" (.num 1))))
  rejects "malformed output" (checkCase cfg g (withOk
    (ok.setObjVal! "result" (result.setObjVal! "outputs" .null))))
  rejectsWith "unsupported class" "malformed upstream result class" (checkCase cfg g (withOk
    (ok.setObjVal! "result" (result.setObjVal! "class" (.str "skip")))))
  rejects "malformed boot" (checkCase cfg g (positive.setObjVal! "boot" .null))
  rejectsWith "out-of-range counter" "outside the signed 63-bit" (checkCase cfg g (withOk
    (ok.setObjVal! "counterAfterBoot" (.num
      (Lean.JsonNumber.fromInt ((2 : Int) ^ 62))))))
  let syntaxRelations ← field syntaxCase "relations"
  let syntaxOk ← field syntaxRelations "Program_ok"
  let withSyntaxOk (run : Lean.Json) : Lean.Json :=
    syntaxCase.setObjVal! "relations" (syntaxRelations.setObjVal! "Program_ok" run)
  rejectsWith "syntax mode" "wrong interpreter mode" (checkCase cfg g
    (withSyntaxOk (syntaxOk.setObjVal! "mode" (.str "SL"))))
  rejectsWith "syntax guard" "guard must be disabled" (checkCase cfg g
    (withSyntaxOk (syntaxOk.setObjVal! "guard" (.bool true))))
  let boot ← Lang.Il.Json.value (← field positive "boot")
  let .error fuelError := checkRelation 0 cfg g boot "Program_ok" ok
    | throw "zero-fuel relation was accepted"
  unless fuelError == "Program_ok: Lean exhausted fuel (not an upstream unmatch)" do
    throw s!"zero-fuel relation was misclassified: {fuelError}"

end P4SpecTecTest.Diff.P4Interp

/-- Validate and replay the bounded full-P4 AL observations. -/
def main (args : List String) : IO UInt32 := do
  let some (path, testMutations) := (match args with
    | [path] => some (path, false)
    | [path, "--sensitivity"] => some (path, true)
    | _ => none)
    | IO.eprintln "usage: p4-interp-replay <bundle.json> [--sensitivity]"; return 1
  try
    let bundle ← P4SpecTec.Util.Yojson.readFile path
    let spec ← P4SpecTec.Lang.Al.Json.readSpec "exports/p4.al.json"
    let debug := (← IO.getEnv "P4SPECTEC_INTERP_DEBUG").isSome
    let .ok cfg := P4SpecTec.Interp_al.Interp.Config.withPrintHints
      ({ guard := false, debug, extern := P4SpecTecTest.Diff.P4Interp.placeholderExtern } :
        P4SpecTec.Interp_al.Interp.Config
        P4SpecTec.Prelude.StateEval) spec
      | IO.eprintln "[p4-interp] invalid print hints"; return 1
    let .ok globals := P4SpecTec.Interp_al.Interp.init spec
      | IO.eprintln "[p4-interp] full-P4 spec initialization failed"; return 1
    match P4SpecTecTest.Diff.P4Interp.check cfg globals bundle with
    | .error message => IO.eprintln s!"[p4-interp] {message}"; return 1
    | .ok lines =>
        for line in lines do IO.println s!"[p4-interp] {line}"
        if testMutations then
          match P4SpecTecTest.Diff.P4Interp.sensitivity cfg globals bundle with
          | .error message => IO.eprintln s!"[p4-interp] {message}"; return 1
          | .ok _ => IO.println "[p4-interp] nine Lean sensitivity mutations rejected"
        return 0
  catch e =>
    IO.eprintln s!"[p4-interp] {e}"
    return 1
