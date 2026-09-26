import Lean.Util.Path
import P4SpecTec.Codegen.Coverage.Check
import NanoP4Spec

/-!
Runtime validation of Nano's generated coverage inventory against the current
export and compiled theorem environment, with fail-closed sensitivity checks.
-/

set_option linter.missingDocs false

open Lean Elab Term
open P4SpecTec.Codegen.Coverage

private def expectRejected (label diagnostic : String) (action : IO Unit) : IO Unit := do
  let failure ← try action; pure none catch e => pure (some e.toString)
  let some message := failure
    | throw <| IO.userError s!"coverage mutation accepted: {label}"
  unless (message.splitOn diagnostic).length > 1 do
    throw <| IO.userError s!"coverage mutation failed unexpectedly ({label}): {message}"

private def baseClaim : Claim := {
  name := "Nat.add_comm", kind := "test", direction := "test"
  expectedType := "∀ n m : Nat, n + m = m + n"
}

private def sensitivity (env : Environment) (report : Report) : IO Unit := do
  let check := fun claim => Check.inEnvironment env "NanoP4Spec" (Check.checkClaim claim)
  check baseClaim
  expectRejected "missing theorem" "not a compiled theorem" <|
    check { baseClaim with name := "CoverageMissing.theorem" }
  expectRejected "unrelated theorem" "type mismatch" <|
    check { baseClaim with name := "Nat.add_assoc" }
  expectRejected "wrong expected type" "type mismatch" <|
    check { baseClaim with expectedType := "False" }
  expectRejected "non-theorem" "not a compiled theorem" <|
    check { baseClaim with name := "Nat.add" }
  expectRejected "unresolved expected type" "not closed" <|
    check { baseClaim with expectedType := "_" }
  expectRejected "forbidden axiom" "forbidden axioms" <|
    Check.inEnvironment env "NanoP4Spec" do
      addDecl <| .axiomDecl {
        name := `CoverageMutation.assumption, levelParams := []
        type := mkConst ``True, isUnsafe := false
      }
      addDecl <| .thmDecl {
        name := `CoverageMutation.theorem, levelParams := []
        type := mkConst ``True, value := mkConst `CoverageMutation.assumption
      }
      Check.checkClaim { baseClaim with
        name := "CoverageMutation.theorem", expectedType := "True" }
  let checkReport := fun mutated =>
    Check.inEnvironment env "NanoP4Spec" (Check.checkReport mutated report)
  expectRejected "missing inventory" "differs from current source" <|
    checkReport { report with definitions := [] }
  expectRejected "forged schema" "differs from current source" <|
    checkReport { report with schemaVersion := report.schemaVersion + 1 }
  let some entry := report.definitions.find? fun entry => !entry.claims.isEmpty
    | throw <| IO.userError "coverage sensitivity requires a real emitted claim"
  let forged := { entry with claims := entry.claims.map fun claim =>
    { claim with expectedType := "True" } }
  expectRejected "forged expected types" "differs from current source" <|
    checkReport { report with definitions := report.definitions.map fun candidate =>
      if candidate.id == entry.id then forged else candidate }
  expectRejected "omitted claims" "differs from current source" <|
    checkReport { report with definitions := report.definitions.map fun candidate =>
      if candidate.id == entry.id then { candidate with claims := [] } else candidate }
  expectRejected "forged direction" "differs from current source" <|
    checkReport { report with definitions := report.definitions.map fun candidate =>
      { candidate with claims := candidate.claims.map fun claim =>
        { claim with direction := "reverse" } } }
  IO.println "[coverage] eleven mutations rejected at their intended boundaries"

def runCoverageChecks (env : Environment) (args : List String) : IO Unit := do
  let report ← Check.checkFiles env "NanoP4Spec" "exports/nano-p4.al.json"
    "NanoP4Spec/coverage.json"
  let count := (report.definitions.map (·.claims.length)).sum
  IO.println s!"[coverage] {report.definitions.length} definitions; {count} claims checked"
  sensitivity env report
  if let some entryPoint := args.head? then
    match explain report entryPoint with
    | .ok text => IO.println text
    | .error error => throw <| IO.userError error

def main (args : List String) : IO UInt32 := do
  if args.length > 1 then
    IO.eprintln "usage: check-coverage [AL-entry-point]"
    return 2
  try
    -- Use Lean's ordinary frontend to initialize notation and elaborator extensions.
    -- The only interpolated text is a Lean-escaped list of strings, never raw source.
    let source := "import P4SpecTecTest.Coverage.Main\n" ++
      "run_cmd do\n  runCoverageChecks (← Lean.getEnv) " ++ reprStr args ++ "\n"
    let result ← IO.Process.output {
      cmd := ((← findSysroot) / "bin" / "lean").toString, args := #["--stdin"]
    } (some source)
    (← IO.getStdout).putStr result.stdout
    (← IO.getStderr).putStr result.stderr
    return result.exitCode
  catch error =>
    IO.eprintln s!"[coverage] {error}"
    return 1
