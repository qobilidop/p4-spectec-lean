import Lean.Util.Path
import P4SpecTec.Codegen.Coverage.Check

/-!
Runtime validation of a generated library's coverage inventory against the current
export and compiled theorem environment: Nano-P4 by default, full P4 with `--full-p4`.
-/

open Lean Elab Term
open P4SpecTec.Codegen.Coverage

/-- A generated library whose coverage report is checked. -/
structure Target where
  /-- The library's root module and namespace. -/
  library : String
  /-- The export it is generated from. -/
  input : String
  /-- Runtime-only raw extern alternatives the library was generated with. -/
  rawExternTypes : List String := []

/-- The checked libraries, by command-line flag. -/
def target (fullP4 : Bool) : Target :=
  if fullP4 then { library := "P4Spec", input := "exports/p4.al.json" }
  else { library := "NanoP4Spec", input := "exports/nano-p4.al.json", rawExternTypes := ["value"] }

/-- Validate a library's compiled claims and optionally explain an entry point. -/
def runCoverageChecks (env : Environment) (fullP4 : Bool) (args : List String) : IO Unit := do
  let t := target fullP4
  let report ← Check.checkFiles env t.library t.input s!"{t.library}/coverage.json"
    { rawExternTypes := t.rawExternTypes }
  let count := ((report.definitions ++ report.representations).map (·.claims.length)).sum +
    report.profiles.length
  IO.println s!"[coverage] {t.library}: {report.definitions.length} callables; \
    {report.representations.length} types; {count} claims checked"
  if let some entryPoint := args.head? then
    match explain report entryPoint with
    | .ok text => IO.println text
    | .error error => throw <| IO.userError error

/-- Check coverage through Lean's ordinary elaboration frontend. -/
def main (args : List String) : IO UInt32 := do
  let fullP4 := args.contains "--full-p4"
  let args := args.filter (· != "--full-p4")
  if args.length > 1 || args.any (·.startsWith "-") then
    IO.eprintln "usage: check-coverage [--full-p4] [AL-entry-point]"
    return 2
  try
    -- Use Lean's ordinary frontend to initialize notation and elaborator extensions.
    -- The only interpolated text is a Lean-escaped list of strings, never raw source.
    let source := s!"import Tools.CheckCoverage\nimport {(target fullP4).library}\n" ++
      s!"run_cmd do\n  runCoverageChecks (← Lean.getEnv) {fullP4} " ++ reprStr args ++ "\n"
    let result ← IO.Process.output {
      cmd := ((← findSysroot) / "bin" / "lean").toString, args := #["--stdin"]
    } (some source)
    (← IO.getStdout).putStr result.stdout
    (← IO.getStderr).putStr result.stderr
    return result.exitCode
  catch error =>
    IO.eprintln s!"[coverage] {error}"
    return 1
