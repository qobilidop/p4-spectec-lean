import Lean.Util.Path
import P4SpecTec.Codegen.Coverage.Check

/-!
Runtime validation of Nano's generated coverage inventory against the current
export and compiled theorem environment.
-/

open Lean Elab Term
open P4SpecTec.Codegen.Coverage

/-- Validate compiled Nano claims and optionally explain an entry point. -/
def runCoverageChecks (env : Environment) (args : List String) : IO Unit := do
  let report ← Check.checkFiles env "NanoP4Spec" "exports/nano-p4.al.json"
    "NanoP4Spec/coverage.json" { rawExternTypes := ["value"] }
  let count := (report.definitions.map (·.claims.length)).sum
  IO.println s!"[coverage] {report.definitions.length} definitions; {count} claims checked"
  if let some entryPoint := args.head? then
    match explain report entryPoint with
    | .ok text => IO.println text
    | .error error => throw <| IO.userError error

/-- Check coverage through Lean's ordinary elaboration frontend. -/
def main (args : List String) : IO UInt32 := do
  if args.length > 1 then
    IO.eprintln "usage: check-coverage [AL-entry-point]"
    return 2
  try
    -- Use Lean's ordinary frontend to initialize notation and elaborator extensions.
    -- The only interpolated text is a Lean-escaped list of strings, never raw source.
    let source := "import Tools.CheckCoverage\nimport NanoP4Spec\n" ++
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
