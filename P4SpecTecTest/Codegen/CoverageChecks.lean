import Lean.Elab.Command
import P4SpecTec.Codegen.Coverage.Check
import NanoP4Spec

/-! Distinguishing mutations for compiled certificate inventory checks. -/

open Lean Elab Term
open P4SpecTec.Codegen.Coverage

namespace P4SpecTecTest.Codegen.CoverageChecks

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
  for (label, kind, direction) in
      [("reverse replaced by forward", "refinement", "generatedToReference"),
       ("dispatch replaced by invocation", "builtinContract", "twoWayDispatch"),
       ("source entry replaced by invocation", "sourceEntry", "sourceInputsToTwoWay"),
       ("producer replaced by invocation", "producer", "sourceInputsToSourceOutput")] do
    let some entry := report.definitions.find? fun candidate =>
        candidate.claims.any fun claim => claim.kind == kind && claim.direction == direction
      | throw <| IO.userError s!"coverage sensitivity requires {direction} evidence"
    let some expected := entry.claims.find? fun claim =>
        claim.kind == kind && claim.direction == direction
      | throw <| IO.userError s!"missing {direction} claim"
    let some forward := entry.claims.find? (·.direction == "referenceToGenerated")
      | throw <| IO.userError s!"missing forward claim for {entry.id}"
    expectRejected label "type mismatch" <| check { expected with name := forward.name }
  expectRejected "missing type inventory" "differs from current source" <|
    checkReport { report with representations := [] }
  expectRejected "missing source profile" "differs from current source" <|
    checkReport { report with profiles := [] }
  let some variables := report.profiles.find? (·.kind == "sourceVariables")
    | throw <| IO.userError "source-profile sensitivity requires variable omission evidence"
  expectRejected "variable omission replaced by unrelated theorem" "type mismatch" <|
    check { variables with name := baseClaim.name }
  let codecs := report.representations.flatMap (·.claims)
  let first :: second :: _ := codecs
    | throw <| IO.userError "representation sensitivity requires two source codec claims"
  expectRejected "codec replaced by another source family" "type mismatch" <|
    check { first with name := second.name }
  IO.println "[coverage] nineteen mutations rejected at their intended boundaries"

run_cmd do
  let env ← getEnv
  let report ← Check.checkFiles env "NanoP4Spec" "exports/nano-p4.al.json"
    "NanoP4Spec/coverage.json" { rawExternTypes := ["value"] }
  sensitivity env report

end P4SpecTecTest.Codegen.CoverageChecks
