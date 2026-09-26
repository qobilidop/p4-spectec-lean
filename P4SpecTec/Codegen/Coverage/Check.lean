import Lean.Elab.Term
import Lean.Elab.Extra
import Lean.Elab.BuiltinNotation
import Lean.Elab.SyntheticMVars
import Lean.Util.CollectAxioms
import Lean.Util.Sorry
import P4SpecTec.Codegen.Emit
import P4SpecTec.Codegen.Coverage
import P4SpecTec.Lang.Al.Json
import P4SpecTec.Tactic.Audit

/-!
Validate coverage metadata against a freshly generated report and compiled
theorem declarations. Metadata carries no cached validation verdict. The
checker is independent of any particular generated library.
-/

namespace P4SpecTec.Codegen.Coverage.Check

open Lean Elab Term Meta

/-- Check a compiled theorem's expected type and complete allowed-axiom closure.
The caller supplies the generated namespace and ordinary proof-support opens. -/
def checkClaim (claim : Claim) : TermElabM Unit := withoutErrToSorry do
  let env ← getEnv
  let nameSyntax ← match Parser.runParserCategory env `term claim.name with
    | .ok stx => pure stx
    | .error msg => throwError "invalid coverage theorem name {claim.name}: {msg}"
  unless nameSyntax.isIdent do
    throwError "coverage theorem name is not an identifier: {claim.name}"
  let name := nameSyntax.getId
  let some (.thmInfo info) := env.find? name
    | throwError "coverage claim is not a compiled theorem: {claim.name}"
  let typeSyntax ← match Parser.runParserCategory env `term claim.expectedType with
    | .ok stx => pure stx
    | .error msg => throwError "invalid coverage type for {claim.name}: {msg}"
  let expected ← elabType typeSyntax
  synthesizeSyntheticMVarsNoPostponing
  let expected ← instantiateMVars expected
  if expected.hasMVar || expected.hasFVar || expected.hasSorry then
    throwError "coverage type is not closed and fully elaborated: {claim.name}"
  let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let actual := info.type.instantiateLevelParams info.levelParams levels
  unless ← isDefEq actual expected do
    throwError "coverage theorem type mismatch: {claim.name}"
  let axioms ← collectAxioms name
  let forbidden := axioms.filter fun ax => !P4SpecTec.Tactic.allowedAxioms.contains ax
  unless forbidden.isEmpty do
    throwError "coverage theorem has forbidden axioms: {claim.name}: {forbidden.toList}"

/-- Reject stale or forged metadata before checking any compiled declaration. -/
def checkReport (stored regenerated : Report) : TermElabM Unit := do
  unless stored == regenerated do
    throwError "coverage report differs from current source/planner output"
  unless stored.schemaVersion == 1 do
    throwError "unsupported coverage schema: {stored.schemaVersion}"
  for entry in stored.definitions do
    for claim in entry.claims do
      checkClaim claim

/-- Run a checker action under the generated library's proof elaboration context. -/
def inEnvironment (env : Environment) (library : String) (action : TermElabM α) : IO α := do
  let context : Core.Context := {
    fileName := "<coverage>"
    fileMap := FileMap.ofString ""
    currNamespace := library.toName
    openDecls := [.simple `P4SpecTec [], .simple `P4SpecTec.Prelude [],
      .simple `P4SpecTec.Refine []]
    options := ({} : Options).set `maxRecDepth (10000 : Nat)
      |>.set `maxHeartbeats (4000000 : Nat)
  }
  let (result, state) ← ((action.run').run').toIO context { env }
  if state.messages.hasErrors then
    throw <| IO.userError "coverage elaboration produced errors"
  return result

/-- Recompute metadata from the actual export, then check the compiled environment.
Only canonical generated JSON is accepted, including its schema and every entry. -/
def checkFiles (env : Environment) (library input reportPath : String) : IO Report := do
  let spec ← Lang.Al.Json.readSpec input
  let regenerated ← match Emit.coverage library input spec with
    | .ok report => pure report
    | .error msg => throw <| IO.userError msg
  let text ← IO.FS.readFile reportPath
  unless text == regenerated.render do
    throw <| IO.userError "coverage report differs from current source/planner output"
  let json ← match Json.parse text with
    | .ok json => pure json
    | .error msg => throw <| IO.userError msg
  let stored ← match fromJson? json with
    | .ok report => pure report
    | .error msg => throw <| IO.userError msg
  inEnvironment env library (checkReport stored regenerated)
  return regenerated

end P4SpecTec.Codegen.Coverage.Check
