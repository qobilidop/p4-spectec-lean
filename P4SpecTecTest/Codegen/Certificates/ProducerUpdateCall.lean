import Lean.Elab.Command
import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.ProducerUpdateCall
import P4SpecTec.Refine.Representation.SourceCodec
import P4SpecTec.Refine.Representation.SourceExtern

/-! Actual source-checked recursive suffix input admission. -/

namespace NanoP4Spec.UpdaterCallFixture
open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Codegen

open Lean Elab Command in
run_cmd do
  let env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
  let some d := env.defs.find? (·.it.id.it == "update_fieldValue")
    | throwError "no actual updater"
  let proof ← match ProducerUpdateCall.declarations env d with
    | .ok proof => pure proof
    | .error message => throwError "{message}"
  for text in (render proof).splitOn "\n\n" do
    let command ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok command => pure command
      | .error message => throwError "{text}\n{message}"
    elabCommand command

end NanoP4Spec.UpdaterCallFixture
