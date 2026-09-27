import Lean.Elab.Command
import P4SpecTecTest.Codegen.Certificates.ProducerContextProof
import P4SpecTec.Codegen.Certificates.ProducerContextCall

/-! Complete actual context insertion call argument admission. -/

namespace NanoP4Spec.ContextCallFixture
open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Codegen

open Lean Elab Command in
run_cmd do
  let env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
  let some d := env.defs.find? (·.it.id.it == "add_var_e") | throwError "no actual insertion"
  let known := fun name => if name == "nameIR" then some
    ({ nominal := { codec := "NanoP4Spec.nameIR.codec", admitted := "fun _ => True" },
       proof := "NanoP4Spec.nameIR.admittedAll" } : RepresentationTotals.TotalContract) else none
  if (ProducerContextCall.declarations env d (fun _ => none)).isOk then
    throwError "missing independent key totality was accepted"
  let proof ← match ProducerContextCall.declarations env d known with
    | .ok proof => pure proof
    | .error message => throwError "{message}"
  let emitted := render proof
  unless (emitted.splitOn "«$add_var_e».callInputsSource").length == 2 do
    throwError "missing unique fixture projection proof reference"
  let emitted := emitted.replace "«$add_var_e».callInputsSource"
    "NanoP4Spec.ContextProofFixture.«$add_var_e».callInputsSource"
  for text in emitted.splitOn "\n\n" do
    let command ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok command => pure command
      | .error message => throwError "{text}\n{message}"
    elabCommand command

end NanoP4Spec.ContextCallFixture
