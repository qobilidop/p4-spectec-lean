import Lean.Elab.Command
import NanoP4Spec.Refinement.exists_
import NanoP4Spec.Refinement.forall_
import P4SpecTec.Codegen.Certificates.SourceEntry
import P4SpecTec.Refine.Representation.SourceExtern

/-! Full source input lifting for actual recursive Nano Boolean traversals. -/

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Codegen P4SpecTec.Refine

namespace NanoP4Spec

open Lean Elab Command in
run_cmd do
  let env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
  for declaration in [NanoP4Spec.«$exists_».al, NanoP4Spec.«$forall_».al] do
    let member ← match Props.memberOf { env } declaration with
      | .ok member => pure member
      | .error message => throwError "{message}"
    let output ← match SourceEntry.declarations env declaration member with
      | .ok output => pure output
      | .error message => throwError "{message}"
    for text in (output.pretty.replace "sourceCorrespondence" "testSourceCorrespondence").splitOn
        "\n\n" do
      let command ← match Parser.runParserCategory (← getEnv) `command text with
        | .ok command => pure command
        | .error message => throwError "{text}\n{message}"
      elabCommand command

/-- info: 'NanoP4Spec.«$exists_».testSourceCorrespondence' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms «$exists_».testSourceCorrespondence

end NanoP4Spec
