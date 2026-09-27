import Lean.Elab.Command
import NanoP4Spec.Refinement.Representation.evalContext
import P4SpecTec.Codegen.Certificates.ProducerContextProof
import P4SpecTec.Codegen.Funcs
import P4SpecTec.Refine.ProducerMap
import P4SpecTec.Refine.Producer

/-! Actual source-selected context insertion and list-tail exit certificates. -/

namespace NanoP4Spec
open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Codegen

open Lean Elab Command in
run_cmd do
  let env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
  for (name, renamed) in [("add_var_e", false), ("exit_e", false),
      ("add_var_e", true), ("exit_e", true)] do
    let some original := env.defs.find? (·.it.id.it == name) | throwError "no callable"
    let d := if renamed then
      match original.it with
      | .FuncDecD _ ts ps t cs ec hints =>
        { original with it := .FuncDecD (Q.i ("renamed_" ++ name)) ts ps t cs ec hints }
      | _ => original
      else original
    if renamed then
      let .FuncDecD i ts ps t cs ec _ := d.it | throwError "not a function"
      let native ← match Funcs.funcDecl { env } false false i.it
          (ts.map (·.it)) (ps.map (·.it)) t.it cs ec with
        | .ok native => pure native
        | .error message => throwError "{message}"
      let command ← match Parser.runParserCategory (← getEnv) `command
          (render native) with
        | .ok command => pure command
        | .error message => throwError "{message}"
      elabCommand command
    let proof ← match ProducerContextProof.declarations env d with
      | .ok proof => pure proof
      | .error message => throwError "{message}"
    for text in ["namespace ContextProofFixture"] ++
        (render proof).splitOn "\n\n" ++ ["end ContextProofFixture"] do
      let command ← match Parser.runParserCategory (← getEnv) `command text with
        | .ok command => pure command
        | .error message => throwError "{text}\n{message}"
      elabCommand command

end NanoP4Spec
