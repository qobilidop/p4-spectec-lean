import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.ProducerTotal
import P4SpecTec.Prelude.Eval
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Tactic.Audit

/-! Total-output producers require proof of every admitted result carrier. -/

namespace P4SpecTecTest.Codegen.ProducerTotal

open P4SpecTec P4SpecTec.Refine P4SpecTec.Prelude
open P4SpecTec.Codegen (Env)

def spec : Lang.Al.spec := []
abbrev Eval := ExceptT Fail Option
def «$constant» (_ : Bool) : Eval Bool := pure false

private def declaration (result : Lang.Il.typ') :=
  Q.d (.FuncDecD (Q.i "constant") [] [Q.p (.ExpP (Q.t .BoolT))]
    (Q.t result) [] none [])

private def env := Env.ofSpec "P4SpecTecTest.Codegen.ProducerTotal" spec

#guard (Codegen.ProducerTotal.plan env (declaration .BoolT) (fun _ => none)).isOk
#guard !(Codegen.ProducerTotal.plan env (declaration (Q.varT "missing" []))
  (fun _ => none)).isOk
#guard !(Codegen.ProducerTotal.plan { env with mode := .freshState }
  (declaration .BoolT) (fun _ => none)).isOk

open Lean Elab Command in
run_cmd do
  let plan ← match Codegen.ProducerTotal.plan env (declaration .BoolT) (fun _ => none) with
    | .ok plan => pure plan
    | .error message => throwError "{message}"
  for source in plan.declarations.splitOn "\n#audit_axioms" do
    let source := if source.startsWith "/--" then source else "#audit_axioms" ++ source
    let command ← match Parser.runParserCategory (← getEnv) `command source with
      | .ok command => pure command
      | .error message => throwError "{source}\n{message}"
    elabCommand command

end P4SpecTecTest.Codegen.ProducerTotal
