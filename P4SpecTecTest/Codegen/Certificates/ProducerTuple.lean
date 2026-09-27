import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.ProducerTotal
import P4SpecTec.Prelude.Eval
import P4SpecTec.Refine.Representation.SourceTuple
import P4SpecTec.Refine.Representation.SourceExtern

/-! Closed positional tuple output dictionaries and zero-output relation producer certificates. -/

namespace P4SpecTecTest.Codegen.ProducerTuple

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Codegen

def spec : Lang.Al.spec := []
private def env := Env.ofSpec "P4SpecTecTest.Codegen.ProducerTuple" spec
private def pairType : Lang.Il.typ' := .TupleT
  [Q.t (.IterT (Q.t .BoolT) .List), Q.t (.IterT (Q.t (.NumT .IntT)) .List)]
private def declaration (name : String) (result : Lang.Il.typ') : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i name) [] [Q.p (.ExpP (Q.t .BoolT))] (Q.t result) [] none [])
private def relation : Lang.Al.def :=
  Q.d (.RelD (Q.i "ZeroOutput") (Q.nt (.Arg (Q.t .BoolT))) [0] [] none [])

def «$pair» (_ : Bool) : Option (Except Fail (List Bool × List Int)) :=
  some (.ok ([true], [1]))
def «$optionalPair» (_ : Bool) : Option (Except Fail (Option (List Bool × List Int))) :=
  some (.ok (some ([true], [1])))
def ZeroOutput.run (_ : Bool) : Option (Except Fail Unit) := some (.ok ())

#guard (ProducerTotal.plan env (declaration "pair" pairType) (fun _ => none)).isOk
#guard (ProducerTotal.plan env (declaration "optionalPair" (.IterT (Q.t pairType) .Opt))
  (fun _ => none)).isOk
#guard (ProducerTotal.plan env relation (fun _ => none)).isOk

private def hiddenProduct : Lang.Al.def :=
  Q.d (.TypD (Q.i "hidden") [] (Q.dt (.PlainT (Q.t pairType))) [])
private def aliasEnv := Env.ofSpec "AliasTuple" [hiddenProduct]
private def badType : Lang.Il.typ := Q.t (.TupleT [Q.t .BoolT, Q.t (Q.varT "hidden" [])])

-- A closed right product would be flattened by ambient ToValues and must fail closed.
#guard (RepresentationFields.resolve aliasEnv (fun _ => none) badType).isOk == false
#guard (Producer.encoder aliasEnv badType).isOk == false
#guard (RepresentationFields.resolve env (fun _ => none)
  (Q.t (.TupleT [Q.t .BoolT]))).isOk == false
#guard (RepresentationFields.resolve env (fun _ => none)
  (Q.t (.TupleT [Q.t .BoolT, Q.t .BoolT, Q.t .BoolT]))).isOk == false

open Lean Elab Command in
run_cmd do
  for declaration in [declaration "pair" pairType,
      declaration "optionalPair" (.IterT (Q.t pairType) .Opt), relation] do
    let plan ← match ProducerTotal.plan env declaration (fun _ => none) with
      | .ok plan => pure plan
      | .error message => throwError "{message}"
    unless (plan.declarations.splitOn "\n").all (fun line => line.length ≤ 100) do
      throwError "tuple producer exceeds the line limit"
    for source in plan.declarations.splitOn "\n#audit_axioms" do
      let source := if source.startsWith "/--" then source else "#audit_axioms" ++ source
      let command ← match Parser.runParserCategory (← getEnv) `command source with
        | .ok command => pure command
        | .error message => throwError "{source}\n{message}"
      elabCommand command

end P4SpecTecTest.Codegen.ProducerTuple
