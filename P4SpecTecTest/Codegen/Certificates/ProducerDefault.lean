import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.ProducerDefault

/-! Constructor producer selection rejects changed output and traversal roles. -/

namespace P4SpecTecTest.Codegen.ProducerDefault
open P4SpecTec P4SpecTec.Codegen P4SpecTec.Refine

private def env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
private def builder := NanoP4Spec.«$default».al

#guard (Codegen.ProducerDefault.plan env builder).isOk
#guard (Codegen.ProducerDefault.declarations env builder).isOk
#guard !(Codegen.ProducerDefault.plan { env with mode := .freshState } builder).isOk

private def clauses (f : Lang.Il.clause → Lang.Il.clause) : Lang.Al.def :=
  match builder.it with
  | .FuncDecD name types params result cs otherwise hints =>
    { builder with it := .FuncDecD name types params result (cs.map f) otherwise hints }
  | _ => builder

private def changedResult : Lang.Al.def := clauses fun c =>
  let (args, result, premises) := c.it
  let result := match result.it with
    | .UpCastE _ inner => { result with it := .UpCastE (Q.t .TextT) inner }
    | _ => result
  { c with it := (args, result, premises) }

#guard !(Codegen.ProducerDefault.plan env changedResult).isOk

private def missingStage : Lang.Al.def := clauses fun c =>
  let (args, result, premises) := c.it
  { c with it := (args, result, premises.take 4) }

#guard !(Codegen.ProducerDefault.plan env missingStage).isOk

private def unrelatedCall : Lang.Al.def := clauses fun c =>
  let (args, result, premises) := c.it
  let premises := premises.map fun p => match p.it with
    | .IterPr body iteration =>
      let body := match body.it with
        | .LetPr pattern value => match value.it with
          | .CallE _ ts args =>
            let value := { value with it := .CallE (Q.i "unrelated") ts args }
            { body with it := .LetPr pattern value }
          | _ => body
        | _ => body
      { p with it := .IterPr body iteration }
    | _ => p
  { c with it := (args, result, premises) }

#guard !(Codegen.ProducerDefault.plan env unrelatedCall).isOk
#guard (ProducerConstructor.declarations env "value" 10000 "impossible").isOk == false
#guard (ProducerConstructor.declarations env "pair" 0 "openParameters").isOk == false
#guard match Codegen.ProducerDefault.declarations env builder with
  | .error _ => false
  | .ok text => (text.splitOn "\n").all (fun line => line.length ≤ 100)

end P4SpecTecTest.Codegen.ProducerDefault
