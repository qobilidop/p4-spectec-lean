import Lean.Elab.Command
import P4SpecTec.Lang.Al.Json
import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.ProducerComposition

/-! Source producer composition retains ordered, typed call dependencies. -/

namespace P4SpecTecTest.Codegen.ProducerComposition
open P4SpecTec P4SpecTec.Codegen

private def env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
private def relation := NanoP4Spec.Var_init.al

#guard match Codegen.ProducerComposition.dependencies env relation with
  | .ok names => names == ["default", "add_var_e"]
  | .error _ => false
#guard (Codegen.ProducerComposition.declarations env relation).isOk
#guard (Codegen.ProducerComposition.callAdmissionDeclarations env relation).isOk
-- The second call's inputs need only the first call's success, never the current call's success.
#guard (Codegen.ProducerComposition.callAdmissionType env relation).toOption.any fun statement =>
  (statement.splitOn "«$default»").length == 2 &&
    (statement.splitOn "«$add_var_e»").length == 1 &&
    (statement.splitOn "some (.ok").length == 2

private def paths (change : Lang.Al.rulepath → Lang.Al.rulepath) : Lang.Al.def :=
  match relation.it with
  | .RelD name shape modes groups alternative hints =>
    let groups := groups.map fun group =>
      let (name, inputs, paths) := group.it
      { group with it := (name, inputs, paths.map change) }
    { relation with it := .RelD name shape modes groups alternative hints }
  | _ => relation

private def reversed := paths fun (name, premises, outputs) => (name, premises.reverse, outputs)
private def missing := paths fun (name, premises, outputs) => (name, premises.drop 1, outputs)
private def duplicated := paths fun (name, premises, outputs) =>
  (name, premises ++ premises, outputs)

#guard !(Codegen.ProducerComposition.plan env reversed).isOk
#guard !(Codegen.ProducerComposition.plan env missing).isOk
#guard !(Codegen.ProducerComposition.plan env duplicated).isOk
#guard !(Codegen.ProducerComposition.plan { env with mode := .freshState } relation).isOk
#guard match Codegen.ProducerComposition.declarations env relation with
  | .error _ => false
  | .ok text => (text.splitOn "\n").all (fun line => line.length ≤ 100)

-- Production decoding retains the input hint that quotation normalization erases.
open Lean Elab Command in
run_cmd do
  let root ← IO.currentDir
  let decoded ← Lang.Al.Json.readSpec (root / "exports/nano-p4.al.json").toString
  let some actual := decoded.find? (fun d => d.it.id.it == "Var_init")
    | throwError "actual Var_init declaration is missing"
  let .RelD _ _ _ _ _ hints := actual.it | throwError "actual Var_init is not a relation"
  if hints.isEmpty then throwError "regression no longer exercises retained source hints"
  let decodedEnv := Env.ofSpec "NanoP4Spec" decoded
  let result := Codegen.ProducerComposition.dependencies decodedEnv actual
  unless result.toOption == some ["default", "add_var_e"] do
    throwError "hinted source composition differs: {repr result}"
  unless (Codegen.ProducerComposition.declarations decodedEnv actual).isOk do
    throwError "hinted source composition cannot be emitted"

end P4SpecTecTest.Codegen.ProducerComposition
