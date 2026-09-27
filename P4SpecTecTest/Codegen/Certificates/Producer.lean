import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.Producer

/-! Source updater selection checks ordered control flow and exact constructor roles. -/

namespace P4SpecTecTest.Codegen.ProducerCertificates
open P4SpecTec P4SpecTec.Codegen P4SpecTec.Refine

private def env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
private def updater := NanoP4Spec.«$update_fieldValue».al

#guard (Producer.updatePlan env updater).isOk
#guard (Producer.declarations env updater).isOk
#guard (Producer.updatePlan { env with mode := .freshState } updater).isOk == false
#guard (Producer.updatePlan
  { env with representation.rawExternTypes := ["fieldValue"] } updater).isOk == false

private def clauses (f : List Lang.Il.clause → List Lang.Il.clause) : Lang.Al.def :=
  match updater.it with
  | .FuncDecD name types params result cs otherwise hints =>
    { updater with it := .FuncDecD name types params result (f cs) otherwise hints }
  | _ => updater

-- Clause priority, the equality test and every recursive argument are proof boundaries.
#guard (Producer.updatePlan env (clauses List.reverse)).isOk == false
#guard (Producer.updatePlan env (clauses fun cs => cs.map fun c =>
  { c with it := (c.it.1, c.it.2.1, []) })).isOk == false
#guard (Producer.updatePlan env (clauses fun cs => cs.map fun c =>
  { c with it := (c.it.1, c.it.2.1, c.it.2.2 ++ c.it.2.2) })).isOk == false

private def renamed : Lang.Al.def :=
  match updater.it with
  | .FuncDecD _ types params result cs otherwise hints =>
    let name := Q.i "renamed_first_match"
    let cs := cs.map fun c =>
      let (args, body, premises) := c.it
      let body := match body.it with
        | .ConsE head tail => match tail.it with
          | .CallE _ ts args =>
            { body with it := .ConsE head { tail with it := .CallE name ts args } }
          | _ => body
        | _ => body
      { c with it := (args, body, premises) }
    { updater with it := .FuncDecD name types params result cs otherwise hints }
  | _ => updater

-- Selection uses roles in the source operation, never a callable-name whitelist.
#guard (Producer.updatePlan env renamed).isOk

private def alteredTail : Lang.Al.def :=
  clauses fun cs => cs.map fun c =>
    let (args, body, premises) := c.it
    let body := match body.it with
      | .ConsE head tail => match tail.it with
        | .CallE name ts recursiveArgs =>
          let changed := { tail with it := .CallE name ts recursiveArgs.reverse }
          { body with it := .ConsE head changed }
        | _ => body
      | _ => body
    { c with it := (args, body, premises) }

#guard (Producer.updatePlan env alteredTail).isOk == false
#guard match Producer.declarations env updater with
  | .error _ => false
  | .ok text => (text.splitOn "\n").all (fun line => line.length ≤ 100)

#guard (Producer.theoremType env NanoP4Spec.Var_init.al).isOk

private def relationModes (positions : List Int) : Lang.Al.def :=
  let relation := NanoP4Spec.Var_init.al
  match relation.it with
  | .RelD name sourceNotation _ groups alternative hints =>
    { relation with it := .RelD name sourceNotation positions groups alternative hints }
  | _ => relation

#guard !(Producer.theoremType env (relationModes [0, 1])).isOk
-- All arguments are inputs: the declared result is the supported empty tuple/Unit.
#guard (Producer.theoremType env (relationModes [0, 1, 2, 3])).isOk
#guard !(Producer.theoremType env (relationModes [0, 1, 1])).isOk
#guard !(Producer.theoremType env (relationModes [-1, 1, 2])).isOk
#guard !(Producer.theoremType env (relationModes [0, 1, 100])).isOk

end P4SpecTecTest.Codegen.ProducerCertificates
