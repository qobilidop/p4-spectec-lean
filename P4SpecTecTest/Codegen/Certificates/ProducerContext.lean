import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.ProducerContext

/-! Exact source-role selection for context map insertion and local list-tail removal. -/

namespace P4SpecTecTest.Codegen.ProducerContexts

open P4SpecTec P4SpecTec.Codegen P4SpecTec.Refine

private def env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
private def exit := NanoP4Spec.«$exit_e».al
private def insert := NanoP4Spec.«$add_var_e».al

#guard (ProducerContexts.exitPlan env exit).isOk
#guard (ProducerContexts.insertPlan env insert).isOk
#guard match ProducerContexts.insertPlan env insert with
  | .ok p => p.frame.name == "frame" && p.frame.map == "map" &&
      p.frame.set == "set" && p.frame.pair == "pair" &&
      p.scopeConstructors == ["GLOBAL", "BLOCK", "LOCAL"] &&
      p.domain == "dom_map" && p.membership == "in_set" && p.insertion == "add_map"
  | .error _ => false

private def clauses (d : Lang.Al.def)
    (f : List Lang.Il.clause → List Lang.Il.clause) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name params inputs result cs otherwise hints =>
    { d with it := .FuncDecD name params inputs result (f cs) otherwise hints }
  | _ => d

private def renamed (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD _ params inputs result cs otherwise hints =>
    { d with it := (.FuncDecD (Q.i "renamed_context_producer")
        params inputs result cs otherwise hints) }
  | _ => d

-- Callable names are source roles; clause priority and guards are proof boundaries.
#guard (ProducerContexts.exitPlan env (renamed exit)).isOk
#guard (ProducerContexts.insertPlan env (renamed insert)).isOk
#guard (ProducerContexts.insertPlan env (clauses insert List.reverse)).isOk == false
#guard (ProducerContexts.exitPlan env (clauses exit fun cs => cs.map fun c =>
  { c with it := (c.it.1, c.it.2.1, c.it.2.2.reverse) })).isOk == false
#guard (ProducerContexts.insertPlan env (clauses insert fun cs => cs.map fun c =>
  { c with it := (c.it.1, c.it.2.1, c.it.2.2 ++ c.it.2.2) })).isOk == false
#guard (ProducerContexts.insertPlan env (clauses insert fun cs => cs.map fun c =>
  { c with it := (c.it.1, c.it.2.1, []) })).isOk == false

private def alterResult (d : Lang.Al.def) : Lang.Al.def :=
  clauses d fun cs => cs.map fun c =>
    { c with it := (c.it.1, Q.e (.VarE (Q.i "unbound_output")) c.it.2.1.note, c.it.2.2) }

#guard (ProducerContexts.exitPlan env (alterResult exit)).isOk == false
#guard (ProducerContexts.insertPlan env (alterResult insert)).isOk == false
#guard (ProducerContexts.exitPlan { env with mode := .freshState } exit).isOk == false
#guard (ProducerContexts.insertPlan
  { env with representation.rawExternTypes := ["frame"] } insert).isOk == false

private def wrongTypeArguments : Lang.Al.def :=
  clauses insert fun cs => cs.map fun c =>
    let (args, result, premises) := c.it
    let premises := premises.map fun p => match p.it with
      | .LetPr target call => match call.it with
        | .CallE name types inputs =>
          { p with it := .LetPr target { call with it := .CallE name types.reverse inputs } }
        | _ => p
      | _ => p
    { c with it := (args, result, premises) }

private def wrongUpdateField : Lang.Al.def :=
  clauses insert fun cs => cs.map fun c =>
    let (args, result, premises) := c.it
    let premises := premises.map fun p => match p.it with
      | .LetPr target update => match update.it with
        | .UpdE base path value => match path.it with
          | .DotP parent _ =>
            { p with it := .LetPr target { update with it :=
                (.UpdE base { path with it := .DotP parent (Q.a (.Keyword "UNKNOWN")) } value) } }
          | _ => p
        | _ => p
      | _ => p
    { c with it := (args, result, premises) }

#guard (ProducerContexts.insertPlan env wrongTypeArguments).isOk == false
#guard (ProducerContexts.insertPlan env wrongUpdateField).isOk == false

end P4SpecTecTest.Codegen.ProducerContexts
