import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.SourcePolymorphic

/-! Source-domain selection for actual polymorphic membership and component projection. -/

namespace P4SpecTecTest.Codegen.SourcePolymorphic
open P4SpecTec P4SpecTec.Refine P4SpecTec.Codegen
open SourcePolymorphic

private def env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
private def selected := NanoP4Spec.spec.filter fun d =>
  ["in_set", "dom_map", "codom_map"].contains d.it.id.it

#guard selected.length == 3
#guard selected.all fun d => (declarations env d).isOk
#guard selected.all fun d => (declarations env d).toOption.any fun source =>
  (source.splitOn "\n").all (fun line => line.length ≤ 100)

private def renamed (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD _ parameters inputs result clauses fallback hints =>
    { d with it := .FuncDecD (Q.i "renamed") parameters inputs result clauses fallback hints }
  | _ => d

-- Selection follows source shape rather than one of the production callable names.
#guard selected.all fun d => (plan env (renamed d)).isOk
#guard selected.all fun d => !(plan { env with mode := .freshState } d).isOk

private def wrongOutput (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name parameters inputs _ clauses fallback hints =>
    { d with it := .FuncDecD name parameters inputs (Q.t .TextT) clauses fallback hints }
  | _ => d

private def duplicatedClauses (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name parameters inputs result clauses fallback hints =>
    { d with it := .FuncDecD name parameters inputs result (clauses ++ clauses) fallback hints }
  | _ => d

#guard selected.all fun d => !(plan env (wrongOutput d)).isOk
#guard selected.all fun d => !(plan env (duplicatedClauses d)).isOk

end P4SpecTecTest.Codegen.SourcePolymorphic
