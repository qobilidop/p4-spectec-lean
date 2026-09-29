import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.SourcePolymorphic

/-! Source-domain selection for polymorphic membership, projections, empty containers and choice. -/

namespace P4SpecTecTest.Codegen.SourcePolymorphic
open P4SpecTec P4SpecTec.Refine P4SpecTec.Codegen
open SourcePolymorphic

private def env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
private def selected := NanoP4Spec.spec.filter fun d =>
  ["in_set", "dom_map", "codom_map"].contains d.it.id.it
private def empty := NanoP4Spec.spec.filter fun d =>
  ["empty_set", "empty_map"].contains d.it.id.it
private def choice := NanoP4Spec.spec.filter fun d => d.it.id.it == "ite"

#guard selected.length == 3
#guard empty.length == 2
#guard choice.length == 1
#guard selected.all fun d => (declarations env d).isOk
#guard empty.all fun d => (declarations env d).isOk
#guard choice.all fun d => (declarations env d).isOk
#guard selected.all fun d => (declarations env d).toOption.any fun source =>
  (source.splitOn "\n").all (fun line => line.length ≤ 100)
#guard empty.all fun d => (declarations env d).toOption.any fun source =>
  (source.splitOn "\n").all (fun line => line.length ≤ 100)
#guard empty.all fun d => (plan env d).toOption.any (·.emptyContainer.isSome)
#guard choice.all fun d => (plan env d).toOption.any (·.booleanChoice)

private def renamed (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD _ parameters inputs result clauses fallback hints =>
    { d with it := .FuncDecD (Q.i "renamed") parameters inputs result clauses fallback hints }
  | _ => d

-- Selection follows source shape rather than one of the production callable names.
#guard selected.all fun d => (plan env (renamed d)).isOk
#guard empty.all fun d => (plan env (renamed d)).isOk
#guard choice.all fun d => (plan env (renamed d)).isOk
#guard selected.all fun d => !(plan { env with mode := .freshState } d).isOk
#guard empty.all fun d => !(plan { env with mode := .freshState } d).isOk
#guard choice.all fun d => !(plan { env with mode := .freshState } d).isOk

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

private def withoutParameters (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name _ inputs result clauses fallback hints =>
    { d with it := .FuncDecD name [] inputs result clauses fallback hints }
  | _ => d

private def duplicatedParameters (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name parameters inputs result clauses fallback hints =>
    { d with it :=
      .FuncDecD name (parameters ++ parameters) inputs result clauses fallback hints }
  | _ => d

#guard selected.all fun d => !(plan env (wrongOutput d)).isOk
#guard empty.all fun d => !(plan env (wrongOutput d)).isOk
#guard choice.all fun d => !(plan env (wrongOutput d)).isOk
#guard selected.all fun d => !(plan env (duplicatedClauses d)).isOk
#guard empty.all fun d => !(plan env (duplicatedClauses d)).isOk
#guard choice.all fun d => !(plan env (duplicatedClauses d)).isOk
#guard (selected ++ empty ++ choice).all fun d => !(plan env (withoutParameters d)).isOk
#guard (selected ++ empty ++ choice).all fun d => !(plan env (duplicatedParameters d)).isOk

private def wrongBody (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name parameters inputs result clauses fallback hints =>
    let clauses := clauses.map fun clause =>
      let (arguments, _, premises) := clause.it
      { clause with it := (arguments, Q.e (.BoolE true) .BoolT, premises) }
    { d with it := .FuncDecD name parameters inputs result clauses fallback hints }
  | _ => d

-- The same signature with a different producer must not receive the empty proof.
#guard empty.all fun d => !(plan env (wrongBody d)).isOk
#guard choice.all fun d => !(plan env (wrongBody d)).isOk

private def reversedClauses (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name parameters inputs result clauses fallback hints =>
    { d with it := .FuncDecD name parameters inputs result clauses.reverse fallback hints }
  | _ => d

-- A changed branch order is outside the proved source choice pattern.
#guard choice.all fun d => !(plan env (reversedClauses d)).isOk

private def repetition := NanoP4Spec.spec.find? (fun d => d.it.id.it == "repeat_")
#guard repetition.any fun d => (plan env d).isOk
#guard repetition.any fun d => (declarations env d).isOk
#guard repetition.any fun d => !(plan env (wrongOutput d)).isOk
#guard repetition.any fun d => !(plan env (duplicatedClauses d)).isOk
-- Merely renaming the declaration leaves the old recursive callee and must reject.
#guard repetition.any fun d => !(plan env (renamed d)).isOk

#guard repetition.any fun d => !(plan env (wrongBody d)).isOk
#guard repetition.any fun d => !(plan env (reversedClauses d)).isOk

private def renamedRepetition (d : Lang.Al.def) : Lang.Al.def := Id.run do
  let .FuncDecD _ parameters inputs result [base, step] fallback hints := d.it | return d
  let (arguments, output, premises) := step.it
  let .CatE head tail := output.it | return d
  let .CallE _ types actuals := tail.it | return d
  let tail := { tail with it := .CallE (Q.i "renamed") types actuals }
  let output := { output with it := .CatE head tail }
  let step := { step with it := (arguments, output, premises) }
  let definition : Lang.Al.def' :=
    .FuncDecD (Q.i "renamed") parameters inputs result [base, step] fallback hints
  return { d with it := definition }

-- Renaming the declaration and its actual recursive call preserves the source shape.
#guard repetition.any fun d => (plan env (renamedRepetition d)).isOk

private def unguardedRepetition (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name parameters inputs result [base, step] fallback hints =>
    let (arguments, output, premises) := step.it
    let step := { step with it := (arguments, output, premises.drop 1) }
    { d with it := .FuncDecD name parameters inputs result [base, step] fallback hints }
  | _ => d

#guard repetition.any fun d => !(plan env (unguardedRepetition d)).isOk

end P4SpecTecTest.Codegen.SourcePolymorphic
