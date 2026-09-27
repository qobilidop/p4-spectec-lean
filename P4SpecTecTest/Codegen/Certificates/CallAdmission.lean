import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.CallAdmission

/-! Actual call input types, relation modes and signature-note mutations. -/

namespace P4SpecTecTest.Codegen.CallAdmission

open P4SpecTec P4SpecTec.Codegen P4SpecTec.Refine

private def env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec

#guard match Codegen.CallAdmission.argumentTypes env NanoP4Spec.«$default».al with
  | .ok [t] => Types.typEq t.it (Q.varT "typeIR" [])
  | _ => false
#guard match Codegen.CallAdmission.argumentTypes env NanoP4Spec.Type_eq.al with
  | .ok [t] => Types.typEq t.it (Q.varT "parameterIR" [])
  | _ => false
#guard !(Codegen.CallAdmission.plan env NanoP4Spec.«$default».al (fun _ => none)).isOk

private def actualCaller := NanoP4Spec.«$find_typeDef_t».al
#guard (Codegen.CallAdmission.argumentTypes env actualCaller).isOk

private def changedSignature :=
  match env.funcs["find_map"]? with
  | none => env
  | some info => { env with funcs := env.funcs.insert "find_map" { info with tparams := [] } }

#guard !(Codegen.CallAdmission.argumentTypes changedSignature actualCaller).isOk

private def changedArgument :=
  match env.funcs["find_map"]? with
  | none => env
  | some info =>
    let changed := { info with params := [.ExpP (Q.t .BoolT), .ExpP (Q.t .BoolT)] }
    { env with funcs := env.funcs.insert "find_map" changed }

#guard !(Codegen.CallAdmission.argumentTypes changedArgument actualCaller).isOk

private def changedModes :=
  match env.rels["ParameterType_eq"]? with
  | none => env
  | some info =>
    { env with rels := env.rels.insert "ParameterType_eq" { info with inputs := [100] } }

#guard !(Codegen.CallAdmission.argumentTypes changedModes NanoP4Spec.Type_eq.al).isOk

end P4SpecTecTest.Codegen.CallAdmission
