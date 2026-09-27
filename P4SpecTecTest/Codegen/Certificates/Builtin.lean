import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.Builtin

/-! Builtin certificate selection rejects source-signature drift and keeps output bounded. -/

namespace P4SpecTecTest.Codegen.BuiltinCertificates

open P4SpecTec P4SpecTec.Refine P4SpecTec.Codegen P4SpecTec.Codegen.BuiltinCertificates

private def env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec

private def builtins := NanoP4Spec.spec.filter fun d => match d.it with
  | .BuiltinDecD .. => true
  | _ => false

#guard builtins.length == 26
#guard (builtins.filter requiresPrintHints).map (·.it.id.it) == ["print_"]
#guard builtins.all fun d => (checkSupport env d).isOk
#guard builtins.all fun d => (declarations env d).toOption.any fun source =>
  (source.pretty.splitOn "\n").all (fun line => line.length ≤ 100)

private def changedResult (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .BuiltinDecD name tps ps _ hints =>
      { d with it := .BuiltinDecD name tps ps (Q.t (.TupleT [])) hints }
  | _ => d

private def changedTypeArity (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .BuiltinDecD name tps ps ret hints =>
      { d with it := .BuiltinDecD name (Q.i "extra" :: tps) ps ret hints }
  | _ => d

#guard builtins.all fun d => !(checkSupport env (changedResult d)).isOk
#guard builtins.all fun d => !(checkSupport env (changedTypeArity d)).isOk

private def unknown : Lang.Al.def :=
  Q.d (.BuiltinDecD (Q.i "unknown") [] [Q.pm (.ExpP (Q.t .TextT))] (Q.t .TextT) [])

#guard !(declarations env unknown).isOk
#guard builtins.all fun d => !(checkSupport { env with mode := .freshState } d).isOk

private def wrongCarrier (name : String) : Env :=
  let info : TypeInfo :=
    { tparams := [], deftyp := some (.PlainT (Q.t .BoolT)), file := "fixture" }
  { env with types := env.types.insert name info }

#guard builtins.filter (fun d => d.it.id.it.endsWith "_map" || d.it.id.it == "find_maps")
  |>.all fun d => !(checkSupport (wrongCarrier "pair") d).isOk &&
    !(checkSupport (wrongCarrier "map") d).isOk
#guard builtins.filter (fun d => d.it.id.it.endsWith "_set")
  |>.all fun d => !(checkSupport (wrongCarrier "set") d).isOk
#guard builtins.filter (fun d => d.it.id.it.startsWith "bits_to_" ||
    d.it.id.it.startsWith "int_to_bits_")
  |>.all fun d => !(checkSupport (wrongCarrier "bits") d).isOk

end P4SpecTecTest.Codegen.BuiltinCertificates
