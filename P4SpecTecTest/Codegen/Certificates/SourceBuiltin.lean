import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.SourceBuiltin
import P4SpecTec.Codegen.Certificates.SourcePolymorphic

/-! Builtin source-domain selection preserves legal codecs and rejects signature drift. -/

namespace P4SpecTecTest.Codegen.SourceBuiltin
open P4SpecTec P4SpecTec.Refine P4SpecTec.Codegen
open SourceBuiltinCertificates

private def env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec
private def builtins := NanoP4Spec.spec.filter fun d => match d.it with
  | .BuiltinDecD .. => true
  | _ => false

#guard builtins.length == 26
#guard builtins.all fun d => (declarations env d).isOk
#guard builtins.all fun d => (declarations env d).toOption.any fun source =>
  (source.splitOn "\n").all (fun line => line.length ≤ 100)

private def wrongResult (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .BuiltinDecD name parameters inputs _ hints =>
    { d with it := .BuiltinDecD name parameters inputs (Q.t (.TupleT [])) hints }
  | _ => d

#guard builtins.all fun d => !(theoremType env (wrongResult d)).isOk
#guard builtins.all fun d => !(declarations { env with mode := .freshState } d).isOk

-- Legal type parameters are resolved from their binder, even if a global type shares the name.
#guard (field env ["value"] (Q.t (Q.varT "value" []))).toOption.any fun contract =>
  contract.carrier == "α0" && contract.codec == "c0" && contract.admitted == "A0" &&
    contract.sourceType == "t0" && contract.dependencies.isEmpty

-- A parameterized carrier without a proved source codec is never silently admitted.
#guard !(field env ["X"] (Q.t (Q.varT "not-a-source-type" [Q.t (Q.varT "X" [])]))).isOk
#guard !(field env [] (Q.t (.TupleT []))).isOk

-- A map's complete source coverage requires its actual map, set and pair declarations.
private def findMap := builtins.find? (fun d => d.it.id.it == "find_map")
#guard findMap.any fun d => (dependencies env d).toOption.any (·.contains "map")
#guard findMap.any fun d => (theoremType env d).toOption.any fun source =>
  (source.splitOn "Representation.Codec").length == 3 &&
    (source.splitOn "sourceDomain").length == 1

-- A catalog lookup supplies a complex named codec directly. Its absence is a failure;
-- the field resolver must not launch recursive representation planning as a fallback.
private def valueType := Q.t (Q.varT "value" [])
private def supplied (name : String) : Option RepresentationFields.NominalContract :=
  if name == "value" then some ⟨"suppliedCodec", "suppliedAdmitted"⟩ else none
#guard (fieldWithKnown env supplied [] valueType).toOption.any fun contract =>
  contract.codec == "suppliedCodec" && contract.admitted == "suppliedAdmitted" &&
    contract.dependencies == ["value"]
#guard !(fieldWithKnown env (fun _ => none) [] valueType).isOk

-- The single-plan API reproduces each part of the standalone builtin contract.
private def sameComplete (actual expected : Except String (String × String × List String)) :
    Bool :=
  match actual, expected with
  | .ok (proof, statement, dependencies), .ok (oldProof, oldStatement, oldDependencies) =>
    proof == oldProof && statement == oldStatement && dependencies == oldDependencies
  | _, _ => false

private def selectedBuiltins := builtins.filter fun d =>
  ["bits_to_int_unsigned", "find_map"].contains d.it.id.it
#guard selectedBuiltins.length == 2
#guard selectedBuiltins.all fun d =>
  sameComplete (complete env (namedKnown env) d)
    (do pure (← declarations env d, ← theoremType env d, ← dependencies env d))

-- Pair projections and membership use the same once-resolved plan path.
private def selectedPolymorphic := NanoP4Spec.spec.filter fun d =>
  ["in_set", "dom_map", "codom_map"].contains d.it.id.it
#guard selectedPolymorphic.length == 3
#guard selectedPolymorphic.all fun d =>
  sameComplete (SourcePolymorphic.complete env (namedKnown env) d)
    (do pure (← SourcePolymorphic.declarations env d,
      ← SourcePolymorphic.theoremType env d, ← SourcePolymorphic.dependencies env d))

end P4SpecTecTest.Codegen.SourceBuiltin
