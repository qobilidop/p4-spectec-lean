import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveEncoding
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveIteration
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveAdmission
import P4SpecTec.Refine.Representation.SourceCodec
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceVariant
import P4SpecTec.Refine.Quote

/-! Recursive option/list fields use actual generated helpers and exact conditional contracts. -/

namespace P4SpecTecTest.Codegen.RepresentationRecursiveIteration
open P4SpecTec P4SpecTec.Lang.Il P4SpecTec.Codegen P4SpecTec.Domain P4SpecTec.Refine
open P4SpecTec.Prelude P4SpecTec.Codegen.RepresentationRecursive

private def nodeDeclaration := Q.d (.TypD (Q.i "node") [] (Q.dt (.VariantT
  [Q.tc (.Atom (Q.a (.Keyword "END"))) "node" [],
   Q.tc (.Seq [.Atom (Q.a (.Keyword "NEXT")),
     .Arg (Q.t (.IterT (Q.t (Q.varT "node" [])) .Opt))]) "node" [],
   Q.tc (.Seq [.Atom (Q.a (.Keyword "MANY")),
     .Arg (Q.t (.IterT (Q.t (Q.varT "node" [])) .List))]) "node" []])) [])
def spec : Lang.Al.spec := [nodeDeclaration]

private def env :=
  Env.ofSpec "P4SpecTecTest.Codegen.RepresentationRecursiveIteration" [nodeDeclaration]

open Lean Elab Command in
run_cmd do
  let .TypD name [] body _  := nodeDeclaration.it | throwError "fixture shape"
  let group := [(name.it, ([] : List String), body.it)]
  let .ok plan := derive env (fun _ => none) "node" | throwError "fixture plan"
  let .ok families := familyDeclarations plan "Proof" | throwError "fixture families"
  let .ok predicates := admissionDeclarations env plan "Proof" | throwError "fixture predicates"
  let .ok iterations := iterationDeclarations env plan "Proof" | throwError "fixture iterations"
  let .ok identities := fieldInstantiationDeclarations plan "Proof"
    | throwError "fixture substitutions"
  let .ok constructors := variantEncodingDeclarations env plan "Proof"
    | throwError "fixture encoding branches"
  let .ok compositions := compositionEncodingDeclarations env plan "Proof"
    | throwError "fixture encoding composition"
  let .ok encodings := encodingDeclarations env plan "Proof"
    | throwError "fixture encoding induction"
  let declarations := [Types.typeDecl env [name.it] name.it [] body.it,
    Types.toValueDecls env group, Types.ofValueDecls env group]
  let texts := declarations.flatMap (fun d =>
    match ((render d).replace "\ninstance" "\n\ninstance").splitOn "\n\ninstance" with
    | [] => []
    | first :: rest => first :: rest.map ("instance" ++ ·)) ++ (render families).splitOn "\n\n" ++
    predicates.map render ++ (render iterations).splitOn "\n\n" ++
    [identities, constructors, compositions, encodings].flatMap fun d =>
      (render d).splitOn "\n\n"
  for text in texts do
    let command ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok command => pure command
      | .error message => throwError "{text}\n{message}"
    elabCommand command

end P4SpecTecTest.Codegen.RepresentationRecursiveIteration
