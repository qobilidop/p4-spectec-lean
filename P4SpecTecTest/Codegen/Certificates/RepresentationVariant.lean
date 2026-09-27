import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.RepresentationVariant
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceVariant

/-! Complete single-field variant codecs and source-shape rejection boundaries. -/

namespace P4SpecTecTest.Codegen.RepresentationVariants

open P4SpecTec P4SpecTec.Refine P4SpecTec.Codegen P4SpecTec.Prelude

open Lean Elab Command in
private def elaborateFormats (formats : List Std.Format) : CommandElabM Unit := do
  for text in formats.flatMap (fun f =>
      ((render f).replace "\ninstance" "\n\ninstance"
        |>.replace "\n#audit_axioms" "\n\n#audit_axioms").splitOn "\n\n") do
    let command ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok command => pure command
      | .error message => throwError "{text}\n{message}"
    elabCommand command

private def variantDeclaration (name : String) (field : Lang.Il.typ') : Lang.Al.def :=
  Q.d (.TypD (Q.i name) [] (Q.dt (.VariantT
    [Q.tc (.Brack (Q.a (.Operator "(")) (.Arg (Q.t field)) (Q.a (.Operator ")"))) name []])) [])

private def variantDeclarations : Lang.Al.spec :=
  [variantDeclaration "booleanBox" .BoolT,
   variantDeclaration "naturalBox" (.NumT .NatT),
   variantDeclaration "integerBox" (.NumT .IntT),
   variantDeclaration "textBox" .TextT,
   variantDeclaration "textsBox" (.IterT (Q.t .TextT) .List),
   variantDeclaration "optionalBox" (.IterT (Q.t .BoolT) .Opt)]

private def variantEnv := Env.ofSpec "P4SpecTecTest.Codegen.RepresentationVariants"
  variantDeclarations

#guard variantDeclarations.all fun d => (RepresentationVariants.checkSupport variantEnv d).isOk
#guard !(RepresentationVariants.checkSupport variantEnv (Q.d (.TypD (Q.i "two") []
  (Q.dt (.VariantT [Q.tc (.Atom (Q.a (.Keyword "ONE"))) "two" [],
    Q.tc (.Atom (Q.a (.Keyword "TWO"))) "two" []])) []))).isOk
#guard !(RepresentationVariants.checkSupport
  { variantEnv with representation := { rawExternTypes := ["textBox"] } }
  (variantDeclaration "textBox" .TextT)).isOk
#guard !(RepresentationVariants.checkSupport variantEnv
  (variantDeclaration "open" (Q.varT "T" []))).isOk
#guard !(RepresentationVariants.checkSupport
  (Env.ofSpec "Cycle" [variantDeclaration "self" (Q.varT "self" [])])
  (variantDeclaration "self" (Q.varT "self" []))).isOk
#guard variantDeclarations.all fun d =>
  (RepresentationVariants.declarations variantEnv d).toOption.any fun output =>
    (output.pretty.splitOn "\n").all (fun line => line.length ≤ 100)

open Lean Elab Command in
run_cmd do
  let mut formats : List Std.Format := []
  for declaration in variantDeclarations do
    let .TypD id [] body _ := declaration.it | throwError "expected monomorphic variant"
    let group := [(id.it, ([] : List String), body.it)]
    formats := formats ++ [Types.typeDecl variantEnv [] id.it [] body.it,
      Types.toValueDecls variantEnv group, Types.ofValueDecls variantEnv group,
      Reify.quoted id.it declaration]
  formats := formats ++ [Std.Format.text
    "def variantSpec : Lang.Al.spec := [booleanBox.al, naturalBox.al, integerBox.al, " ++
    Std.Format.text "textBox.al, textsBox.al, optionalBox.al]"]
  -- The production predicate always uses the compiled library's specification name.
  for declaration in variantDeclarations do
    let certificate ← match RepresentationVariants.declarations variantEnv declaration with
      | .ok proof => pure proof
      | .error message => throwError "{message}"
    formats := formats ++ [Std.Format.text (certificate.pretty.replace
      "P4SpecTecTest.Codegen.RepresentationVariants.spec"
      "P4SpecTecTest.Codegen.RepresentationVariants.variantSpec")]
  elaborateFormats formats

end P4SpecTecTest.Codegen.RepresentationVariants
