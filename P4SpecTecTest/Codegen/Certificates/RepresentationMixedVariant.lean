import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.RepresentationMixedVariant
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Representation.SourceCodec
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceVariant

/-! Complete mixed-constructor codecs, ordered alternatives and source-shape rejections. -/

namespace P4SpecTecTest.Codegen.RepresentationMixedVariants

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
    [Q.tc (.Seq [.Atom (Q.a (.Tag "LEFT")), .Arg (Q.t field)]) name [],
     Q.tc (.Atom (Q.a (.Keyword "DONE"))) name [],
     Q.tc (.Seq [.Atom (Q.a (.Tag "RIGHT")), .Arg (Q.t field)]) name []])) [])

private def wideDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "wideBox") [] (Q.dt (.VariantT
    [Q.tc (.Seq [.Atom (Q.a (.Tag "WIDE")), .Arg (Q.t .BoolT), .Arg (Q.t .TextT),
      .Arg (Q.t (.IterT (Q.t .TextT) .List)), .Arg (Q.t (.IterT (Q.t .BoolT) .Opt))]) "wideBox" [],
     Q.tc (.Atom (Q.a (.Keyword "DONE"))) "wideBox" [],
     Q.tc (.Brack (Q.a (.Operator "["))
       (.Seq [.Arg (Q.t (.NumT .NatT)), .Arg (Q.t (.NumT .IntT))])
       (Q.a (.Operator "]"))) "wideBox" []])) [])

private def variantDeclarations : Lang.Al.spec := [wideDeclaration]

private def variantEnv := Env.ofSpec "P4SpecTecTest.Codegen.RepresentationMixedVariants"
  variantDeclarations

#guard variantDeclarations.all fun d => (RepresentationMixedVariants.checkSupport variantEnv d).isOk
#guard !(RepresentationMixedVariants.checkSupport variantEnv (Q.d (.TypD (Q.i "two") []
  (Q.dt (.VariantT [Q.tc (.Atom (Q.a (.Keyword "ONE"))) "two" [],
    Q.tc (.Atom (Q.a (.Keyword "ONE"))) "two" []])) []))).isOk
#guard (RepresentationMixedVariants.checkSupport variantEnv (Q.d (.TypD (Q.i "many") []
  (Q.dt (.VariantT [Q.tc (.Atom (Q.a (.Keyword "ONE"))) "many" [],
    Q.tc (.Seq [.Arg (Q.t .TextT), .Arg (Q.t .BoolT)]) "many" []])) []))).isOk
#guard !(RepresentationMixedVariants.checkSupport
  { variantEnv with representation := { rawExternTypes := ["textBox"] } }
  (variantDeclaration "textBox" .TextT)).isOk
#guard !(RepresentationMixedVariants.checkSupport variantEnv
  (variantDeclaration "open" (Q.varT "T" []))).isOk
#guard !(RepresentationMixedVariants.checkSupport
  (Env.ofSpec "Cycle" [variantDeclaration "self" (Q.varT "self" [])])
  (variantDeclaration "self" (Q.varT "self" []))).isOk
#guard variantDeclarations.all fun d =>
  (RepresentationMixedVariants.declarations variantEnv d).toOption.any fun output =>
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
  formats := formats ++ [Std.Format.text "def variantSpec : Lang.Al.spec := [wideBox.al]"]
  -- The production predicate always uses the compiled library's specification name.
  for declaration in variantDeclarations do
    let certificate ← match RepresentationMixedVariants.declarations variantEnv declaration with
      | .ok proof => pure proof
      | .error message => throwError "{message}"
    formats := formats ++ [Std.Format.text (certificate.pretty.replace
      "P4SpecTecTest.Codegen.RepresentationMixedVariants.spec"
      "P4SpecTecTest.Codegen.RepresentationMixedVariants.variantSpec")]
  elaborateFormats formats

end P4SpecTecTest.Codegen.RepresentationMixedVariants
