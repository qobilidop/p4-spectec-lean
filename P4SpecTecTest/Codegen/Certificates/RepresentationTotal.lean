import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.RepresentationTotal
import P4SpecTec.Codegen.Certificates.RepresentationAlias
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceRecord
import P4SpecTec.Refine.Representation.SourceVariant

/-! Structural total admission uses real codec predicates and proved child totals. -/

namespace P4SpecTecTest.Codegen.RepresentationTotals

open P4SpecTec P4SpecTec.Codegen P4SpecTec.Refine P4SpecTec.Prelude

private def pairDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "duo") [Q.i "P", Q.i "Q"] (Q.dt (.VariantT
    [Q.tc (.Infix (.Arg (Q.t (Q.varT "P" []))) (Q.a (.Operator "~"))
      (.Arg (Q.t (Q.varT "Q" [])))) "duo" [Q.t (Q.varT "P" []), Q.t (Q.varT "Q" [])]])) [])

private def listDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "bag") [Q.i "E"] (Q.dt (.VariantT
    [Q.tc (.Seq [.Atom (Q.a (.Tag "ITEMS")),
      .Arg (Q.t (.IterT (Q.t (Q.varT "E" [])) .List))]) "bag" [Q.t (Q.varT "E" [])]])) [])

private def mapDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "dictionary") [Q.i "A", Q.i "B"] (Q.dt (.PlainT
    (Q.t (Q.varT "bag" [Q.t (Q.varT "duo" [Q.t (Q.varT "A" []),
      Q.t (Q.varT "B" [])])])))) [])

private def childDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "child") [] (Q.dt (.VariantT
    [Q.tc (.Seq [.Atom (Q.a (.Tag "CHILD")), .Arg (Q.t .BoolT)]) "child" []])) [])

private def variantDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "choice") [] (Q.dt (.VariantT
    [Q.tc (.Atom (Q.a (.Keyword "EMPTY"))) "choice" [],
     Q.tc (.Seq [.Atom (Q.a (.Tag "BOTH")), .Arg (Q.t (Q.varT "child" [])),
       .Arg (Q.t (.IterT (Q.t (.IterT (Q.t .TextT) .Opt)) .List))]) "choice" []])) [])

private def recordDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "record") [] (Q.dt (.StructT
    [(Q.a (.Keyword "ITEM"), Q.t (Q.varT "child" [])),
     (Q.a (.Keyword "MAP"), Q.t (Q.varT "dictionary" [Q.t .BoolT, Q.t .TextT]))])) [])

private def aliasDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "wrapped") [] (Q.dt (.PlainT (Q.t (Q.varT "child" [])))) [])

private def sourceSpec : Lang.Al.spec :=
  [pairDeclaration, listDeclaration, mapDeclaration, childDeclaration,
   variantDeclaration, recordDeclaration, aliasDeclaration]

private def env := Env.ofSpec "P4SpecTecTest.Codegen.RepresentationTotals" sourceSpec

private def known (name : String) : Option RepresentationTotals.TotalContract :=
  if name == "child" then some
    { nominal := { codec := env.q "child.codec", admitted := env.q "child.admitted" }
      proof := env.q "child.admittedAll" }
  else none

#guard (RepresentationTotals.declarations env recordDeclaration "record.admitted").toOption.isNone
#guard (RepresentationTotals.declarations
  { env with representation := { rawExternTypes := ["child"] } }
  childDeclaration "child.admitted" known).toOption.isNone

private def cyclic : Lang.Al.def :=
  Q.d (.TypD (Q.i "loop") [] (Q.dt (.PlainT (Q.t (Q.varT "loop" [])))) [])
#guard (RepresentationTotals.declarations (Env.ofSpec "Loop" [cyclic]) cyclic
  "fun _ => True").toOption.isNone

#guard sourceSpec.all fun d =>
  (RepresentationTotals.declarations env d
    (env.q (Names.typeName d.it.id.it) ++ ".admitted") known).toOption.any fun output =>
      ((render output).splitOn "\n").all (fun line => line.length ≤ 100)

open Lean Elab Command in
private def elaborateFormats (formats : List Std.Format) : CommandElabM Unit := do
  for text in formats.flatMap (fun f =>
      ((render f).replace "\ninstance" "\n\ninstance"
        |>.replace "\n#audit_axioms" "\n\n#audit_axioms").splitOn "\n\n") do
    if text.trimAscii.toString.isEmpty then continue
    let command ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok command => pure command
      | .error message => throwError "{text}\n{message}"
    elabCommand command

open Lean Elab Command in
run_cmd do
  let mut formats : List Std.Format := []
  for d in sourceSpec do
    let .TypD name parameters body _ := d.it | throwError "fixture declaration"
    let params := parameters.map (·.it)
    let group := [(name.it, params, body.it)]
    formats := formats ++ [Types.typeDecl env [] name.it params body.it,
      Types.toValueDecls env group, Types.ofValueDecls env group, Reify.quoted name.it d]
  formats := formats ++ [Std.Format.text
    ("def spec : Lang.Al.spec := [" ++ ", ".intercalate
      (sourceSpec.map (fun d => Names.typeName d.it.id.it ++ ".al")) ++ "]")]
  let nominal := fun name => (known name).map (·.nominal)
  for d in sourceSpec do
    let codec := if d.it.id.it == "child" then
        RepresentationVariants.declarations env d nominal
      else if d.it.id.it == "choice" then
        RepresentationMixedVariants.declarations env d nominal
      else if d.it.id.it == "record" then
        RepresentationRecords.declarations env nominal d
      else if d.it.id.it == "wrapped" then
        RepresentationAliases.fieldDeclarations env nominal d
      else if d.it.id.it == "dictionary" then RepresentationMaps.declarations env d
      else RepresentationContainers.declarations env d
    let codec ← match codec with | .ok f => pure f | .error e => throwError "{e}"
    formats := formats ++ [codec]
    let total ← match RepresentationTotals.declarations env d
        (env.q (Names.typeName d.it.id.it) ++ ".admitted") known with
      | .ok f => pure f | .error e => throwError "{e}"
    formats := formats ++ [total]
  elaborateFormats formats

end P4SpecTecTest.Codegen.RepresentationTotals
