import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.RepresentationAlias
import P4SpecTec.Codegen.Certificates.RepresentationField
import P4SpecTec.Codegen.Certificates.RepresentationMap
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceVariant

/-! Whole-source polymorphic codecs use source shapes, not particular operation names. -/

namespace P4SpecTecTest.Codegen.RepresentationContainers

open P4SpecTec P4SpecTec.Refine P4SpecTec.Codegen P4SpecTec.Prelude
open P4SpecTec.Codegen.RepresentationContainers

private def pairDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "duo") [Q.i "P", Q.i "Q"] (Q.dt (.VariantT
    [Q.tc (.Infix (.Arg (Q.t (Q.varT "P" []))) (Q.a (.Operator "~"))
      (.Arg (Q.t (Q.varT "Q" [])))) "duo" [Q.t (Q.varT "P" []), Q.t (Q.varT "Q" [])]])) [])

private def listDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "bag") [Q.i "E"] (Q.dt (.VariantT
    [Q.tc (.Seq [.Atom (Q.a (.Tag "ITEMS")),
      .Arg (Q.t (.IterT (Q.t (Q.varT "E" [])) .List))]) "bag" [Q.t (Q.varT "E" [])]])) [])

private def aliasDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "dictionary") [Q.i "A", Q.i "B"] (Q.dt (.PlainT
    (Q.t (Q.varT "bag" [Q.t (Q.varT "duo" [Q.t (Q.varT "A" []),
      Q.t (Q.varT "B" [])])])))) [])

private def fieldAlias (name : String) (target : Lang.Il.typ') : Lang.Al.def :=
  Q.d (.TypD (Q.i name) [] (Q.dt (.PlainT (Q.t target))) [])

private def fieldAliases := [
  fieldAlias "flags" (.IterT (Q.t .BoolT) .List),
  fieldAlias "namedDictionary" (Q.varT "dictionary" [Q.t .TextT, Q.t (.NumT .NatT)]),
  fieldAlias "namedFlags" (Q.varT "flags" [])]

private def declarationsToCheck :=
  [pairDeclaration, listDeclaration, aliasDeclaration] ++ fieldAliases
private def env := Env.ofSpec "P4SpecTecTest.Codegen.RepresentationContainers" declarationsToCheck

-- Long qualified names must not separate a tactic location from its keyword.
#guard !(boundedLines (String.ofList (List.replicate 90 'x') ++ " at hd")).contains "at\n"
#guard (boundedLines (String.ofList (List.replicate 80 'x') ++
  " \"escaped \\\" quote with spaces\"")).contains "\"escaped \\\" quote with spaces\""

#guard (pairShape env pairDeclaration).isOk
#guard (listShape env listDeclaration).isOk
#guard !(pairShape env listDeclaration).isOk
#guard !(listShape env pairDeclaration).isOk
#guard !(pairShape { env with representation := { rawExternTypes := ["duo"] } }
  pairDeclaration).isOk
#guard !(pairShape env (Q.d (.TypD (Q.i "duo") [Q.i "P", Q.i "P"]
  (Q.dt (.VariantT [])) []))).isOk
#guard !(listShape env (Q.d (.TypD (Q.i "bag") [Q.i "E"]
  (Q.dt (.VariantT [Q.tc (.Arg (Q.t (.IterT (Q.t .TextT) .List))) "bag" []])) []))).isOk

open Lean Elab Command in
private def elaborateFormats (formats : List Std.Format) : CommandElabM Unit := do
  for text in formats.flatMap (fun f =>
      ((render f).replace "\ninstance" "\n\ninstance"
        |>.replace "\n#audit_axioms" "\n\n#audit_axioms").splitOn "\n\n") do
    let command ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok command => pure command
      | .error message => throwError "{text}\n{message}"
    elabCommand command

open Lean Elab Command in
run_cmd do
  let mut formats : List Std.Format := []
  for declaration in declarationsToCheck do
    let .TypD id parameters body _ := declaration.it | throwError "expected a source type"
    let parameters := parameters.map (·.it)
    let group := [(id.it, parameters, body.it)]
    formats := formats ++ [Types.typeDecl env [] id.it parameters body.it,
      Types.toValueDecls env group, Types.ofValueDecls env group,
      Reify.quoted id.it declaration]
  formats := formats ++ [Std.Format.text
    ("def spec : Lang.Al.spec := [duo.al, bag.al, dictionary.al, " ++
      "flags.al, namedDictionary.al, namedFlags.al]")]
  for declaration in declarationsToCheck do
    let known : String → Option RepresentationFields.NominalContract := fun name =>
      if name == "flags" then some ⟨env.q "flags.codec", env.q "flags.admitted"⟩ else none
    let result := if fieldAliases.any (fun d => d.it.id.it == declaration.it.id.it) then
      RepresentationAliases.fieldDeclarations env known declaration
      else if declaration.it.id.it == "dictionary" then
        RepresentationMaps.declarations env declaration else declarations env declaration
    let certificate ← match result with
      | .ok proof => pure proof
      | .error message => throwError "{message}"
    formats := formats ++ [certificate]
  elaborateFormats formats

private def parameterFields : List Lang.Il.typ := [
  Q.t (Q.varT "duo" [Q.t .TextT, Q.t (.NumT .NatT)]),
  Q.t (Q.varT "bag" [Q.t (Q.varT "duo" [Q.t .TextT, Q.t (.NumT .NatT)])]),
  Q.t (Q.varT "dictionary" [Q.t .TextT, Q.t .BoolT])]

open Lean Elab Command in
run_cmd do
  for (field, index) in parameterFields.zipIdx do
    let contract ← match RepresentationFields.resolve env (fun _ => none) field with
      | .ok contract => pure contract
      | .error message => throwError "{message}"
    let theoremName := s!"parameterField{index}"
    elaborateFormats [Std.Format.text (s!"theorem {theoremName} : " ++
      contract.type (RepresentationFields.source env field) ++ " := " ++ contract.codec),
      Std.Format.text s!"#audit_axioms {theoremName}"]

/-- info: 'P4SpecTecTest.Codegen.RepresentationContainers.duo.codec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duo.codec

/-- info: 'P4SpecTecTest.Codegen.RepresentationContainers.bag.codec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bag.codec

/-- info: 'P4SpecTecTest.Codegen.RepresentationContainers.dictionary.codec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dictionary.codec

/-- info: 'P4SpecTecTest.Codegen.RepresentationContainers.namedDictionary.codec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms namedDictionary.codec

end P4SpecTecTest.Codegen.RepresentationContainers
