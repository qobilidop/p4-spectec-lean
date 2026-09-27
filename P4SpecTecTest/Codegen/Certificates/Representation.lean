import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.Representation
import P4SpecTec.Codegen.Reify
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Representation.Delay
import P4SpecTec.Refine.Representation.Source
import P4SpecTec.Refine.Representation.SourceAlias
import P4SpecTec.Refine.Representation.SourceAtomic
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceRecord
import P4SpecTec.Refine.Representation.SourceVariant

/-! Production codec emission and distinguishing source-family rejection tests. -/

namespace P4SpecTecTest.Codegen.RepresentationCertificates

open P4SpecTec P4SpecTec.Refine P4SpecTec.Codegen P4SpecTec.Prelude
open P4SpecTec.Codegen.RepresentationCertificates

private def cases : List Lang.Il.typcase :=
  [Q.tc (.Atom (Q.a (.Tag "EMPTY"))) "direction" [],
   Q.tc (.Atom (Q.a (.Keyword "IN"))) "direction" [],
   Q.tc (.Atom (Q.a (.Keyword "OUT"))) "direction" [],
   Q.tc (.Atom (Q.a (.Keyword "INOUT"))) "direction" []]

private def d : Lang.Al.def :=
  Q.d (.TypD (Q.i "direction") [] (Q.dt (.VariantT cases)) [])

private def singletonDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "singleton") [] (Q.dt (.VariantT
    [Q.tc (.Atom (Q.a (.Operator ";"))) "singleton" []])) [])

private def uniformDeclaration : Lang.Al.def :=
  Q.d (.TypD (Q.i "uniform") [] (Q.dt (.VariantT
    [Q.tc (.Atom (Q.a (.Keyword "YES"))) "uniform" [],
     Q.tc (.Atom (Q.a (.Keyword "NO"))) "uniform" []])) [])

private def env := Env.ofSpec "P4SpecTecTest.Codegen.RepresentationCertificates" [d]

#guard (checkSupport env d).isOk
#guard (declarations env d).toOption.any fun text =>
  (text.pretty.splitOn "\n").all (fun line => line.length ≤ 100)

private def changedCases (cs : List Lang.Il.typcase) : Lang.Al.def :=
  Q.d (.TypD (Q.i "direction") [] (Q.dt (.VariantT cs)) [])

#guard !(checkSupport env (changedCases [])).isOk
#guard !(checkSupport env (changedCases (cases ++ cases))).isOk
#guard !(checkSupport env (changedCases
  [Q.tc (.Arg (Q.t .TextT)) "direction" []])).isOk
#guard !(checkSupport env (Q.d
  (.TypD (Q.i "direction") [Q.i "T"] (Q.dt (.VariantT cases)) []))).isOk
#guard !(checkSupport env (Q.d
  (.TypD (Q.i "direction") [] (Q.dt (.PlainT (Q.t .TextT))) []))).isOk
#guard !(checkSupport { env with representation := { rawExternTypes := ["direction"] } } d).isOk

-- Wrapping preserves spaces inside string literals and quoted identifiers.
#guard (boundedLines ((String.ofList (List.replicate 90 'x')) ++
  " «spaced name» \"literal with spaces\"")).contains "«spaced name»"
#guard (boundedLines ((String.ofList (List.replicate 90 'x')) ++
  " «spaced name» \"literal with spaces\"")).contains "\"literal with spaces\""

private def aliasDefinition (name : String) (target : Lang.Il.typ') : Lang.Al.def :=
  Q.d (.TypD (Q.i name) [] (Q.dt (.PlainT (Q.t target))) [])

private def aliasDeclarations : Lang.Al.spec :=
  [aliasDefinition "textBase" .TextT, aliasDefinition "textSibling" .TextT,
   aliasDefinition "textAlias" (Q.varT "textBase" [])]

private def aliasEnv := Env.ofSpec "P4SpecTecTest.Codegen.RepresentationCertificates"
  aliasDeclarations

#guard aliasDeclarations.all fun d => (RepresentationAliases.checkSupport aliasEnv d).isOk
#guard !(RepresentationAliases.checkSupport
  (Env.ofSpec "Cycle" [aliasDefinition "loop" (Q.varT "loop" [])])
  (aliasDefinition "loop" (Q.varT "loop" []))).isOk
#guard !(RepresentationAliases.checkSupport
  (Env.ofSpec "Missing" [aliasDefinition "missing" (Q.varT "absent" [])])
  (aliasDefinition "missing" (Q.varT "absent" []))).isOk
#guard !(RepresentationAliases.checkSupport
  { aliasEnv with representation := { rawExternTypes := ["textAlias"] } }
  (aliasDefinition "textAlias" (Q.varT "textBase" []))).isOk

private def wrappedDirectionDeclaration := Q.d (.TypD (Q.i "wrappedDirection") [] (Q.dt (.VariantT
  [Q.tc (.Seq [.Atom (Q.a (.Tag "WRAPPED")), .Arg (Q.t (Q.varT "direction" []))])
    "wrappedDirection" []])) [])

private def recordDeclaration := Q.d (.TypD (Q.i "recordInfo") [] (Q.dt (.StructT
  [(Q.a (.Keyword "DIRECTION"), Q.t (Q.varT "wrappedDirection" [])),
   (Q.a (.Keyword "NAME"), Q.t (Q.varT "textAlias" []))])) [])

private def wrappers := [wrappedDirectionDeclaration, recordDeclaration,
  aliasDefinition "records" (.IterT (Q.t (Q.varT "recordInfo" [])) .List)]

def spec : Lang.Al.spec := [d, singletonDeclaration, uniformDeclaration] ++
  aliasDeclarations ++ wrappers

private def completeEnv := Env.ofSpec "P4SpecTecTest.Codegen.RepresentationCertificates" spec

-- A primitive alias codec is self-contained, but its totality proof uses its named parent.
#guard ((catalog completeEnv)["textAlias"]?.bind Except.toOption).map
  (·.dependencies) == some ["textBase"]
#guard ((catalog completeEnv)["textAlias"]?.bind Except.toOption).bind
  (·.total) == some "P4SpecTecTest.Codegen.RepresentationCertificates.textAlias.admittedAll"

#guard (dependencies completeEnv wrappedDirectionDeclaration).toOption == some ["direction"]
#guard (dependencies completeEnv recordDeclaration).toOption ==
  some ["wrappedDirection", "textAlias"]
#guard !(plan (Env.ofSpec "Cycle" [aliasDefinition "loop" (Q.varT "loop" [])])
  (aliasDefinition "loop" (Q.varT "loop" []))).isOk

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
  for declaration in spec do
    let .TypD id [] body _ := declaration.it | throwError "expected a monomorphic type"
    let group := [(id.it, ([] : List String), body.it)]
    formats := formats ++ [Types.typeDecl completeEnv [] id.it [] body.it,
      Types.toValueDecls completeEnv group, Types.ofValueDecls completeEnv group,
      Reify.quoted id.it declaration]
  for declaration in spec do
    let certificate ← match declarations completeEnv declaration with
      | .ok proof => pure proof
      | .error message => throwError "{message}"
    formats := formats ++ [certificate]
  elaborateFormats formats

-- Fuel layers follow the declared alias chain; an unrelated sibling adds no layer.
private def bytes := ByteText.ofString "x"
#guard textBase.ofValue 1 (Runtime.Value.Make.text bytes) = some bytes
#guard textSibling.ofValue 1 (Runtime.Value.Make.text bytes) = some bytes
#guard textAlias.ofValue 1 (Runtime.Value.Make.text bytes) = none
#guard textAlias.ofValue 2 (Runtime.Value.Make.text bytes) = some bytes

/-- info: 'P4SpecTecTest.Codegen.RepresentationCertificates.textAlias.codec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms textAlias.codec

/-- info: 'P4SpecTecTest.Codegen.RepresentationCertificates.direction.codec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms direction.codec

/-- info: 'P4SpecTecTest.Codegen.RepresentationCertificates.records.codec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms records.codec

end P4SpecTecTest.Codegen.RepresentationCertificates
