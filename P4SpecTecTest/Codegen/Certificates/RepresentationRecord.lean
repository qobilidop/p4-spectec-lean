import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.RepresentationAlias
import P4SpecTec.Codegen.Certificates.RepresentationRecord
import P4SpecTec.Refine.Representation.Delay
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Refine.Representation.SourceRecord
import P4SpecTec.Refine.Representation.SourceVariant

/-! Record codec emission over actual ordered declarations and fixed field dictionaries. -/

namespace P4SpecTecTest.Codegen.RepresentationRecords
open P4SpecTec P4SpecTec.Refine P4SpecTec.Prelude P4SpecTec.Lang.Il P4SpecTec.Domain
open P4SpecTec.Codegen P4SpecTec.Codegen.RepresentationRecords

private def field (name : String) (t : typ') : typfield := (Q.a (.Keyword name), Q.t t)
private def recordDeclaration (name : String) (fields : List typfield) : Lang.Al.def :=
  Q.d (.TypD (Q.i name) [] (Q.dt (.StructT fields)) [])

private def textDeclaration :=
  Q.d (.TypD (Q.i "textAlias") [] (Q.dt (.PlainT (Q.t .TextT))) [])
private def records :=
  [recordDeclaration "single" [field "count" (.NumT .NatT)],
   recordDeclaration "scalars"
     [field "flag" .BoolT, field "count" (.NumT .NatT),
      field "integer" (.NumT .IntT), field "bytes" .TextT],
   recordDeclaration "containers"
     [field "items" (.IterT (Q.t (.IterT (Q.t .TextT) .Opt)) .List),
      field "label" (Q.varT "textAlias" [])]]
private def declarations := textDeclaration :: records
private def env := Env.ofSpec "P4SpecTecTest.Codegen.RepresentationRecords" declarations
private def known : String → Option RepresentationFields.NominalContract
  | "textAlias" => some
      ⟨"P4SpecTecTest.Codegen.RepresentationRecords.textAlias.codec", "fun _ => True"⟩
  | _ => none

#guard records.all fun d => (checkSupport env known d).isOk
#guard !(checkSupport env known (recordDeclaration "empty" [])).isOk
#guard !(checkSupport env known (recordDeclaration "duplicate"
  [field "x" .TextT, field "x" .BoolT])).isOk
#guard !(checkSupport env known (recordDeclaration "tagged"
  [(Q.a (.Tag "x"), Q.t .TextT)])).isOk
#guard !(checkSupport env known (recordDeclaration "unknown"
  [field "x" (Q.varT "missing" [])])).isOk
#guard !(records.all fun d => (checkSupport env (fun _ => none) d).isOk)
#guard !(checkSupport env known (Q.d (.TypD (Q.i "poly") [Q.i "K"]
  (Q.dt (.StructT [field "x" (Q.varT "K" [])])) []))).isOk

private def recursive := recordDeclaration "recursive" [field "child" (Q.varT "recursive" [])]
#guard !(checkSupport (Env.ofSpec "Recursive" [recursive])
  (fun _ => some ⟨"recursiveCodec", "fun _ => True"⟩) recursive).isOk

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
  let mut formats := []
  for declaration in declarations do
    let .TypD name [] body _ := declaration.it | throwError "expected a monomorphic declaration"
    let group := [(name.it, ([] : List String), body.it)]
    formats := formats ++ [Types.typeDecl env [] name.it [] body.it,
      Types.toValueDecls env group, Types.ofValueDecls env group,
      Reify.quoted name.it declaration]
  formats := formats ++ [Std.Format.text
    "def spec : Lang.Al.spec := [textAlias.al, single.al, scalars.al, containers.al]"]
  let aliasProof ← match RepresentationAliases.declarations env textDeclaration with
    | .ok proof => pure proof
    | .error message => throwError "{message}"
  formats := formats ++ [aliasProof, Std.Format.text
    "private instance hostile : OfValue ByteText := ⟨fun _ _ => none⟩"]
  for declaration in records do
    let proof ← match P4SpecTec.Codegen.RepresentationRecords.declarations
        env known declaration with
      | .ok proof => pure proof
      | .error message => throwError "{message}"
    unless (proof.pretty.splitOn "\n").all (fun line => line.length ≤ 100) do
      throwError "record proof exceeds the Lean line limit"
    formats := formats ++ [proof]
  elaborateFormats formats

/-- info: 'P4SpecTecTest.Codegen.RepresentationRecords.containers.codec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms containers.codec

private def wrongLabel := Runtime.Value.Make.str (Prelude.Value.varT "single")
  [("other", Runtime.Value.Make.nat 1)]

-- Generated decoders ignore labels; the independently declared source grammar retains them.
#guard single.ofValue 1 wrongLabel == some ⟨1⟩
example : ¬ single.source wrongLabel := by
  intro valid
  obtain ⟨fields, shape, labels, _⟩ := single.payload wrongLabel valid
  simp only [wrongLabel, Runtime.Value.Make.str, Runtime.Value.Make.mk] at shape
  have same := value'.StructV.inj shape
  subst fields
  cases labels with
  | cons wrong _ => simp [Atom.eq, Atom.compare] at wrong

end P4SpecTecTest.Codegen.RepresentationRecords
