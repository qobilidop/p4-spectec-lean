import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.Representation
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveTotality
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Representation.SourceExtern
import P4SpecTec.Tactic.CarrierInduction
import P4SpecTec.Tactic.Audit

/-! Native recursive admission totality covers renamed list and option carriers. -/

namespace P4SpecTecTest.Codegen.RepresentationRecursiveTotality
open P4SpecTec P4SpecTec.Lang.Il P4SpecTec.Codegen P4SpecTec.Domain P4SpecTec.Refine
open P4SpecTec.Prelude P4SpecTec.Codegen.RepresentationRecursive

private def nodeDeclaration := Q.d (.TypD (Q.i "node") [] (Q.dt (.VariantT
  [Q.tc (.Atom (Q.a (.Keyword "END"))) "node" [],
   Q.tc (.Seq [.Atom (Q.a (.Keyword "NEXT")),
     .Arg (Q.t (.IterT (Q.t (Q.varT "node" [])) .Opt))]) "node" [],
   Q.tc (.Seq [.Atom (Q.a (.Keyword "MANY")),
     .Arg (Q.t (.IterT (Q.t (Q.varT "node" [])) .List))]) "node" [],
   Q.tc (.Seq [.Atom (Q.a (.Keyword "BOOL")), .Arg (Q.t .BoolT)]) "node" []])) [])
def spec : Lang.Al.spec := [nodeDeclaration]
private def env := Env.ofSpec "P4SpecTecTest.Codegen.RepresentationRecursiveTotality" spec
#guard ((RepresentationCertificates.catalog env)["node"]?.bind Except.toOption).bind
  (·.total) == some "P4SpecTecTest.Codegen.RepresentationRecursiveTotality.node.admittedAll"

private def restrictiveLeaf := Q.d (.TypD (Q.i "leaf") []
  (Q.dt (.PlainT (Q.t .BoolT))) [])
private def restrictedRoot := Q.d (.TypD (Q.i "root") [] (Q.dt (.VariantT
  [Q.tc (.Seq [.Atom (Q.a (.Keyword "NEXT")), .Arg (Q.t (Q.varT "root" []))]) "root" [],
   Q.tc (.Seq [.Atom (Q.a (.Keyword "LEAF")), .Arg (Q.t (Q.varT "leaf" []))]) "root" []])) [])
private def restrictedEnv := Env.ofSpec "Restricted" [restrictiveLeaf, restrictedRoot]
private def restrictedPlan := derive restrictedEnv
  (fun _ => some ⟨"unprovedLeafCodec", "fun _ => False"⟩) "root"
#guard restrictedPlan.isOk
-- Metadata alone cannot supply the genuine independent leaf totality obligation.
#guard restrictedPlan.toOption.any fun plan =>
  !(totalityDeclarations restrictedEnv plan "NoLeafTotal" (fun _ => none)).isOk

open Lean Elab Command in
run_cmd do
  let .TypD name [] body _ := nodeDeclaration.it | throwError "fixture shape"
  let group := [(name.it, ([] : List String), body.it)]
  let .ok plan := derive env (fun _ => none) "node" | throwError "fixture plan"
  let .ok families := familyDeclarations plan "Proof" | throwError "fixture families"
  let .ok predicates := admissionDeclarations env plan "Proof" | throwError "fixture predicates"
  let totals ← match totalityDeclarations env plan "Proof" (fun _ => none) with
    | .ok totals => pure totals
    | .error message => throwError "{message}"
  let declarations := [Types.typeDecl env [name.it] name.it [] body.it,
    Types.toValueDecls env group, Types.ofValueDecls env group]
  let texts := declarations.flatMap (fun d =>
    match ((render d).replace "\ninstance" "\n\ninstance").splitOn "\n\ninstance" with
    | [] => []
    | first :: rest => first :: rest.map ("instance" ++ ·)) ++ (render families).splitOn "\n\n" ++
    predicates.map render ++ ["def node.admitted := Proof.admitted .f0"] ++
    (render totals).splitOn "\n\n"
  for text in texts do
    let command ← match Parser.runParserCategory (← getEnv) `command text with
      | .ok command => pure command
      | .error message => throwError "{text}\n{message}"
    elabCommand command

end P4SpecTecTest.Codegen.RepresentationRecursiveTotality
