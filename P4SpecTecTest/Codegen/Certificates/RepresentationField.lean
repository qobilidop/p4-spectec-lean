import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.RepresentationField
import P4SpecTec.Refine.Representation.SourceExtern

/-! Exact field dictionary resolution and metadata-preserving substitution templates. -/

namespace P4SpecTecTest.Codegen.RepresentationFields
open P4SpecTec P4SpecTec.Refine P4SpecTec.Prelude P4SpecTec.Lang.Il
open P4SpecTec.Codegen P4SpecTec.Codegen.RepresentationFields

private def nominal := Q.d (.TypD (Q.i "name") [] (Q.dt (.PlainT (Q.t .TextT))) [])
private def opaqueDeclaration := Q.d (.ExternTypD (Q.i "opaque") [])
private def parameterized :=
  Q.d (.TypD (Q.i "box") [Q.i "K"] (Q.dt (.PlainT (Q.t (Q.varT "K" [])))) [])
private def env := Env.ofSpec "P4SpecTecTest.Codegen.RepresentationFields"
  [nominal, opaqueDeclaration, parameterized]

private def primitives : List typ :=
  [Q.t .BoolT, Q.t (.NumT .NatT), Q.t (.NumT .IntT), Q.t .TextT,
   Q.t (.IterT (Q.t .TextT) .List),
   Q.t (.IterT (Q.t (.IterT (Q.t .TextT) .Opt)) .List)]

#guard primitives.all fun t => (resolve env (fun _ => none) t).isOk
#guard !(resolve env (fun _ => none) (Q.t (Q.varT "missing" []))).isOk
#guard !(resolve env (fun _ => none) (Q.t (Q.varT "name" []))).isOk
#guard (resolve env (fun _ => none) (Q.t (Q.varT "opaque" []))).toOption.any
  (fun field => field.codec.contains "Representation.Source.externalCodec")
#guard !(resolve env (fun _ => some ⟨"boxCodec", "fun _ => True"⟩)
  (Q.t (Q.varT "box" []))).isOk
#guard (resolve env (fun _ => none) (Q.t (.TupleT []))).isOk
#guard (resolve env (fun _ => none) (Q.t (.TupleT [Q.t .BoolT, Q.t .TextT]))).isOk
#guard !(resolve env (fun _ => none) (Q.t (.TupleT [Q.t .BoolT]))).isOk
#guard !(resolve env (fun _ => none)
  (Q.t (.TupleT [Q.t .BoolT, Q.t .TextT, Q.t .BoolT]))).isOk
#guard !(resolve env (fun _ => none) (Q.t (.FuncT [] [] (Q.t .TextT)))).isOk
#guard (normalizeSubstitution (Q.t (Q.varT "box" [Q.t .TextT]))).isOk
#guard !(normalizeSubstitution (Q.t (Q.varT "box"
  [Q.t (.IterT (Q.t .TextT) .List)]))).isOk

-- A later reducible alias dictionary must not replace the primitive text dictionary.
private instance : OfValue ByteText := ⟨fun _ _ => none⟩

def spec : Lang.Al.spec := []

open Lean Elab Command in
private def elaborate (text : String) : CommandElabM Unit := do
  let command ← match Parser.runParserCategory (← getEnv) `command text with
    | .ok command => pure command
    | .error message => throwError "{text}\n{message}"
  elabCommand command

open Lean Elab Command in
run_cmd do
  for (t, index) in primitives.zipIdx do
    let contract ← match resolve env (fun _ => none) t with
      | .ok contract => pure contract
      | .error message => throwError "{message}"
    let name := s!"fieldCodec{index}"
    elaborate s!"theorem {name} : {contract.type (source env t)} := {contract.codec}"
    elaborate s!"#audit_axioms {name}"
    let normalization ← match normalizeSubstitution t with
      | .ok proof => pure proof
      | .error message => throwError "{message}"
    let sourceType := (Reify.typ t).fmt.pretty
    let name := s!"fieldSubstitution{index}"
    elaborate (s!"theorem {name} : ∀ actual, " ++
      s!"Representation.Source.Substitutes [] ({sourceType}).it actual → " ++
      s!"∀ v, Representation.Source.Valid spec Representation.Source.externDomain actual v → " ++
      s!"({source env t}) v := {normalization}")
    elaborate s!"#audit_axioms {name}"

open Lean Elab Command in
run_cmd do
  for (t, index) in ([Q.t (Q.varT "box" [Q.t .TextT]),
      Q.t (Q.varT "container" [Q.t (Q.varT "name" []), Q.t (.NumT .NatT)])]).zipIdx do
    let normalization ← match normalizeSubstitution t with
      | .ok proof => pure proof
      | .error message => throwError "{message}"
    let sourceType := (Reify.typ t).fmt.pretty
    let theoremName := s!"parameterSubstitution{index}"
    elaborate (s!"theorem {theoremName} : ∀ actual, " ++
      s!"Representation.Source.Substitutes [] ({sourceType}).it actual → " ++
      s!"∀ v, Representation.Source.Valid spec Representation.Source.externDomain actual v → " ++
      s!"({source env t}) v := {normalization}")
    elaborate s!"#audit_axioms {theoremName}"

/-- info: 'P4SpecTecTest.Codegen.RepresentationFields.fieldCodec5' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fieldCodec5

/-- info: 'P4SpecTecTest.Codegen.RepresentationFields.fieldSubstitution5' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fieldSubstitution5

end P4SpecTecTest.Codegen.RepresentationFields
