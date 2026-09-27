import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.SourceProfile
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Representation.SourcePrimitive
import P4SpecTec.Refine.Representation.SourceExtern

/-! Typed omission accounting, exact quotation mutations and audited no-op initialization. -/

namespace P4SpecTecTest.Codegen.SourceProfiles

open P4SpecTec P4SpecTec.Codegen P4SpecTec.Refine

private def variableDecl (name : String) (type : Lang.Il.typ') : Lang.Al.def :=
  Q.d (.VarD (Q.i name) (Q.t type) [])

-- The eight pinned Nano metavariable signatures; the external declaration tests filtering.
def fixture : Lang.Al.spec :=
  [variableDecl "b" .BoolT,
   variableDecl "i" (.NumT .IntT),
   Q.d (.ExternTypD (Q.i "interleaved") []),
   variableDecl "n" (.NumT .NatT),
   variableDecl "w" (.NumT .NatT),
   variableDecl "TC" (Q.varT "typingContext" []),
   variableDecl "TBLC" (Q.varT "tableContext" []),
   variableDecl "LC" (Q.varT "loadContext" []),
   variableDecl "EC" (Q.varT "evalContext" [])]

def spec : Lang.Al.spec := fixture

#guard (SourceProfiles.metadata fixture).map (·.name) ==
  ["b", "i", "n", "w", "TC", "TBLC", "LC", "EC"]
#guard match SourceProfiles.compareVariables fixture
    (SourceProfiles.variableDeclarations fixture) with
  | .ok n => n == 8
  | .error _ => false
#guard (SourceProfiles.compareVariables fixture []).isOk == false
#guard (SourceProfiles.compareVariables fixture
  (SourceProfiles.variableDeclarations fixture).reverse).isOk == false
#guard (SourceProfiles.compareVariables fixture
  (variableDecl "renamed" .BoolT :: (SourceProfiles.variableDeclarations fixture).drop 1)).isOk
  == false
#guard (SourceProfiles.compareVariables fixture
  (variableDecl "b" (.NumT .NatT) :: (SourceProfiles.variableDeclarations fixture).drop 1)).isOk
  == false
#guard (SourceProfiles.compareVariables fixture fixture).isOk == false

open Lean Elab Command in
run_cmd do
  for (scope, spec) in [("", fixture), ("Empty", [])] do
    let output := (SourceProfiles.declarations spec).pretty ++ "\n\n" ++
      (SourceProfiles.primitiveDeclarations "P4SpecTecTest.Codegen.SourceProfiles").pretty
    unless (output.splitOn "\n").all (fun line => line.length ≤ 100) do
      throwError "source profile output exceeds the line limit"
    let text := if scope.isEmpty then output else
      "namespace " ++ scope ++ "\n\n" ++ output ++ "\n\nend " ++ scope
    for source in text.splitOn "\n\n" do
      unless source.trimAscii.toString.isEmpty do
        let command ← match Parser.runParserCategory (← getEnv) `command source with
          | .ok command => pure command
          | .error message => throwError "{source}\n{message}"
        elabCommand command

#guard match SourceProfiles.compareVariables fixture SourceProfile.variableDeclarations with
  | .ok n => n == 8
  | .error _ => false

/-- info: 'P4SpecTecTest.Codegen.SourceProfiles.SourceProfile.variablesIgnored' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms SourceProfile.variablesIgnored

example (g : Interp_al.Ctx.global) :
    Interp_al.Ctx.load_defs g SourceProfile.variableDeclarations = .ok g :=
  SourceProfile.variablesIgnored g

-- The generic removal theorem preserves failure too, without assuming initialization succeeds.
example : Interp_al.Ctx.init (Refine.SourceProfile.withoutVariables fixture) =
    Interp_al.Ctx.init fixture := Refine.SourceProfile.initWithoutVariables fixture

end P4SpecTecTest.Codegen.SourceProfiles
