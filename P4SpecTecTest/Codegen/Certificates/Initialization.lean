import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.Initialization
import P4SpecTec.Refine.Environment
import P4SpecTec.Refine.Init
import P4SpecTec.Refine.Quote

/-!
Elaborate the production initialization certificates. Equal names across the
source's three tables are legal; duplicates within one table are rejected.
-/

namespace P4SpecTecTest.Codegen.Initialization

open P4SpecTec P4SpecTec.Refine

private def builtin : Lang.Al.def :=
  Q.d (.BuiltinDecD (Q.i "same") [] [] (Q.t .BoolT) [])

def spec : List Lang.Al.def :=
  [Q.d (.ExternTypD (Q.i "same") []),
   Q.d (.ExternRelD (Q.i "same") (Q.nt (.Seq [])) [] []), builtin]

open Lean Elab Command in
run_cmd do
  let declarations := P4SpecTec.Codegen.Initialization.declarations
    "P4SpecTecTest.Codegen.Initialization"
  for source in declarations.pretty.splitOn "\n\n" do
    let command ← match Parser.runParserCategory (← getEnv) `command source with
      | .ok command => pure command
      | .error message => throwError "{source}\n{message}"
    elabCommand command

/-- Duplicate declarations cannot satisfy the generated certificate's uniqueness proof. -/
theorem duplicateRejected : ¬ Init.NamesUnique [builtin, builtin] := by decide

/-- info: 'P4SpecTecTest.Codegen.Initialization.duplicateRejected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms duplicateRejected

end P4SpecTecTest.Codegen.Initialization
