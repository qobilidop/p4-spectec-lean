import Lean.Elab.Command
import P4SpecTec.Codegen.PrintHints
import P4SpecTec.Prelude.Value

/-!
Print-policy invariants: inheritance and casts must preserve the selected
policy, including the absence of one. Unrelated types keep separate keys.
The emitted table is parsed and elaborated to test its literal quotation.
-/

namespace P4SpecTecTest.PrintPolicies

open P4SpecTec P4SpecTec.Util.Source P4SpecTec.Domain P4SpecTec.Lang.Il
open P4SpecTec.Codegen P4SpecTec.Lang.Hints

def mixop : Mixfix.mixop := .Seq [.Atom (mkPhrase (.Tag "C")), .Arg ()]

def caseOf (origin : String) : typcase :=
  .mk (mkPhrase (Mixfix.map (fun _ => mkPhrase (.NumT .NatT)) mixop))
    (mkPhrase (.mk (mkPhrase origin) [])) []

def variant (name origin : String) : Lang.Al.def :=
  mkPhrase (.TypD (mkPhrase name) [] (mkPhrase (.VariantT [caseOf origin])) [])
    { left := ⟨"policies.watsup", 1, 0⟩, right := ⟨"policies.watsup", 1, 20⟩ }

def ownSpec : Lang.Al.spec := [variant "Small" "Small", variant "Large" "Large"]

def inheritedSpec : Lang.Al.spec :=
  [variant "Small" "Small", variant "Large" "Small"]

def varT (name : String) : typ' := .VarT (mkPhrase name) []

def bridgeSpec : Lang.Al.spec := ownSpec ++ [mkPhrase (.FuncDecD (mkPhrase "up") []
  [mkPhrase (.ExpP (mkPhrase (varT "Small")))] (mkPhrase (varT "Large"))
  [mkPhrase ([mkPhrase (.ExpA ⟨.VarE (mkPhrase "x"), varT "Small", no_region⟩)],
    ⟨.UpCastE (mkPhrase (varT "Large"))
      ⟨.VarE (mkPhrase "x"), varT "Small", no_region⟩, varT "Large", no_region⟩, [])]
  none [])]

def policies (small large : String) : P4.Unparse.HEnv :=
  [("Small", mixop, .TextH small), ("Large", mixop, .TextH large)]

def accepts (spec : Lang.Al.spec) (henv : P4.Unparse.HEnv) : Bool :=
  (PrintHints.validate (Env.ofSpec "Fixture" spec) spec henv).isOk

#guard accepts inheritedSpec (policies "same" "same")
#guard !accepts inheritedSpec (policies "source" "target")
#guard !accepts inheritedSpec [("Small", mixop, .TextH "only source")]
#guard !accepts inheritedSpec [("Large", mixop, .TextH "only target")]
#guard accepts inheritedSpec []
#guard accepts bridgeSpec (policies "same" "same")
#guard !accepts bridgeSpec (policies "source" "target")
#guard !accepts bridgeSpec [("Small", mixop, .TextH "only source")]
#guard !accepts bridgeSpec [("Large", mixop, .TextH "only target")]
#guard accepts bridgeSpec []
-- Same constructor spelling alone does not connect unrelated type families.
#guard accepts ownSpec (policies "source" "target")
#guard !accepts [variant "Small" "Unknown"] [("Small", mixop, .TextH "hint")]
-- An empty policy table cannot distinguish origins, preserving no-hint fixtures.
#guard accepts [variant "Small" "Unknown"] []

def constructorSpec (note : typ') (constructor : String := "C") : Lang.Al.spec :=
  let n : Mixfix.t exp := .Seq [.Atom (mkPhrase (.Tag constructor)),
    .Arg ⟨.NumE (.Nat 7), .NumT .NatT, no_region⟩]
  ownSpec ++ [mkPhrase (.FuncDecD (mkPhrase "construct") [] [] (mkPhrase note)
    [mkPhrase ([], ⟨.CaseE n, note, no_region⟩, [])] none [])]

#guard accepts (constructorSpec (varT "Small")) (policies "small" "large")
#guard !accepts (constructorSpec (varT "Unknown")) (policies "small" "large")
#guard !accepts (constructorSpec .BoolT) (policies "small" "large")
#guard !accepts (constructorSpec (varT "Small") "Missing") (policies "small" "large")
#guard accepts (constructorSpec .BoolT) []

def aliasNoteSpec : Lang.Al.spec := constructorSpec (varT "SmallAlias") ++
  [mkPhrase (.TypD (mkPhrase "SmallAlias") []
    (mkPhrase (.PlainT (mkPhrase (varT "Small")))) [])]

-- Even an alias of the right variant is a different runtime lookup key.
#guard !accepts aliasNoteSpec (policies "small" "large")

def mismatchDiagnostic : Bool :=
  match PrintHints.validate (Env.ofSpec "Fixture" bridgeSpec) bridgeSpec
      (policies "source" "target") with
  | .ok _ => false
  | .error e => e == "print policy mismatch: Small -> Large, constructor `_C %` (policies.watsup)"

#guard mismatchDiagnostic

def definitionPrint : hint := Lean.Json.mkObj [("it", Lean.Json.mkObj [
  ("hintid", Lean.Json.mkObj [("it", .str "print")])])]

def definitionPrintSpec : Lang.Al.spec :=
  [mkPhrase (.TypD (mkPhrase "Small") []
    (mkPhrase (.VariantT [caseOf "Small"])) [definitionPrint])]

#guard !accepts definitionPrintSpec []

def quotedPolicy : Alter.t := .SeqH [
  .TextH "quoted \"text\"\nwith slash \\",
  .AtomH (mkPhrase (.Keyword "TOKEN")),
  .BrackH (mkPhrase .LParen) (.HoleH (mkPhrase .Next)) (mkPhrase .RParen),
  .FuseH (.TextH "prefix") (.HoleH (mkPhrase (.Num 0)))]

def quoteEnv : P4.Unparse.HEnv := [("Family", mixop, quotedPolicy)]

#guard (PrintHints.tableDecl quoteEnv).isOk
#guard !(PrintHints.tableDecl [("Family", mixop, .OtherH .null)]).isOk
#guard !(PrintHints.tableDecl [("Family", mixop, .HoleH (mkPhrase (.Num 1)))]).isOk

open Lean Elab Command in
run_cmd do
  let source ← match PrintHints.tableDecl quoteEnv with
    | .ok f => pure (Codegen.render f)
    | .error e => throwError "table emission failed: {e}"
  let stx ← match Lean.Parser.runParserCategory (← getEnv) `command source with
    | .ok stx => pure stx
    | .error e => throwError "table did not parse:\n{source}\n{e}"
  Lean.Elab.Command.elabCommand stx

#guard PrintHints.policyEq (P4.Unparse.find_hint «$print_».hints "Family" mixop)
  (some quotedPolicy)
#guard PrintHints.policyEq (P4.Unparse.find_hint «$print_».hints "Unrelated" mixop) none

end P4SpecTecTest.PrintPolicies
