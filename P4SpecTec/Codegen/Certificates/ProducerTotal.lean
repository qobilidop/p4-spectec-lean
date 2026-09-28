import P4SpecTec.Codegen.Certificates.Producer
import P4SpecTec.Codegen.Certificates.RepresentationTotal

/-!
Source-output preservation when the entire actual result carrier has a proved source
admission. Both the codec and totality proof are explicit dependencies; absence of a
runtime extension alone never grants eligibility.
-/

namespace P4SpecTec.Codegen.ProducerTotal

open P4SpecTec.Lang.Il P4SpecTec.Domain

/-- A source producer justified by a checked total result-carrier admission. -/
structure Plan where
  /-- Nominal codec and total-admission sidecars used by the output proof. -/
  dependencies : List String
  /-- Exact source-input/source-output theorem and its axiom audit. -/
  declarations : String

/-- Select a result codec and its independent, previously proved total admission. -/
def plan (env : Env) (d : Lang.Al.def)
    (known : String → Option RepresentationTotals.TotalContract) (externs : Bool := false) :
    Except String Plan := do
  let statement ← Producer.theoremType env d externs
  let (callable, inputs, results) ← Producer.signature d
  let owner := callable.replace ".run" ""
  let inputCount := inputs.length
  let components ← (results.zip (Producer.resultProjections results.length)).mapM
    fun (result, value) => do
      let field ← RepresentationFields.resolve env (fun name => (known name).map (·.nominal))
        result
      let total ← RepresentationTotals.fieldProof env known result
      pure (field, "(@Representation.Codec.encodingValid (" ++ field.carrier ++ ") ⟨" ++
        field.encoder ++ "⟩ ⟨" ++ field.decoder ++ "⟩ (" ++
        RepresentationFields.source env result ++ ") (" ++ field.admitted ++ ") (" ++
        field.codec ++ ")) " ++ value ++ " ((" ++ total ++ ") " ++ value ++ ")")
  let proof := match components with
    | [(_, single)] => single
    | _ => "⟨" ++ ", ".intercalate (components.map (·.2)) ++ "⟩"
  let arguments := (List.range inputCount).map (fun index => s!"p{index}")
  let declarations := "/-- Every successful result inhabits the independent source domain. -/\n" ++
    s!"theorem {owner}.{env.part "producesSource"} :\n    " ++
      statement.replace "\n" "\n    " ++
    " := by\n  intro " ++ " ".intercalate ((if externs then ["_"] else []) ++ arguments ++
      List.replicate inputCount "_" ++
      ["result", "_"]) ++ "\n" ++ "  exact " ++ proof ++ "\n" ++
    s!"#audit_axioms {owner}.{env.part "producesSource"}\n"
  pure { dependencies := (components.flatMap (·.1.dependencies)).eraseDups
         declarations := boundedLines declarations }


end P4SpecTec.Codegen.ProducerTotal
