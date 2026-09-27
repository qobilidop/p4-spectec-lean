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
    (known : String → Option RepresentationTotals.TotalContract) : Except String Plan := do
  let statement ← Producer.theoremType env d
  let (owner, inputCount, result) ← match d.it with
    | .FuncDecD name [] params result .. => pure (Names.funcName name.it, params.length, result)
    | .RelD name sourceNotation modes .. =>
      let (inputs, results) := Exp.splitArgs (modes.map (·.toNat))
        (Mixfix.args sourceNotation.it)
      let result ← match results with
        | [] => pure (P4SpecTec.Refine.Q.t (.TupleT []))
        | [result] => pure result
        | _ => throw "total producer needs at most one relation output"
      pure (Names.relName name.it, inputs.length, result)
    | _ => throw "total producer needs a monomorphic function or zero/single-output relation"
  let field ← RepresentationFields.resolve env (fun name => (known name).map (·.nominal)) result
  let total ← RepresentationTotals.fieldProof env known result
  let arguments := (List.range inputCount).map (fun index => s!"p{index}")
  let declarations := "/-- Every successful result inhabits the independent source domain. -/\n" ++
    s!"theorem {owner}.producesSource :\n    " ++ statement.replace "\n" "\n    " ++
    " := by\n  intro " ++ " ".intercalate (arguments ++ List.replicate inputCount "_" ++
      ["result", "_"]) ++ "\n" ++
    "  exact (@Representation.Codec.encodingValid (" ++ field.carrier ++ ") ⟨" ++
    field.encoder ++ "⟩ ⟨" ++ field.decoder ++ "⟩ (" ++
    RepresentationFields.source env result ++ ") (" ++ field.admitted ++ ") (" ++
    field.codec ++ ")) result ((" ++ total ++ ") result)\n" ++
    s!"#audit_axioms {owner}.producesSource\n"
  pure { dependencies := field.dependencies, declarations := boundedLines declarations }

end P4SpecTec.Codegen.ProducerTotal
