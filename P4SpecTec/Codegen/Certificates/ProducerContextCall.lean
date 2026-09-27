import P4SpecTec.Codegen.Certificates.ProducerContextProof
import P4SpecTec.Codegen.Certificates.RepresentationTotal

/-!
Complete call-argument domains for checked context insertion. The map paths follow
source projections; keys and replacements retain initial admission. The intermediate
key-set domain is discharged only with an exact, independently checked leaf totality.
-/

namespace P4SpecTec.Codegen.ProducerContextCall

open P4SpecTec.Lang.Il P4SpecTec.Codegen.Types P4SpecTec.Refine

private def contract (env : Env) (d : Lang.Al.def) :
    Except String (ProducerContexts.InsertPlan × List typ) := do
  let plan ← ProducerContexts.insertPlan env d
  let .FuncDecD _ _ parameters .. := d.it | throw "context call needs a function"
  let types ← parameters.mapM fun p => match p.it with
    | .ExpP t => pure t | _ => throw "context call needs value arguments"
  pure (plan, types)

/-- Exact initial domains imply all map, key, payload and intermediate key-set call domains. -/
def theoremType (env : Env) (d : Lang.Al.def) : Except String String := do
  let (plan, types) ← contract env d
  let binders := types.zipIdx.map fun (t, i) =>
    s!"(p{i} : {(typTerm env [] t.it).fmt.pretty})"
  let inputs ← types.zipIdx.mapM fun (t, i) => Producer.admission env t s!"p{i}"
  let [global, block, localPath] := plan.paths | throw "context path count differs"
  let access (path : ProducerContexts.FieldPath) :=
    "p1." ++ Names.fieldName path.outer.it ++ "." ++ Names.fieldName path.inner.it
  let map := Q.t (Q.varT plan.frame.map [plan.frame.key, plan.frame.payload])
  let first ← Producer.admission env map ("(" ++ access global ++ ")")
  let second ← Producer.admission env map ("(" ++ access block ++ ")")
  let frame ← Producer.admission env map "frame"
  let projections := first ++ " ∧\n" ++ second ++ " ∧\n" ++
    "(∀ frame ∈ " ++ access localPath ++ ", " ++ frame ++ ")"
  let key ← Producer.admission env plan.frame.key "p2"
  let payload ← Producer.admission env plan.frame.payload "p3"
  let keys ← Producer.admission env (Q.t (Q.varT plan.frame.set [plan.frame.key])) "keys"
  pure ("∀ " ++ " ".intercalate binders ++ ",\n" ++
    "\n".intercalate (inputs.map (· ++ " →")) ++ "\n(" ++ projections ++ ") ∧\n" ++
    key ++ " ∧\n" ++ payload ++ " ∧\n∀ keys, " ++ keys)

/-- Render the complete call-domain bridge using exact checked key-carrier totality. -/
def declarations (env : Env) (d : Lang.Al.def)
    (known : String → Option RepresentationTotals.TotalContract) : Except String Std.Format := do
  let (plan, _) ← contract env d
  let keysType := Q.t (Q.varT plan.frame.set [plan.frame.key])
  let keys ← RepresentationFields.resolve env (fun name => (known name).map (·.nominal)) keysType
  let all ← RepresentationTotals.fieldProof env known keysType
  let source := RepresentationFields.source env keysType
  let encoding := keys.encodingProof source keys.codec
  let owner := Names.funcName plan.callable
  let statement ← theoremType env d
  pure (Std.Format.text (boundedLines (
    "/-- Complete actual source call arguments, including arbitrary intermediate key sets. -/\n" ++
    s!"theorem {owner}.callArgumentsSource :\n" ++ statement ++ " := by\n" ++
    "  intro _scope ctx key value _scopeValid contextValid keyValid valueValid\n" ++
    s!"  refine ⟨{owner}.callInputsSource ctx contextValid, keyValid, valueValid, ?_⟩\n" ++
    "  intro keys\n" ++ s!"  exact ({encoding}) keys (({all}) keys)\n\n" ++
    s!"#audit_axioms {owner}.callArgumentsSource\n")))

end P4SpecTec.Codegen.ProducerContextCall
