import P4SpecTec.Codegen.Certificates.Producer

/-!
Recursive input admission for source-checked first-match list updaters. The checked
operation recurses only on its list tail, with its key and replacement unchanged;
all suffixes therefore satisfy the independently declared input source domains.
-/

namespace P4SpecTec.Codegen.ProducerUpdateCall

open P4SpecTec.Lang.Il P4SpecTec.Codegen.Types P4SpecTec.Refine

/-- Exact source admission of every suffix call of a checked list updater. -/
def theoremType (env : Env) (d : Lang.Al.def) : Except String String := do
  let plan ← Producer.updatePlan env d
  let field := Q.t (Q.varT plan.field [])
  let list := Q.t (.IterT field .List)
  let types := [list, plan.key, plan.payload]
  let binders := types.zipIdx.map fun (t, i) =>
    s!"(p{i} : {(typTerm env [] t.it).fmt.pretty})"
  let inputs ← types.zipIdx.mapM fun (t, i) => Producer.admission env t s!"p{i}"
  let outputs ← [list, plan.key, plan.payload].zip
    ["(List.drop n p0)", "p1", "p2"] |>.mapM fun (t, x) => Producer.admission env t x
  pure ("∀ " ++ " ".intercalate binders ++ ",\n" ++
    "\n".intercalate (inputs.map (· ++ " →")) ++ "\n∀ n : Nat,\n" ++
    " ∧\n".intercalate outputs)

/-- Render suffix admission without a callable whitelist or recursive decoder premises. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String Std.Format := do
  let plan ← Producer.updatePlan env d
  let field := Q.t (Q.varT plan.field [])
  let carrier := env.q (Names.typeName plan.field)
  let listIff := "@P4SpecTec.Refine.Representation.Source.encodedListIff " ++
    carrier ++ " ⟨" ++ (← Producer.encoder env field) ++ "⟩ " ++ env.lib ++
    ".spec P4SpecTec.Refine.Representation.Source.externDomain (" ++
    (Reify.typ field).fmt.pretty ++ ")"
  let owner := Names.funcName plan.callable
  let statement ← theoremType env d
  pure (Std.Format.text (boundedLines (
    "/-- Every recursive suffix has all actual declared input source domains. -/\n" ++
    s!"theorem {owner}.recursiveInputsSource :\n" ++ statement ++ " := by\n" ++
    "  intro p0 p1 p2 h0 h1 h2 n\n" ++
    "  refine ⟨?_, h1, h2⟩\n" ++
    s!"  apply ({listIff} (List.drop n p0)).mpr\n" ++
    "  intro field member\n" ++
    s!"  exact ({listIff} p0).mp h0 field (List.mem_of_mem_drop member)\n\n" ++
    s!"#audit_axioms {owner}.recursiveInputsSource\n")))

end P4SpecTec.Codegen.ProducerUpdateCall
