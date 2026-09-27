import P4SpecTec.Codegen.Types

/-!
Source-order-preserving decoder alternative equations. The emitted proof selects one
actual notation, excludes every other notation and retains child decoding failures.
-/

namespace P4SpecTec.Codegen.RepresentationConstructors

open P4SpecTec.Domain P4SpecTec.Codegen.Types

/-- An exact decoder branch statement, without any assumptions about child success. -/
structure Branch where
  /-- Actual ordered constructor notations, with source fields erased to unit. -/
  notations : List Mixfix.mixop
  /-- Position of the selected constructor in the actual decoder alternatives. -/
  selected : Nat
  /-- Names of the raw positional fields. -/
  arguments : List String
  /-- Exact whole decoder application, referring to the theorem's fuel, value and context. -/
  decoder : String
  /-- Exact selected monadic decoding expression, including its generated constructor. -/
  outcome : String
  /-- Actual definitions needed to expose the decoder alternatives. -/
  unfolding : List String
  /-- Explicit independent child decoding expressions whose Option cases close the equation. -/
  children : List String
  /-- Additional concrete context binders needed by the decoder application. -/
  contextBinders : String := ""

/-- Render an audited exact branch equation after checking positional notation disjointness. -/
def declaration (name : String) (branch : Branch) : Except String String := do
  let some chosen := branch.notations[branch.selected]?
    | throw "constructor decoder branch has no selected source notation"
  if (Mixfix.args chosen).length != branch.arguments.length then
    throw "constructor decoder branch raw field arity differs from the source notation"
  for (other, index) in branch.notations.zipIdx do
    if index != branch.selected && Mixfix.eq_mixop chosen other then
      throw "constructor decoder branch needs disjoint source notations"
  let mixop := (mixopTerm chosen).fmt.pretty 1000000
  let fields := "[" ++ String.intercalate ", " branch.arguments ++ "]"
  let rawBinders := String.join (branch.arguments.map fun raw => s!" ({raw} : Lang.Il.value)")
  let mut proof := s!"private theorem {name} (fuel : Nat) {branch.contextBinders}" ++
    "(v : Lang.Il.value) (tree : Mixfix.t Lang.Il.value)" ++ rawBinders ++ "\n" ++
    "    (shape : v.it = .CaseV tree) " ++
    s!"(matching : Mixfix.eq_mixop tree (({mixop}) : Mixfix.mixop) = true)\n" ++
    s!"    (fields : Mixfix.args tree = {fields}) :\n" ++
    s!"    {branch.decoder} = {branch.outcome} := by\n" ++
    s!"  have selected : Prelude.Value.caseArgs tree ({mixop}) = some {fields} := by\n" ++
    "    simp only [Prelude.Value.caseArgs, matching, ite_true, fields]\n"
  let mut others : List String := []
  for (other, index) in branch.notations.zipIdx do
    if index != branch.selected then
      let otherMixop := (mixopTerm other).fmt.pretty 1000000
      proof := proof ++ s!"  have other{index} : Prelude.Value.caseArgs tree " ++
        s!"({otherMixop}) = none :=\n" ++
        s!"    Representation.Source.caseArgsDisjoint tree ({mixop}) ({otherMixop}) " ++
        "matching (by decide)\n"
      others := others ++ [s!"other{index}"]
  proof := proof ++ "  simp only [" ++
    String.intercalate ", " (branch.unfolding ++ ["shape", "selected"] ++ others) ++ "]\n"
  if branch.children.isEmpty then
    proof := proof ++ "  rfl\n"
  else
    let alternatives := branch.notations.zipIdx.map fun (_, index) =>
      if index == branch.selected then "(" ++ branch.outcome ++ ")" else "none"
    proof := proof ++ "  change (" ++ String.intercalate " <|> " alternatives ++ ") = " ++
      branch.outcome ++ "\n"
    proof := proof ++ "  " ++ String.intercalate " <;> "
      ((branch.children.map fun decoder => s!"cases ({decoder})") ++ ["rfl"]) ++ "\n"
  return proof ++ s!"\n#audit_axioms {name}\n\n"

end P4SpecTec.Codegen.RepresentationConstructors
