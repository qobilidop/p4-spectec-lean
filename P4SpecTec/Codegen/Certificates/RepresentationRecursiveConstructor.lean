import P4SpecTec.Codegen.Certificates.RepresentationConstructor
import P4SpecTec.Codegen.Certificates.RepresentationRecursive

/-!
Exact recursive decoder constructor equations and conditional stable witnesses.
The equations use actual compiler dictionaries, source constructor order and
notation disjointness. Child codec correctness is not assumed by these helpers.
-/

namespace P4SpecTec.Codegen.RepresentationRecursive

open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Codegen.Types

private def outcome (env : Env) (index : Nat) (sourceName constructorName : String)
    (children : List Nat) (raws : List String) : String :=
  let values := (List.range children.length).map (fun position => s!"x{position}")
  let value := env.q (Names.typeName sourceName) ++ "." ++ constructorName ++ " " ++
    " ".intercalate values
  ((children.zip raws).zipIdx).foldr (fun ((child, raw), position) tail =>
    s!"(decode .f{child} fuel {raw}).bind (fun x{position} => {tail})")
    s!"some (({value}) : Carrier .f{index})"

private def stableBranch (env : Env) (index selected : Nat) (sourceName constructorName : String)
    (pattern : Mixfix.mixop) (children : List Nat) (guarded : Bool) : String := Id.run do
  let positions := List.range children.length
  let raws := positions.map (fun position => s!"a{position}")
  let values := positions.map (fun position => s!"x{position}")
  let rawBinders := raws.map (fun raw => s!" ({raw} : value)")
  let typedBinders := children.zipIdx.map (fun (child, position) =>
    s!" (x{position} : Carrier .f{child})")
  let hypotheses := (children.zip raws).zipIdx.map fun ((child, raw), position) =>
    s!"\n    (h{position} : Representation.Decodes (decode .f{child}) {raw} x{position})"
  let value := env.q (Names.typeName sourceName) ++ "." ++ constructorName ++ " " ++
    " ".intercalate values
  let name := s!"decodeBranch{index}_{selected}"
  let mut text := "/-- Stable child decodes compose through this actual source constructor. -/\n" ++
    s!"private theorem {name} (v : value) (tree : Mixfix.t value)" ++
    String.join rawBinders ++ String.join typedBinders ++ "\n" ++
    "    (shape : v.it = .CaseV tree)\n" ++
    "    (matching : Mixfix.eq_mixop tree ((" ++ (mixopTerm pattern).fmt.pretty 1000000 ++
    ") : Mixfix.mixop) = true)\n    (fields : Mixfix.args tree = [" ++
    ", ".intercalate raws ++ "])" ++
    String.join hypotheses ++ s!" :\n    Representation.Decodes (decode .f{index}) v " ++
    s!"(({value}) : Carrier .f{index}) := by\n"
  for position in positions do
    text := text ++ s!"  obtain ⟨b{position}, h{position}⟩ := h{position}\n"
  let bound := positions.foldr (fun position tail => s!"max b{position} ({tail})") "0"
  let adjustment := if guarded then " + 1" else ""
  text := text ++ s!"  refine ⟨({bound}){adjustment}, ?_⟩\n  intro fuel _hf\n"
  let indent := if guarded then "    " else "  "
  if guarded then
    text := text ++ "  cases fuel with\n  | zero => omega\n  | succ fuel =>\n"
  for position in positions do
    text := text ++ indent ++ s!"have d{position} := h{position} fuel (by omega)\n"
  text := text ++ indent ++ s!"rw [decoderBranch{index}_{selected} fuel v tree " ++
    " ".intercalate raws ++ " shape matching fields]\n"
  if !positions.isEmpty then
    text := text ++ indent ++ "rw [" ++
      ", ".intercalate (positions.map (fun position => s!"d{position}")) ++ "]\n"
  text := text ++ indent ++ s!"all_goals rfl\n\n#audit_axioms {name}"
  return text

/-- Emit exact decoder branch equations and conditional sufficient-fuel composition.
Actual source field classifications and the source induction provide child witnesses later. -/
def constructorDeclarations (env : Env) (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut declarations := []
  for (family, index) in plan.families.toList.zipIdx do
    let some (.VariantT cases) := family.body | continue
    let .VarT name _ := family.source.it | throw "recursive variant source root is not nominal"
    let notations := cases.map (fun c => Mixfix.to_mixop c.nottyp.it)
    let mut cursor := 0
    for ((sourceCase, constructorName), selected) in (cases.zip (ctorNames cases)).zipIdx do
      let count := (Mixfix.args sourceCase.nottyp.it).length
      let children := family.children.drop cursor |>.take count
      let raws := (List.range count).map (fun position => s!"a{position}")
      let fuel := if family.guarded then "(fuel + 1)" else "fuel"
      let unfolding := ["decode"] ++
        (if family.guarded then [env.q (ofValueName name.it)] else [])
      let branch : RepresentationConstructors.Branch := {
        notations, selected, arguments := raws
        decoder := s!"decode .f{index} {fuel} v"
        outcome := outcome env index name.it constructorName children raws
        unfolding
        children := (children.zip raws).map (fun (child, raw) => s!"decode .f{child} fuel {raw}") }
      let equation ← RepresentationConstructors.declaration
        s!"decoderBranch{index}_{selected}" branch
      declarations := declarations ++ [equation.trimAscii.toString,
        stableBranch env index selected name.it
        constructorName (Mixfix.to_mixop sourceCase.nottyp.it) children family.guarded]
      cursor := cursor + count
    if cursor != family.children.length then throw "recursive constructor field arity mismatch"
  pure (Std.Format.text (boundedLines (
    s!"namespace {namespaceName}\n\n" ++ "\n\n".intercalate declarations ++
    s!"\n\nend {namespaceName}")))

private partial def sequenceKinds {α : Type} : Mixfix.t α → Bool × Bool
  | .Arg _ | .Atom _ => (false, false)
  | .Brack _ inner _ => sequenceKinds inner
  | .Infix left _ right =>
    let l := sequenceKinds left
    let r := sequenceKinds right
    (l.1 || r.1, l.2 || r.2)
  | .Seq children =>
    let nested := children.map sequenceKinds
    (true, !children.isEmpty || nested.any (·.2))

/-- Exact simplifier equations needed to expose positional arguments of a finite notation. -/
def argumentRules {α : Type} (pattern : Mixfix.t α) : String :=
  let kinds := sequenceKinds pattern
  ", ".intercalate (["Mixfix.args"] ++
    (if kinds.2 then ["List.flatMap_cons"] else []) ++
    (if kinds.1 then ["List.flatMap_nil"] else []))

private def soundBranch (env : Env) (index selected : Nat) (sourceName constructorName : String)
    (pattern : Mixfix.mixop) (children : List Nat) (guarded : Bool)
    (encoderUnfolding : List String) : String := Id.run do
  let positions := List.range children.length
  let raws := positions.map (fun position => s!"a{position}")
  let values := positions.map (fun position => s!"x{position}")
  let value := "(" ++ env.q (Names.typeName sourceName) ++ "." ++ constructorName ++ " " ++
    " ".intercalate values ++ s!" : Carrier .f{index})"
  let encoded := (children.zip values).map fun (child, value) =>
    Term.call "encode" [.atom s!".f{child}", .atom value]
  let rendered := (mixfixTerm pattern encoded).fmt.pretty 1000000
  let renderedFields := "[" ++ ", ".intercalate ((children.zip values).map fun (child, value) =>
    s!"encode .f{child} {value}") ++ "]"
  let argsRules := argumentRules pattern
  let matching := "((" ++ (mixopTerm pattern).fmt.pretty 1000000 ++ ") : Mixfix.mixop)"
  let hypotheses := (children.zip raws).zipIdx.map fun ((child, raw), position) =>
    s!"\n    (h{position} : ∀ fuel x, decode .f{child} fuel {raw} = some x →\n" ++
    s!"      admitted .f{child} x ∧ Rel {raw} (encode .f{child} x))"
  let name := s!"soundBranch{index}_{selected}"
  let mut text := "/-- Child fidelity composes through the actual source constructor. -/\n" ++
    s!"private theorem {name} (v : value) (tree : Mixfix.t value)" ++
    String.join (raws.map (fun raw => s!" ({raw} : value)")) ++ "\n" ++
    s!"    (shape : v.it = .CaseV tree) (matching : Mixfix.eq_mixop tree {matching} = true)\n" ++
    "    (fields : Mixfix.args tree = [" ++ ", ".intercalate raws ++ "])" ++
    String.join hypotheses ++ s!"\n    (fuel : Nat) (x : Carrier .f{index})\n" ++
    s!"    (decoded : decode .f{index} fuel v = some x) :\n" ++
    s!"    admitted .f{index} x ∧ Rel v (encode .f{index} x) := by\n"
  let mut indent := "  "
  if guarded then
    text := text ++ "  cases fuel with\n  | zero => cases decoded\n  | succ fuel =>\n"
    indent := "    "
  text := text ++ indent ++ s!"rw [decoderBranch{index}_{selected} fuel v tree " ++
    " ".intercalate raws ++ " shape matching fields] at decoded\n"
  for (child, position) in children.zipIdx do
    text := text ++ indent ++ s!"cases d{position} : decode .f{child} fuel a{position} with\n" ++
      indent ++ s!"| none => rw [d{position}] at decoded; cases decoded\n" ++
      indent ++ s!"| some x{position} =>\n"
    indent := indent ++ "  "
    text := text ++ indent ++ s!"rw [d{position}] at decoded\n" ++ indent ++
      "dsimp only [Option.bind_some] at decoded\n" ++ indent ++
      s!"obtain ⟨accepted{position}, related{position}⟩ := " ++
      s!"h{position} fuel x{position} d{position}\n"
  text := text ++ indent ++ "injection decoded with equality\n" ++ indent ++ "subst x\n" ++
    indent ++ "constructor\n" ++ indent ++ "· exact ." ++ constructorName ++ " " ++
    " ".intercalate (values ++ positions.map (fun position => s!"accepted{position}")) ++ "\n" ++
    indent ++ s!"· have renderedShape : (encode .f{index} {value}).it = " ++
    s!".CaseV ({rendered}) := by\n" ++
    indent ++ "    dsimp only [encode]\n" ++
    indent ++ "    rw [" ++ encoderUnfolding.head! ++ "] <;> rfl\n" ++
    indent ++ "  refine Representation.Source.caseRelation shape renderedShape ?_ ?_\n" ++
    indent ++
    s!"  · exact Representation.Source.mixopTrans tree {matching} _ matching (by rfl)\n" ++
    indent ++ s!"  · have renderedFields : Mixfix.args (({rendered}) : Mixfix.t value) =\n" ++
    indent ++ s!"        {renderedFields} := by\n" ++
    indent ++ s!"      simp only [{argsRules}] <;> rfl\n" ++
    indent ++ "    rw [fields, renderedFields]\n" ++
    indent ++ "    all_goals simp only [canons]\n"
  if !positions.isEmpty then
    let left := "[" ++ ", ".intercalate (raws.map (fun raw => s!"canon {raw}")) ++ "]"
    let right := "[" ++ ", ".intercalate ((children.zip values).map fun (child, value) =>
      s!"canon (encode .f{child} {value})") ++ "]"
    text := text ++ indent ++ s!"    change {left} = {right}\n"
    for (child, position) in children.zipIdx do
      text := text ++ indent ++
        s!"    change canon a{position} = canon (encode .f{child} x{position}) " ++
        s!"at related{position}\n"
    text := text ++ indent ++ "    rw [" ++
      ", ".intercalate (positions.map (fun position => s!"related{position}")) ++ "]\n"
  return text ++ s!"\n#audit_axioms {name}"

/-- Emit conditional actual decoder fidelity and structural output admission.
The source derivation supplies the child fidelity hypotheses; no decoder-image domain is used. -/
def soundConstructorDeclarations (env : Env) (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut declarations := []
  for (family, index) in plan.families.toList.zipIdx do
    let some (.VariantT cases) := family.body | continue
    let .VarT name _ := family.source.it | throw "recursive variant soundness root is not nominal"
    let mut cursor := 0
    for ((sourceCase, constructorName), selected) in (cases.zip (ctorNames cases)).zipIdx do
      let count := (Mixfix.args sourceCase.nottyp.it).length
      let children := family.children.drop cursor |>.take count
      declarations := declarations ++ [soundBranch env index selected name.it constructorName
        (Mixfix.to_mixop sourceCase.nottyp.it) children family.guarded family.encoderUnfolding]
      cursor := cursor + count
    if cursor != family.children.length then throw "recursive soundness field arity mismatch"
  pure (Std.Format.text (boundedLines (
    s!"namespace {namespaceName}\n\n" ++ "\n\n".intercalate declarations ++
    s!"\n\nend {namespaceName}")))

end P4SpecTec.Codegen.RepresentationRecursive
