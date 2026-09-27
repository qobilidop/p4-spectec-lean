import P4SpecTec.Codegen.Certificates.ProducerConstructor

/-!
Producer certificates for recursive constructor builders. The source operation determines
scalar cases, recursive traversal columns and reconstructed output fields.
-/

namespace P4SpecTec.Codegen.ProducerDefault
open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Refine P4SpecTec.Codegen.Types

/-- One source-selected output branch and its checked traversal roles. -/
structure Branch where
  /-- Index in the declared result variant. -/
  outputIndex : Nat
  /-- Whether the branch reconstructs recursively produced fields. -/
  recursive : Bool
  /-- Whether the scalar downcast value is destructured before returning. -/
  scalarCases : Bool := false
  /-- The actual generated input object's single constructor. -/
  inputConstructor : String := ""
  /-- The independent source type of the copied outer identifier. -/
  outerKey : typ := Q.t .TextT
  /-- The independent source type of copied field identifiers. -/
  fieldKey : typ := Q.t .TextT
  /-- The actual output field variant. -/
  fieldName : String := ""
  /-- The actual generated output field constructor. -/
  fieldConstructor : String := ""

private def expressionEq (a b : exp) : Bool :=
  (Reify.exp a).fmt.pretty 1000000 == (Reify.exp b).fmt.pretty 1000000

private def named (t : typ') : Except String String := do
  let .VarT name [] := t | throw "producer builder needs a closed named type"
  pure name.it

private def casesOf (env : Env) (name : String) : Except String (List typcase) := do
  let some info := env.types[name]? | throw "producer builder type is undeclared"
  unless info.tparams.isEmpty do throw "producer builder type has parameters"
  let some (.VariantT cases) := info.deftyp | throw "producer builder needs a source variant"
  pure cases

private def caseIndex (cases : List typcase) (tree : Mixfix.t exp) : Except String Nat := do
  let some index := cases.findIdx? (fun c => Mixfix.eq_mixop c.nottyp.it tree)
    | throw "producer builder output constructor is undeclared"
  pure index

private def plainScalar (e : exp) : Bool :=
  match e.it with
  | .VarE _ | .NumE _ | .BoolE _ => true
  | .UpCastE target inner => match target.it, inner.it, inner.note with
    | .NumT .IntT, .NumE (.Nat _), .NumT .NatT => true
    | _, _, _ => false
  | _ => false

private def primitive (t : typ') : Bool :=
  match t with | .BoolT | .NumT .NatT | .NumT .IntT => true | _ => false

private def scalarBranch (cases : List typcase) (tree : Mixfix.t exp)
    (premises : List prem) : Except String Branch := do
  let index ← caseIndex cases tree
  let some selected := cases[index]? | throw "producer constructor index disappeared"
  unless (Mixfix.args selected.nottyp.it).all (fun t => primitive t.it) &&
      (Mixfix.args tree).all plainScalar do
    throw "producer scalar output is not primitive constructor data"
  match premises with
  | [guard, binding, test] | [guard, binding, test, _] =>
    let .IfPr _ := guard.it | throw "producer scalar prefix is not a guard"
    let .LetPr sourceVar cast := binding.it | throw "producer scalar prefix is not a downcast"
    let .VarE _ := sourceVar.it | throw "producer scalar downcast binding is not a variable"
    let .DownCastE _ _ := cast.it | throw "producer scalar needs an actual downcast"
    let .IfPr condition := test.it | throw "producer scalar lacks a constructor check"
    let .MatchE tested (.CaseP _) := condition.it
      | throw "producer scalar check is not a constructor match"
    unless expressionEq tested sourceVar do throw "producer scalar tests another value"
    if let [_, _, _, destructure] := premises then
      let .LetPr pattern tested := destructure.it
        | throw "producer scalar final premise is not a constructor binding"
      let .CaseE _ := pattern.it | throw "producer scalar binding is not a constructor"
      unless expressionEq tested sourceVar do throw "producer scalar destructures another value"
    pure { outputIndex := index, recursive := false, scalarCases := premises.length == 4 }
  | _ => throw "producer scalar has unsupported premises"

private def recursiveBranch (env : Env) (callable : String) (input output : typ')
    (cases : List typcase) (tree : Mixfix.t exp) (premises : List prem) : Except String Branch := do
  let [guard, binding, first, second, third] := premises
    | throw "producer builder needs guard/downcast and three traversal stages"
  let .IfPr _ := guard.it | throw "producer builder prefix is not a guard"
  let .LetPr pattern cast := binding.it | throw "producer builder needs object extraction"
  let .DownCastE castType _ := cast.it | throw "producer builder needs an actual downcast"
  let .CaseE inputTree := pattern.it | throw "producer builder needs an object constructor"
  let [inputKey, inputFields] := Mixfix.args inputTree
    | throw "producer builder object must have key and fields"
  let [outputKey, outputFields] := Mixfix.args tree
    | throw "producer builder result must have key and fields"
  unless expressionEq inputKey outputKey do throw "producer builder changed the outer key"
  unless Validate.columnPipeline env first second third do
    throw "producer builder columns lack checked lineage"
  let .IterPr extract (.mk .List [source] [key, selected]) := first.it
    | throw "producer builder extraction must yield key then recursive input"
  let .LetPr inputPattern _ := extract.it | throw "producer builder extraction is not a binding"
  let .CaseE inputFieldTree := inputPattern.it | throw "producer builder field is not a case"
  let .IterPr element (.mk .List [selected'] [produced]) := second.it
    | throw "producer builder recursion must yield one value"
  let .LetPr _ call := element.it | throw "producer builder recursion is not a binding"
  let .CallE callee [] [_] := call.it | throw "producer builder recursion is not a unary call"
  unless callee.it == callable && selected.id.it == selected'.id.it &&
      typEq selected.typ.it input && typEq produced.typ.it output do
    throw "producer builder call does not preserve the actual recursive roles"
  let .IterPr construct (.mk .List [key', produced'] [result]) := third.it
    | throw "producer builder reconstruction must zip keys then recursive outputs"
  unless key.id.it == key'.id.it && produced.id.it == produced'.id.it do
    throw "producer builder reconstruction changes column order"
  let .LetPr _ field := construct.it | throw "producer builder reconstruction is not a binding"
  let .CaseE fieldTree := field.it | throw "producer builder output field is not a constructor"
  let [oldValue, oldKey] := Mixfix.args inputFieldTree
    | throw "producer builder input field has unsupported arity"
  let [value, fieldKey] := Mixfix.args fieldTree
    | throw "producer builder output field has unsupported arity"
  let sourceVar (e : exp) (id : String) := match e.it with
    | .VarE name => name.it == id | _ => false
  unless sourceVar oldValue selected.id.it && sourceVar oldKey key.id.it &&
      sourceVar value produced.id.it && sourceVar fieldKey key.id.it do
    throw "producer builder field payload/key roles changed"
  unless Exp.iterVar? inputFields == some (source.id.it, [.List]) &&
      Exp.iterVar? outputFields == some (result.id.it, [.List]) do
    throw "producer builder result uses unrelated traversal columns"
  let sourceCases ← casesOf env (← named source.typ.it)
  let [sourceCase] := sourceCases | throw "producer builder input field has extra constructors"
  unless Mixfix.eq_mixop sourceCase.nottyp.it inputFieldTree do
    throw "producer builder input field constructor disagrees"
  let fieldName ← named result.typ.it
  let [fieldCase] ← casesOf env fieldName
    | throw "producer builder output field has extra constructors"
  unless Mixfix.eq_mixop fieldCase.nottyp.it fieldTree do
    throw "producer builder output field constructor disagrees"
  let [payloadType, declaredKey] := Mixfix.args fieldCase.nottyp.it
    | throw "producer builder output field declaration has wrong arity"
  unless typEq payloadType.it output do
    throw "producer builder output field payload differs from recursive output"
  let objectCases ← casesOf env (← named castType.it)
  let [objectCase] := objectCases | throw "producer builder input object has extra constructors"
  unless Mixfix.eq_mixop objectCase.nottyp.it inputTree do
    throw "producer builder input object constructor disagrees"
  pure {
    outputIndex := ← caseIndex cases tree
    recursive := true
    inputConstructor := (Types.ctorNames objectCases).head!
    outerKey := Q.t inputKey.note
    fieldKey := declaredKey
    fieldName := fieldName
    fieldConstructor := (Types.ctorNames [fieldCase]).head! }

/-- Select primitive constructors and self-recursive extraction/call/reconstruction clauses. -/
def plan (env : Env) (d : Lang.Al.def) : Except String (typ × typ × List Branch) := do
  unless env.mode == .pure && Validate.functionListColumns env d do
    throw "producer builder needs a pure singleton recursive column function"
  let .FuncDecD name [] [.mk (.ExpP input) _ _] output clauses none [] := d.it
    | throw "producer builder needs a unary monomorphic definition without fallback"
  let cases ← casesOf env (← named output.it)
  let branches ← clauses.mapM fun clause => do
    let (_, result, premises) := clause.it
    let .UpCastE target inner := result.it
      | throw "producer builder result must embed a declared source constructor"
    unless typEq target.it output.it do throw "producer builder result cast changed"
    let .CaseE tree := inner.it | throw "producer builder output is not a constructor"
    if premises.any (fun p => match p.it with | .IterPr .. => true | _ => false) then
      recursiveBranch env name.it input.it output.it cases tree premises
    else scalarBranch cases tree premises
  pure (input, output, branches)

private partial def totalProof (env : Env) (seen : List String) (t : typ) :
    Except String String := do
  match t.it with
  | .BoolT => pure "Representation.Source.Valid.bool _ _ rfl"
  | .NumT .NatT => pure "Representation.Source.Valid.nat _ _ rfl"
  | .NumT .IntT => pure "Representation.Source.Valid.int _ _ rfl"
  | .TextT => pure "Representation.Source.Valid.text _ _ rfl"
  | .VarT name [] =>
    unless !seen.contains name.it do throw "producer scalar alias is recursive"
    let some info := env.types[name.it]? | throw "producer scalar alias is undeclared"
    unless info.tparams.isEmpty do throw "producer scalar alias is parameterized"
    let some (.PlainT child) := info.deftyp | throw "producer leaf is not a primitive alias"
    let proof ← totalProof env (name.it :: seen) child
    let identity ← RepresentationFields.identitySubstitution child
    let childTerm := (Reify.typ child).fmt.pretty 1000000
    pure ("(by\n  apply Representation.Source.Valid.alias (Q.i " ++ name.it.quote ++
      ") [] [] (" ++ childTerm ++ ") (" ++ childTerm ++ ") _ (by rfl)\n" ++
      "  · exact ⟨rfl, .cons (" ++ identity ++ ") .nil⟩\n  · exact " ++
      proof.replace "\n" "\n    " ++ ")")
  | _ => throw "producer copied leaf does not have proved total primitive admission"

private def indent (amount : Nat) (s : String) : String :=
  let padding := String.ofList (List.replicate amount ' ')
  padding ++ s.replace "\n" ("\n" ++ padding)

private def scalarProof (owner : String) (index : Nat) (branch : Branch) : String :=
  "apply Produces.bindAny\nintro _\napply Produces.bindAny\nintro scalar\n" ++
    "apply Produces.bindAny\nintro _\n" ++
    (if branch.scalarCases then "cases scalar <;>\n  first\n" else "first\n") ++
    (if branch.scalarCases then "  " else "") ++
    "| apply Produces.pure\n" ++ (if branch.scalarCases then "    " else "  ") ++
    s!"apply {owner}.producerCase{index}\n" ++
    (if branch.scalarCases then "    " else "  ") ++
    "all_goals first\n" ++ (if branch.scalarCases then "      " else "    ") ++
    "| exact Representation.Source.Valid.nat _ _ rfl\n" ++
    (if branch.scalarCases then "      " else "    ") ++
    "| exact Representation.Source.Valid.int _ _ rfl\n" ++
    (if branch.scalarCases then "      " else "    ") ++
    "| exact Representation.Source.Valid.bool _ _ rfl\n" ++
    (if branch.scalarCases then "  " else "") ++ "| exact Produces.error _ _"

private def recursiveProof (env : Env) (owner : String) (index : Nat) (output : typ)
    (branch : Branch) : Except String String := do
  let carrier := (typTerm env [] output.it).fmt.pretty
  let fieldCarrier := env.q (Names.typeName branch.fieldName)
  let fieldType := Q.t (Q.varT branch.fieldName [])
  let fieldPredicate := "fun field : " ++ fieldCarrier ++ " => " ++
    (← Producer.admission env fieldType "field")
  let keyCarrier := (typTerm env [] branch.fieldKey.it).fmt.pretty
  let keyProof ← totalProof env [] branch.fieldKey
  let outerProof ← totalProof env [] branch.outerKey
  let listProof := "(@Representation.Source.encodedListIff " ++ fieldCarrier ++ " ⟨" ++
    (← Producer.encoder env fieldType) ++ "⟩ " ++ env.lib ++
    ".spec Representation.Source.externDomain (" ++ (Reify.typ fieldType).fmt.pretty ++
    ") fs).mpr accepted"
  pure ("apply Produces.bindAny\nintro _\napply Produces.bindAny\nintro object\n" ++
    "cases object with\n| " ++ branch.inputConstructor ++ " ident fields =>\n" ++ indent 2 (
    "apply Produces.bindAny\nintro pairs\n" ++
    "apply Produces.bind (output := P)\n" ++ indent 2 (
      "(m := (pairs.map Prod.snd).mapM (fun t =>\n" ++
      "  (ExceptT.mk (rec t) : Eval " ++ carrier ++ ") >>= pure))\n" ++
      "(input := fun values : List " ++ carrier ++ " => ∀ x ∈ values, P x)") ++ "\n" ++
    "· apply Produces.mapM\n  intro t _\n  intro output found\n" ++
    "  have found : rec t = some (.ok output) := by\n" ++
    "    simpa only [bind_pure, ExceptT.run, ExceptT.mk] using found\n" ++
    "  exact ih t (.ok output) found output rfl\n" ++
    "· intro values valid\n" ++ indent 2 (
      "apply Produces.bind (output := P)\n" ++ indent 2 (
        "(m := ((pairs.map Prod.fst).zip values).mapM (fun (pair : " ++ keyCarrier ++
        " × " ++ carrier ++ ") =>\n  (pure (" ++ fieldCarrier ++ "." ++
        branch.fieldConstructor ++ " pair.2 pair.1) : Eval " ++ fieldCarrier ++ ")))\n" ++
        "(input := fun fs : List " ++ fieldCarrier ++ " => ∀ f ∈ fs, (" ++
        fieldPredicate ++ ") f)") ++ "\n" ++
      "· apply Produces.mapM\n  intro pair member\n  apply Produces.pure\n" ++
      s!"  exact {owner}.producerField{index} pair.2 pair.1\n" ++
      "    (valid pair.2 (List.of_mem_zip member).2) (" ++
      keyProof.replace "\n" "\n    " ++ ")\n" ++
      "· intro fs accepted\n  apply Produces.pure\n" ++
      s!"  exact {owner}.producerCase{index} ident fs (" ++
      outerProof.replace "\n" "\n    " ++ ")\n    (" ++ listProof ++ ")")))

private def branchesProof : List String → String
  | [] => "exact Produces.error _ _"
  | [last] => last
  | first :: rest => "apply Produces.orElse\n· " ++ first.replace "\n" "\n  " ++
      "\n· " ++ (branchesProof rest).replace "\n" "\n  "

/-- Emit actual outcome induction and source-constructor proofs for the checked builder. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String String := do
  let (input, output, branches) ← plan env d
  let outputName ← named output.it
  let owner := Names.funcName d.it.id.it
  let qualified := env.q owner
  let mut helpers := ""
  let mut proofs := []
  for (branch, index) in branches.zipIdx do
    helpers := helpers ++ (← ProducerConstructor.declarations env outputName branch.outputIndex
      s!"{owner}.producerCase{index}") ++ "\n"
    if branch.recursive then
      helpers := helpers ++ (← ProducerConstructor.declarations env branch.fieldName 0
        s!"{owner}.producerField{index}") ++ "\n"
      proofs := proofs ++ [← recursiveProof env owner index output branch]
    else proofs := proofs ++ [scalarProof owner index branch]
  let predicate := "fun value : " ++ (typTerm env [] output.it).fmt.pretty ++ " => " ++
    (← Producer.admission env output "value")
  let rendered := s!"private theorem {owner}.producesSourceAll " ++
    "(input : " ++ (typTerm env [] input.it).fmt.pretty ++ ") " ++
    "(result : " ++ (typTerm env [] output.it).fmt.pretty ++ ")\n" ++
    s!"    (run : {qualified} input = some (.ok result)) : ({predicate}) result := by\n" ++
    "  let P := " ++ predicate ++ "\n" ++
    s!"  apply {qualified}.partial_correctness\n" ++
    "    (motive := fun _ q => ∀ v, q = .ok v → P v) ?_ input (.ok result) run result rfl\n" ++
    "  intro rec ih p0 q hq v eq\n  subst q\n" ++
    "  exact (show Produces P _ from by\n" ++ indent 4 (branchesProof proofs) ++ "\n  ) v hq\n" ++
    s!"#audit_axioms {owner}.producesSourceAll\n\n" ++
    "/-- Successful generated results preserve the independent source output domain. -/\n" ++
    s!"theorem {owner}.producesSource :\n" ++ indent 4 (← Producer.theoremType env d) ++
    " := by\n  intro p0 _ result run\n" ++
    s!"  exact {owner}.producesSourceAll p0 result run\n#audit_axioms {owner}.producesSource\n"
  pure (boundedLines (helpers ++ rendered))

end P4SpecTec.Codegen.ProducerDefault
