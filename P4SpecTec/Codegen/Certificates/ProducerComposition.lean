import P4SpecTec.Codegen.Certificates.ProducerConstructor

/-!
Source-domain composition for one-rule relations whose premises are sequential calls.
Every call consumes independently source-valid inputs; the available callee certificates
must be checked by the integration frontier before this candidate can claim coverage.
-/

namespace P4SpecTec.Codegen.ProducerComposition
open P4SpecTec.Lang.Il P4SpecTec.Refine P4SpecTec.Domain

private structure Binding where
  name : String
  type : typ
  term : String
  valid : String

private structure Step where
  callee : String
  arguments : List String
  argumentTypes : List typ
  admissions : List String
  output : Binding

/-- Checked source call dependencies and exact proof text for one relation rule. -/
structure Plan where
  /-- Actual source callable dependencies, in execution order. -/
  dependencies : List String
  /-- Private audited proofs for source nullary constructor arguments. -/
  helpers : String
  /-- Actual generated rule constructor. -/
  rule : String
  /-- Names introduced by the rule's intermediate outputs. -/
  intermediates : List String
  /-- Names introduced by the rule's actual successful call equations. -/
  runs : List String
  /-- A checked-order composition proof using the actual producer theorem names. -/
  proof : String
  /-- Source validity of each actual call's inputs after only its successful prefix. -/
  callType : String
  /-- Actual prefix producer composition establishing every call's input domain. -/
  callProof : String

private def variableName (e : exp) : Except String String := do
  let .VarE name := e.it | throw "producer composition expects a variable"
  pure name.it

private def expressionEq (a b : exp) : Bool :=
  (Reify.exp a).fmt.pretty 1000000 == (Reify.exp b).fmt.pretty 1000000

private def conjunction (items : List String) : String :=
  if items.isEmpty then "True" else " ∧ ".intercalate items

private def conjunctionProof : List String → String
  | [] => "trivial"
  | [proof] => proof
  | proof :: rest => "constructor\n· " ++ proof.replace "\n" "\n  " ++
      "\n· " ++ (conjunctionProof rest).replace "\n" "\n  "

private def factsProof (facts : List String) : String :=
  match facts with
  | [] => "trivial"
  | [fact] => "exact " ++ fact
  | facts => "exact ⟨" ++ ", ".intercalate facts ++ "⟩"

private def prefixProof (env : Env) (steps : List Step) : String :=
  String.join (steps.zipIdx.map fun (step, index) =>
    "have " ++ step.output.valid ++ " := " ++
      env.q (Names.funcName step.callee) ++ ".producesSource " ++
      " ".intercalate (step.arguments ++ step.admissions ++ [step.output.term, s!"run{index}"]) ++
      "\n")

/-- Inspect actual rule bindings, typed call arguments and the final output variable. -/
def plan (env : Env) (d : Lang.Al.def) : Except String Plan := do
  let _ ← Producer.theoremType env d
  -- Input-mode hints are already decoded into modes; other hints do not change execution.
  let .RelD name sourceNotation modes [group] none _ := d.it
    | throw "producer composition needs one relation group without fallback"
  let (groupName, (patterns, matched, common), [path]) := group.it
    | throw "producer composition needs one rule path"
  unless common.isEmpty && patterns.length == matched.length &&
      (patterns.zip matched).all (fun (a, b) => expressionEq a b) do
    throw "producer composition input patterns must be unchanged variables"
  let (pathName, premises, [output]) := path
    | throw "producer composition needs one output"
  unless !premises.isEmpty do throw "producer composition needs a call premise"
  let (inputTypes, outputTypes) := Exp.splitArgs (modes.map (·.toNat))
    (Mixfix.args sourceNotation.it)
  let [outputType] := outputTypes | throw "producer composition needs one output type"
  unless patterns.length == inputTypes.length do throw "producer composition input arity differs"
  let mut bindings : List Binding := []
  for ((pattern, type), index) in (patterns.zip inputTypes).zipIdx do
    let identifier ← variableName pattern
    unless Types.typEq pattern.note type.it && !bindings.any (·.name == identifier) do
      throw "producer composition input types or variable roles differ"
    bindings := bindings ++ [{
      name := identifier, type, term := s!"p{index}", valid := s!"h{index}" }]
  let finalName ← variableName output
  unless Types.typEq output.note outputType.it do throw "producer composition output type differs"
  let mut steps : List Step := []
  let mut helpers := ""
  let owner := Names.relName name.it
  for (premise, index) in premises.zipIdx do
    let .LetPr pattern expression := premise.it
      | throw "producer composition only supports successful call bindings"
    let identifier ← variableName pattern
    unless !bindings.any (·.name == identifier) do
      throw "producer composition overwrites a prior variable"
    let .CallE callee [] arguments := expression.it
      | throw "producer composition requires a monomorphic function call"
    let some info := env.funcs[callee.it]? | throw "producer composition callee is undeclared"
    unless info.kind == .defined && info.tparams.isEmpty &&
        Types.typEq pattern.note info.ret && Types.typEq expression.note info.ret do
      throw "producer composition requires a matching defined function signature"
    let types ← info.params.mapM fun p => match p with
      | .ExpP t => pure t | _ => throw "producer composition callee has non-value parameters"
    unless arguments.length == types.length do throw "producer composition call arity differs"
    let mut terms := []
    let mut facts := []
    for ((argument, type), argIndex) in (arguments.zip types).zipIdx do
      let .ExpA value := argument.it | throw "producer composition argument is not a value"
      unless Types.typEq value.note type.it do throw "producer composition argument type differs"
      match value.it with
      | .VarE sourceId =>
        let some binding := bindings.find? (·.name == sourceId.it)
          | throw "producer composition call uses an unbound variable"
        unless Types.typEq binding.type.it type.it do
          throw "producer composition call changes a variable's source domain"
        terms := terms ++ [binding.term]
        facts := facts ++ [binding.valid]
      | .CaseE tree =>
        unless (Mixfix.args tree).isEmpty do
          throw "producer composition only supports nullary constructor constants"
        let .VarT typeName [] := type.it
          | throw "producer composition constructor constant needs a named type"
        let some typeInfo := env.types[typeName.it]?
          | throw "producer composition constant type is undeclared"
        let some (.VariantT cases) := typeInfo.deftyp
          | throw "producer composition constant type is not a variant"
        let some caseIndex := cases.findIdx? (fun c => Mixfix.eq_mixop c.nottyp.it tree)
          | throw "producer composition constant constructor is undeclared"
        let ctor := (Types.ctorNames cases)[caseIndex]!
        let helper := s!"{owner}.producerConstant{index}_{argIndex}"
        helpers := helpers ++ (← ProducerConstructor.declarations env typeName.it caseIndex helper)
        terms := terms ++ [env.q (Names.typeName typeName.it) ++ "." ++ ctor]
        facts := facts ++ [helper]
      | _ => throw "producer composition argument needs a prior variable or source constant"
    let isLast := index + 1 == premises.length
    unless !isLast || Types.typEq info.ret outputType.it do
      throw "producer composition final call changes the declared output source domain"
    unless !isLast || identifier == finalName do
      throw "producer composition final call is not the relation output"
    unless isLast || identifier != finalName do
      throw "producer composition returns before its last call"
    let binding : Binding := {
      name := identifier
      type := Q.t info.ret
      term := if isLast then "result" else s!"value{index}"
      valid := s!"accepted{index}" }
    bindings := bindings ++ [binding]
    steps := steps ++ [{
      callee := callee.it
      arguments := terms
      argumentTypes := types
      admissions := facts
      output := binding }]
  let proof := prefixProof env steps ++ "exact accepted" ++ toString (steps.length - 1)
  let initialBinders := (inputTypes.zipIdx).map fun (type, index) =>
    s!"(p{index} : {(Types.typTerm env [] type.it).fmt.pretty})"
  let initialAdmissions ← (inputTypes.zipIdx).mapM fun (type, index) =>
    Producer.admission env type s!"p{index}"
  let mut callTypes := []
  let mut callProofs := []
  for (step, index) in steps.zipIdx do
    let previous := steps.take index
    let prefixBinders := previous.map fun prior =>
      s!"({prior.output.term} : {(Types.typTerm env [] prior.output.type.it).fmt.pretty})"
    let runs := previous.map fun prior =>
      env.q (Names.funcName prior.callee) ++ " " ++
        " ".intercalate prior.arguments ++ s!" = some (.ok {prior.output.term})"
    let arguments ← (step.argumentTypes.zip step.arguments).mapM fun (type, value) =>
      Producer.admission env type value
    let binders := if prefixBinders.isEmpty then "" else
      "∀ " ++ " ".intercalate prefixBinders ++ ", "
    callTypes := callTypes ++ ["(" ++ binders ++
      String.join (runs.map (· ++ " → ")) ++ conjunction arguments ++ ")"]
    let names := previous.map (·.output.term) ++
      (List.range index).map (fun i => s!"run{i}")
    let intros := if names.isEmpty then "" else "intro " ++ " ".intercalate names ++ "\n"
    callProofs := callProofs ++ [intros ++ prefixProof env previous ++ factsProof step.admissions]
  let callType := (if initialBinders.isEmpty then "" else
      "∀ " ++ " ".intercalate initialBinders ++ ", ") ++
    String.join (initialAdmissions.map (· ++ " → ")) ++ conjunction callTypes
  let initialNames := (List.range inputTypes.length).map (fun i => s!"p{i}") ++
    (List.range inputTypes.length).map (fun i => s!"h{i}")
  let callProof := (if initialNames.isEmpty then "" else
      "intro " ++ " ".intercalate initialNames ++ "\n") ++ conjunctionProof callProofs
  let rule := if groupName.it.isEmpty && pathName.it.isEmpty then "rule0"
    else Names.ruleName groupName.it pathName.it
  pure {
    dependencies := (steps.map (·.callee)).eraseDups
    helpers := helpers
    rule := rule
    intermediates := (steps.dropLast.map (·.output.term))
    runs := (List.range steps.length).map (fun i => s!"run{i}")
    proof := proof
    callType := callType
    callProof := callProof }

/-- Actual producer dependencies required before the candidate is eligible for coverage. -/
def dependencies (env : Env) (d : Lang.Al.def) : Except String (List String) := do
  pure (← plan env d).dependencies

/-- Emit an audited source-domain composition over the actual generated rule derivation. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String String := do
  let checked ← plan env d
  let .RelD name sourceNotation modes .. := d.it
    | throw "producer composition needs a relation"
  let (inputs, _) := Exp.splitArgs (modes.map (·.toNat)) (Mixfix.args sourceNotation.it)
  let params := (List.range inputs.length).map (fun i => s!"p{i}")
  let assumptions := (List.range inputs.length).map (fun i => s!"h{i}")
  let owner := Names.relName name.it
  pure (boundedLines (checked.helpers ++ "\n" ++
    "/-- Actual call composition preserves the independently stated source output domain. -/\n" ++
    s!"theorem {owner}.producesSource :\n    " ++
    (← Producer.theoremType env d).replace "\n" "\n    " ++ " := by\n  intro " ++
    " ".intercalate (params ++ assumptions ++ ["result", "run"]) ++ "\n" ++
    "  have derivation := " ++ env.q owner ++ ".run_sound " ++
    " ".intercalate (params ++ ["result", "run"]) ++ "\n" ++
    "  cases derivation with\n  | " ++ checked.rule ++ " " ++
    " ".intercalate checked.runs ++ " =>\n    " ++
    (if checked.intermediates.isEmpty then "" else
      "rename_i " ++ " ".intercalate checked.intermediates ++ "\n    ") ++
    checked.proof.replace "\n" "\n    " ++ s!"\n#audit_axioms {owner}.producesSource\n"))

/-- Exact call-input contract, quantified over successful prefixes rather than final success. -/
def callAdmissionType (env : Env) (d : Lang.Al.def) : Except String String := do
  return (← plan env d).callType

/-- Emit call admission alongside the producer, reusing its source-constant proof helpers. -/
def callAdmissionDeclarations (env : Env) (d : Lang.Al.def) : Except String String := do
  let checked ← plan env d
  let owner := Names.relName d.it.id.it
  return boundedLines (
    "/-- Successful earlier calls establish every source input of the next actual call. -/\n" ++
    s!"theorem {owner}.callArgumentsSource : {checked.callType} := by\n  " ++
    checked.callProof.replace "\n" "\n  " ++ s!"\n#audit_axioms {owner}.callArgumentsSource\n")

end P4SpecTec.Codegen.ProducerComposition
