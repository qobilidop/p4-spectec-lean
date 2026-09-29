import P4SpecTec.Codegen.Certificates.Forward
import P4SpecTec.Codegen.Certificates.RepresentationField
import P4SpecTec.Refine.Quote

/-!
Producer certificates preserve independently specified source domains of successful
results. Selection inspects source operation structure; callable and type names are roles,
not a whitelist. A selected plan still requires an audited compiled theorem.
-/

namespace P4SpecTec.Codegen.Producer
open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Util.Source
open P4SpecTec.Codegen.Types P4SpecTec.Refine

/-- A checked first-match list updater over one two-field source constructor. -/
structure UpdatePlan where
  /-- Actual source callable. -/
  callable : String
  /-- Actual monomorphic element type. -/
  field : String
  /-- Actual single source constructor. -/
  caseDef : typcase
  /-- Generated constructor selected from that declaration. -/
  constructorName : String
  /-- Payload parameter type, in the source constructor's first position. -/
  payload : typ
  /-- Key parameter type, in the source constructor's second position. -/
  key : typ

private def sourceVariable (name : String) (type : typ') : exp := Q.e (.VarE (Q.i name)) type

private def listVariable (name : String) (element : typ) (bindingType : typ') : exp :=
  Q.e (.IterE (sourceVariable name element.it) (.mk .List [Q.v name bindingType []]))
    (.IterT element .List)

private def sameClause (left right : clause) : Bool :=
  (Reify.clause left).fmt.pretty 1000000 == (Reify.clause right).fmt.pretty 1000000

/-- Recognize the exact nil/equal-head/recurse-tail source operation, modulo source locations.
Every variable role, ordered guard, constructor, result and recursive argument is checked. -/
def updatePlan (env : Env) (d : Lang.Al.def) : Except String UpdatePlan := do
  unless env.mode == .pure do throw "producer update requires pure execution"
  let .FuncDecD name [] [.mk (.ExpP listType) _ _, .mk (.ExpP key) _ _,
      .mk (.ExpP payload) _ _] result [empty, hit, miss] none [] := d.it
    | throw "producer update needs a monomorphic three-argument, three-clause function"
  let .IterT element .List := listType.it
    | throw "producer update first input must be a list"
  let .VarT field [] := element.it | throw "producer update needs a named element type"
  unless typEq result.it listType.it do throw "producer update output differs from its input list"
  let some info := env.types.get? field.it | throw "producer update element is undeclared"
  let some (.VariantT [caseDef]) := info.deftyp
    | throw "producer update needs a single source constructor"
  unless info.tparams.isEmpty && !env.representation.rawExternTypes.contains field.it do
    throw "producer update element has parameters or an extra runtime constructor"
  let [first, second] := Mixfix.args caseDef.nottyp.it
    | throw "producer update constructor must have two fields"
  unless typEq first.it payload.it && typEq second.it key.it do
    throw "producer update constructor fields do not match payload and key"
  let .VarT _ [] := payload.it | throw "producer update payload must be a closed nominal type"
  let .VarT _ [] := key.it | throw "producer update key must be a closed nominal type"
  let (arguments, _, _) := empty.it
  let [a, b, c] := arguments | throw "producer update clause arity differs"
  let .ExpA a := a.it | throw "producer update input is not an expression"
  let .ExpA b := b.it | throw "producer update key is not an expression"
  let .ExpA c := c.it | throw "producer update payload is not an expression"
  let some (listName, [.List]) := Exp.iterVar? a | throw "producer update needs a list input"
  let .VarE keyName := b.it | throw "producer update key is not a variable"
  let .VarE payloadName := c.it | throw "producer update payload is not a variable"
  let (_, _, [_guard, binding, _comparison]) := hit.it
    | throw "producer update head clause has extra premises"
  let .LetPr pattern _ := binding.it | throw "producer update needs a head/tail binding"
  let .ConsE head tail := pattern.it | throw "producer update binding is not a list cons"
  let .CaseE tree := head.it | throw "producer update head is not a constructor"
  let [oldPayload, oldKey] := Mixfix.args tree | throw "producer update head field arity differs"
  let .VarE oldPayload := oldPayload.it | throw "producer update old payload is not a variable"
  let .VarE oldKey := oldKey.it | throw "producer update old key is not a variable"
  let some (tailName, [.List]) := Exp.iterVar? tail
    | throw "producer update tail is not a list variable"
  let names := [listName, keyName.it, payloadName.it, oldPayload.it, oldKey.it, tailName]
  unless names.eraseDups.length == names.length do throw "producer update roles overlap"
  let xs := listVariable listName element listType.it
  let tail := listVariable tailName element element.it
  let keyVar := sourceVariable keyName.it key.it
  let payloadVar := sourceVariable payloadName.it payload.it
  let oldKeyVar := sourceVariable oldKey.it key.it
  let oldPayloadVar := sourceVariable oldPayload.it payload.it
  let makeField (value key : exp) : Except String exp := do
    let some shape := Mixfix.fill (Mixfix.to_mixop caseDef.nottyp.it) [value, key]
      | throw "producer update constructor holes disagree"
    pure (Q.e (.CaseE shape) element.it)
  let replacement ← makeField payloadVar keyVar
  let original ← makeField oldPayloadVar oldKeyVar
  let args := [Q.ar (.ExpA xs), Q.ar (.ExpA keyVar), Q.ar (.ExpA payloadVar)]
  let test (kind : listpattern) := Q.pr (.IfPr (Q.e (.MatchE xs (.ListP kind)) .BoolT))
  let split := Q.pr (.LetPr (Q.e (.ConsE original tail) listType.it) xs)
  let compare (op : cmpop) := Q.pr (.IfPr (Q.e (.CmpE op .BoolT oldKeyVar keyVar) .BoolT))
  let recur := Q.e (.CallE name []
    [Q.ar (.ExpA tail), Q.ar (.ExpA keyVar), Q.ar (.ExpA payloadVar)]) listType.it
  let expectedEmpty := Q.cl args (Q.e (.ListE []) listType.it) [test .Nil]
  let expectedHit := Q.cl args (Q.e (.ConsE replacement tail) listType.it)
    [test .Cons, split, compare .EqOp]
  let expectedMiss := Q.cl args (Q.e (.ConsE original recur) listType.it)
    [test .Cons, split, compare .NeOp]
  unless sameClause empty expectedEmpty && sameClause hit expectedHit &&
      sameClause miss expectedMiss do
    throw "producer update body differs from ordered first-match replacement"
  return {
    callable := name.it
    field := field.it
    caseDef := caseDef
    constructorName := (Types.ctorNames [caseDef]).head!
    payload := payload
    key := key }

/-- An exact encoder for a closed source type, independent of codec availability. -/
partial def encoder (env : Env) (t : typ) : Except String String := do
  match t.it with
  | .VarT name [] =>
    let some info := env.types.get? name.it | throw "producer input type is undeclared"
    unless info.tparams.isEmpty do throw "producer input type has open parameters"
    if info.deftyp.isNone then
      unless env.defs.any (fun d => match d.it with
          | .ExternTypD n .. => n.it == name.it | _ => false) do
        throw "producer input type has no body or external declaration"
      return "@ToValue.toValue ExternValue P4SpecTec.Prelude.instToValueExternValue"
    pure (env.q (Types.toValueName name.it))
  | .VarT name arguments =>
    let some info := env.types[name.it]? | throw "producer input type is undeclared"
    unless info.tparams.length == arguments.length && info.deftyp.isSome do
      throw "producer input type arguments differ from its declaration"
    let encoders ← arguments.mapM (encoder env)
    let carriers := arguments.map (fun t => "(" ++ (typTerm env [] t.it).fmt.pretty ++ ")")
    pure ("@" ++ env.q (Types.toValueName name.it) ++ " " ++
      " ".intercalate (carriers ++ encoders.map (fun child => "⟨" ++ child ++ "⟩")))
  | .IterT element kind =>
    let child ← encoder env element
    let carrier := (typTerm env [] element.it).fmt.pretty
    let kind := if kind == .List then "List" else "Option"
    pure (s!"@ToValue.toValue ({kind} ({carrier})) " ++
      s!"(@P4SpecTec.Prelude.instToValue{kind} ({carrier}) ⟨{child}⟩)")
  | .TupleT [] => pure "@ToValue.toValue Unit (inferInstance : ToValue Unit)"
  | .TupleT [left, right] =>
    if let .TupleT (_ :: _ :: _) := env.resolve right.it then
      throw "producer tuple right carrier would flatten a hidden product"
    let a ← encoder env left
    let b ← encoder env right
    let leftCarrier := (typTerm env [] left.it).fmt.pretty
    let rightCarrier := (typTerm env [] right.it).fmt.pretty
    pure s!"@Representation.Source.pairEncoder ({leftCarrier}) ({rightCarrier}) ⟨{a}⟩ ⟨{b}⟩"
  | .BoolT => pure "@ToValue.toValue Bool P4SpecTec.Prelude.instToValueBool"
  | .NumT .NatT => pure "@ToValue.toValue Nat P4SpecTec.Prelude.instToValueNat"
  | .NumT .IntT => pure "@ToValue.toValue Int P4SpecTec.Prelude.instToValueInt"
  | .TextT => pure "@ToValue.toValue ByteText P4SpecTec.Prelude.instToValueByteText"
  | _ => throw "producer input encoding is outside the closed first-order fragment"

/-- Source admission of a value uses the actual quotation and an explicit encoder. -/
def admission (env : Env) (t : typ) (value : String) : Except String String := do
  pure ("(" ++ RepresentationFields.source env t ++ ") ((" ++ (← encoder env t) ++
    ") " ++ value ++ ")")

/-- The projections of a right-nested product of `count` results: `r.1, r.2.1, ..., r.2.2`. -/
def resultProjections (count : Nat) (result : String := "result") : List String :=
  (List.range count).map fun i =>
    let prefix_ := result ++ String.join (List.replicate i ".2")
    if i + 1 == count then prefix_ else prefix_ ++ ".1"

/-- The source types of a callable's inputs and results, and its generated name. -/
def signature (d : Lang.Al.def) : Except String (String × List typ × List typ) :=
  match d.it with
  | .FuncDecD name [] params result .. => do
    let types ← params.mapM fun param => match param.it with
      | .ExpP t => pure t | _ => throw "producer contract requires value parameters"
    pure (Names.funcName name.it, types, [result])
  | .RelD name sourceNotation inputs .. => do
    let arguments := Mixfix.args sourceNotation.it
    unless inputs.all (fun i => i ≥ 0 && i.toNat < arguments.length) &&
        inputs.eraseDups.length == inputs.length do
      throw "producer relation has invalid input positions"
    let (types, results) := Exp.splitArgs (inputs.map (·.toNat)) arguments
    pure (Names.relName name.it ++ ".run", types,
      if results.isEmpty then [Q.t (.TupleT [])] else results)
  | _ => throw "producer contract needs a monomorphic function or relation"

/-- The exact successful-result contract shared with compiled certificate checking.
A relation with several outputs states each output's domain.
This API constructs a statement only; an emitter must separately validate its proof plan. -/
def theoremType (env : Env) (d : Lang.Al.def) (externs : Bool := false) :
    Except String String := do
  unless env.mode == .pure do throw "producer contract requires pure execution"
  let (callable, types, results) ← signature d
  let binders := (types.zipIdx).map fun (t, index) =>
    s!"(p{index} : {(typTerm env [] t.it).fmt.pretty})"
  let premises ← (types.zipIdx).mapM fun (t, index) => admission env t s!"p{index}"
  let call := env.q callable ++ " " ++
    " ".intercalate ((List.range types.length).map (fun i => s!"p{i}"))
  let quantifiers := if binders.isEmpty then "" else "∀ " ++ " ".intercalate binders ++ ",\n"
  -- an extern-dependent callable runs under the generated extern instance
  let quantifiers := (if externs then s!"∀ [{env.q "Externs"}],\n" else "") ++ quantifiers
  pure (quantifiers ++
    "\n".intercalate (premises.map (· ++ " →")) ++
    s!"\n∀ result, {call} = some (.ok result) →\n" ++
    " ∧\n".intercalate (← (results.zip (resultProjections results.length)).mapM
      fun (t, value) => admission env t value))

/-- Emit an audited preservation proof for a source-checked first-match updater. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String String := do
  let plan ← updatePlan env d
  let field := env.q (Names.typeName plan.field)
  let ctor := field ++ "." ++ plan.constructorName
  let call := env.q (Names.funcName plan.callable)
  let owner := Names.funcName plan.callable
  let payload := (typTerm env [] plan.payload.it).fmt.pretty
  let key := (typTerm env [] plan.key.it).fmt.pretty
  let fieldType := Q.t (Q.varT plan.field [])
  let fieldPred := "fun field : " ++ field ++ " => " ++ (← admission env fieldType "field")
  let listIff := "@Representation.Source.encodedListIff " ++ field ++ " ⟨" ++
    (← encoder env fieldType) ++ "⟩ " ++ env.lib ++
    ".spec Representation.Source.externDomain (" ++ (Reify.typ fieldType).fmt.pretty ++ ")"
  let .mk origin arguments := plan.caseDef.typorigin.it
  let caseTerm := (Term.call "Q.tc" [Reify.mixfix plan.caseDef.nottyp.it Reify.typ,
    Reify.str origin.it, Reify.lst (arguments.map Reify.typ)]).fmt.pretty 1000000
  let payloadTerm := (Reify.typ plan.payload).fmt.pretty
  let keyTerm := (Reify.typ plan.key).fmt.pretty
  let fields := "[" ++ payloadTerm ++ ", " ++ keyTerm ++ "]"
  let substPayload ← RepresentationFields.identitySubstitution plan.payload
  let substKey ← RepresentationFields.identitySubstitution plan.key
  let statement ← theoremType env d
  let template := "
private theorem %OWNER%.preservesFields (P : %FIELD% → Prop)
    (fields : List %FIELD%) (key : %KEY%) (replacement : %PAYLOAD%)
    (input : ∀ f ∈ fields, P f) (accepted : P (%CTOR% replacement key)) :
    ∃ result, %CALL% fields key replacement = some (.ok result) ∧ ∀ f ∈ result, P f := by
  induction fields with
  | nil =>
    refine ⟨[], ?_, by simp⟩
    rw [%CALL%.eq_def]
    rfl
  | cons field tail ih =>
    cases field with
    | %CONSTRUCTOR% old stored =>
      have oldValid := input (%CTOR% old stored) (by simp)
      have tailValid : ∀ f ∈ tail, P f := by
        intro f hf
        exact input f (by simp [hf])
      obtain ⟨result, run, valid⟩ := ih tailValid
      cases equal : (stored == key) with
      | false =>
        refine ⟨%CTOR% old stored :: result, ?_, ?_⟩
        · rw [%CALL%.eq_def]
          simp only [bne, equal, run]
          rfl
        · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro oldValid valid
      | true =>
        refine ⟨%CTOR% replacement key :: tail, ?_, ?_⟩
        · rw [%CALL%.eq_def]
          simp only [bne, equal]
          rfl
        · simpa only [List.mem_cons, forall_eq_or_imp] using And.intro accepted tailValid
#audit_axioms %OWNER%.preservesFields

/-- Successful generated results preserve the independent source output domain. -/
theorem %OWNER%.producesSource :
    %STATEMENT% := by
  intro p0 p1 p2 h0 h1 h2 result run
  have accepted : (%PRED%) (%CTOR% p2 p1) := by
    apply Representation.Source.Valid.variant (Q.i %FIELDNAME%) [] [] [%CASE%] (%CASE%)
      %FIELDS% _ _ (by rfl)
    · simp
    · rfl
    · rfl
    · simp only [Lang.Il.typcase.nottyp, Domain.Mixfix.args,
        List.flatMap_cons, List.flatMap_nil, List.nil_append, List.cons_append]
      exact ⟨rfl, .cons (%SUBSTPAYLOAD%) (.cons (%SUBSTKEY%) .nil)⟩
    · simp only [Domain.Mixfix.args, List.flatMap_cons, List.flatMap_nil,
        List.nil_append, List.cons_append]
      exact .cons _ _ _ _ h2 (.cons _ _ _ _ h1 .nil)
  obtain ⟨actual, outcome, valid⟩ := %OWNER%.preservesFields (%PRED%) p0 p1 p2
    ((%LISTIFF% p0).mp h0) accepted
  have same := Option.some.inj (run.symm.trans outcome)
  cases same
  exact (%LISTIFF% _).mpr valid
#audit_axioms %OWNER%.producesSource
"
  pure (boundedLines (([("%OWNER%", owner), ("%FIELD%", field), ("%KEY%", key),
    ("%PAYLOAD%", payload), ("%CTOR%", ctor), ("%CALL%", call),
    ("%CONSTRUCTOR%", plan.constructorName), ("%STATEMENT%", statement.replace "\n" "\n    "),
    ("%PRED%", fieldPred), ("%FIELDNAME%", (Reify.str plan.field).fmt.pretty),
    ("%CASE%", caseTerm), ("%FIELDS%", fields), ("%SUBSTPAYLOAD%", substPayload),
    ("%SUBSTKEY%", substKey), ("%LISTIFF%", listIff)]).foldl
      (fun text (key, value) => text.replace key value) template))

end P4SpecTec.Codegen.Producer
