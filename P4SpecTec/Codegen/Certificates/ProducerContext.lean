import P4SpecTec.Refine.Quote
import P4SpecTec.Codegen.Certificates.RepresentationMap
import P4SpecTec.Codegen.Certificates.Builtin

/-!
Source-derived plans for context record updates. Exact reconstructed clauses fix ordered
checks, local list destructuring and update paths; names are extracted source roles.
A selected plan is metadata for a separately compiled and audited producer proof.
-/

namespace P4SpecTec.Codegen.ProducerContexts

open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Refine
open P4SpecTec.Codegen.Types

/-- A closed source record and its declaration-ordered fields. -/
structure Record where
  /-- Actual source type identifier. -/
  name : String
  /-- Actual source fields in declaration order. -/
  fields : List typfield

/-- A checked two-field path through actual closed records. -/
structure FieldPath where
  /-- Root context record. -/
  context : Record
  /-- Selected layer record. -/
  layer : Record
  /-- First source field label. -/
  outer : atom
  /-- Second source field label. -/
  inner : atom
  /-- Declared endpoint type. -/
  endpoint : typ

/-- A closed alias to a checked map of positional pairs in a list container. -/
structure Frame where
  /-- Actual source alias identifier. -/
  name : String
  /-- Actual polymorphic map identifier. -/
  map : String
  /-- Actual list-container identifier. -/
  set : String
  /-- Actual positional-pair identifier. -/
  pair : String
  /-- Actual generated list constructor. -/
  setConstructor : String
  /-- Actual generated pair constructor. -/
  pairConstructor : String
  /-- Exact key type argument. -/
  key : typ
  /-- Exact value type argument. -/
  payload : typ

/-- A checked nonempty-list tail update of a context record. -/
structure ExitPlan where
  /-- Source callable identifier. -/
  callable : String
  /-- Actual context-to-list path. -/
  path : FieldPath
  /-- Actual closed element type. -/
  element : typ

/-- A checked ordered scalar/scalar/list-head map insertion into three context layers. -/
structure InsertPlan where
  /-- Source callable identifier. -/
  callable : String
  /-- Closed source scope type identifier. -/
  scope : String
  /-- Actual scope constructors, in clause order. -/
  scopeConstructors : List String
  /-- Scalar map paths followed by the list-of-maps path. -/
  paths : List FieldPath
  /-- Checked concrete map representation. -/
  frame : Frame
  /-- Actual membership-check callable identifier. -/
  membership : String
  /-- Actual domain-projection callable identifier. -/
  domain : String
  /-- Actual builtin insertion identifier. -/
  insertion : String

private def sameExp (a b : exp) : Bool :=
  (Reify.exp a).fmt.pretty 1000000 == (Reify.exp b).fmt.pretty 1000000

private def sameClause (a b : clause) : Bool :=
  (Reify.clause a).fmt.pretty 1000000 == (Reify.clause b).fmt.pretty 1000000

private def sourceVar (n : String) (t : typ') : exp := Q.e (.VarE (Q.i n)) t

private def listVariable (n : String) (t : typ) (binding : typ') : exp :=
  Q.e (.IterE (sourceVar n t.it) (.mk .List [Q.v n binding []])) (.IterT t .List)

private def varName (e : exp) : Except String String := do
  let .VarE n := e.it | throw "context role must be a scalar variable"
  pure n.it

private def listName (e : exp) : Except String String := do
  let some (n, [.List]) := Exp.iterVar? e | throw "context role must be a list variable"
  pure n

private def nominal (t : typ) : Except String String := do
  let .VarT n [] := t.it | throw "context role must have a closed nominal type"
  pure n.it

private def declaration (env : Env) (n : String) : Except String Lang.Al.def := do
  let some d := env.defs.find? (fun d => d.it.id.it == n)
    | throw "context role has no source declaration"
  pure d

private def record (env : Env) (t : typ) : Except String Record := do
  let n ← nominal t
  let .TypD _ [] body _ := (← declaration env n).it
    | throw "context record must be a monomorphic type declaration"
  let .StructT fields := body.it | throw "context role must be a source record"
  unless !env.representation.hasRawExtern n &&
      (fields.map (fun f => Names.fieldName f.1.it)).eraseDups.length == fields.length do
    throw "context record has a runtime alternative or colliding generated fields"
  pure ⟨n, fields⟩

private def field (r : Record) (a : atom) : Except String typ := do
  let some (_, t) := r.fields.find? (fun f =>
    (Reify.atom f.1).fmt.pretty 1000000 == (Reify.atom a).fmt.pretty 1000000)
    | throw "context update selects an undeclared record field"
  pure t

private def fieldPath (env : Env) (contextType : typ) (p : path) :
    Except String FieldPath := do
  let .DotP parent inner := p.it | throw "context update needs a two-field path"
  let .DotP root outer := parent.it | throw "context update needs a two-field path"
  let .RootP := root.it | throw "context update path must start at its root"
  let context ← record env contextType
  let layerType ← field context outer
  let layer ← record env layerType
  let endpoint ← field layer inner
  unless typEq root.note contextType.it && typEq parent.note layerType.it &&
      typEq p.note endpoint.it do throw "context path type notes disagree with source fields"
  pure ⟨context, layer, outer, inner, endpoint⟩

private def project (base : exp) (p : FieldPath) : exp :=
  Q.e (.DotE (Q.e (.DotE base p.outer) (.VarT (Q.i p.layer.name) [])) p.inner) p.endpoint.it

private def checkedFrame (env : Env) (t : typ) : Except String Frame := do
  let n ← nominal t
  if env.representation.hasRawExtern n then throw "context map has a runtime alternative"
  let .TypD _ [] body _ := (← declaration env n).it
    | throw "context map must be a closed alias"
  let .PlainT target := body.it | throw "context map must be a plain alias"
  let .VarT map [key, payload] := target.it | throw "context map alias needs two arguments"
  let _ ← nominal key
  let _ ← nominal payload
  let (_, _, set, pair) ← RepresentationMaps.checkSupport env (← declaration env map.it)
  let (_, sc) ← RepresentationContainers.listShape env (← declaration env set.it)
  let (_, _, pc) ← RepresentationContainers.pairShape env (← declaration env pair.it)
  pure ⟨n, map.it, set.it, pair.it, (ctorNames [sc]).head!, (ctorNames [pc]).head!,
    key, payload⟩

private def distinct (names : List String) : Except String Unit := do
  unless names.eraseDups.length == names.length do throw "context variable roles overlap"

/-- Recognize exact projection, nonempty-list check, cons binding and tail record update. -/
def exitPlan (env : Env) (d : Lang.Al.def) : Except String ExitPlan := do
  unless env.mode == .pure do throw "context producer needs pure execution"
  let .FuncDecD name [] [.mk (.ExpP contextType) _ _] result [clause] none [] := d.it
    | throw "context exit needs one monomorphic input and one clause"
  unless typEq result.it contextType.it do throw "context exit changes its result type"
  let ([arg], body, [binding, _, split]) := clause.it
    | throw "context exit clause shape differs"
  let .ExpA input := arg.it | throw "context exit input must be an expression"
  let inputName ← varName input
  let .UpdE base path output := body.it | throw "context exit must update its record"
  let plan ← fieldPath env contextType path
  unless plan.context.fields.length == 3 && plan.layer.fields.length == 1 do
    throw "context exit needs three layers and a single-field local layer"
  let .IterT element .List := plan.endpoint.it | throw "context exit endpoint must be a list"
  let _ ← nominal element
  let .LetPr xs _ := binding.it | throw "context exit needs a list projection binding"
  let xsName ← listName xs
  let .LetPr pattern _ := split.it | throw "context exit needs a cons binding"
  let .ConsE head tail := pattern.it | throw "context exit needs a cons pattern"
  let headName ← varName head
  let tailName ← listName tail
  distinct [inputName, xsName, headName, tailName]
  let input := sourceVar inputName contextType.it
  let xs := listVariable xsName element plan.endpoint.it
  let tail := listVariable tailName element element.it
  let expected := Q.cl [Q.ar (.ExpA input)]
    (Q.e (.UpdE input path tail) contextType.it)
    [Q.pr (.LetPr xs (project input plan)),
     Q.pr (.IfPr (Q.e (.MatchE xs (.ListP .Cons)) .BoolT)),
     Q.pr (.LetPr (Q.e (.ConsE (sourceVar headName element.it) tail) plan.endpoint.it) xs)]
  unless sameExp base input && sameExp output tail && sameClause clause expected do
    throw "context exit differs from exact ordered list-tail removal"
  pure ⟨name.it, plan, element⟩

private structure Branch where
  path : FieldPath
  scopeCase : mixop
  constructorName : String
  membership : String
  domain : String
  insertion : String

private def premiseAt (premises : List prem) (index : Nat) : Except String prem := do
  let some p := premises[index]? | throw "context insertion premise index is absent"
  pure p

private def insertBranch (env : Env) (contextType scopeType key payload : typ)
    (frame : Frame) (isLocal : Bool) (clause : clause) : Except String Branch := do
  let ([scopeArg, contextArg, keyArg, valueArg], output, premises) := clause.it
    | throw "context insertion has wrong clause arity"
  let inputs ← [scopeArg, contextArg, keyArg, valueArg].mapM fun a => match a.it with
    | .ExpA e => pure e | _ => throw "context insertion requires expression arguments"
  let names ← inputs.mapM varName
  let scope := sourceVar names[0]! scopeType.it
  let context := sourceVar names[1]! contextType.it
  let keyVar := sourceVar names[2]! key.it
  let valueVar := sourceVar names[3]! payload.it
  let outputName ← varName output
  let some guard := premises.head? | throw "context insertion lacks a scope guard"
  let .IfPr test := guard.it | throw "context insertion scope guard must be first"
  let .MatchE _ (.CaseP scopeCase) := test.it
    | throw "context insertion needs an exact scope constructor match"
  let scopeName ← nominal scopeType
  let .TypD _ [] scopeBody _ := (← declaration env scopeName).it
    | throw "context scope must be monomorphic"
  let .VariantT cases := scopeBody.it | throw "context scope must be a variant"
  let indexed := cases.zip (ctorNames cases)
  let some (_, ctor) := indexed.find? (fun (c, _) =>
    (Mixfix.args c.nottyp.it).isEmpty &&
      (Reify.mixop (Mixfix.to_mixop c.nottyp.it)).fmt.pretty 1000000 ==
      (Reify.mixop scopeCase).fmt.pretty 1000000)
    | throw "context scope guard is not a declared nullary constructor"
  let expectedCount := if isLocal then 7 else 5
  unless premises.length == expectedCount do throw "context insertion premise count differs"
  let some last := premises.getLast? | throw "context insertion lacks its record update"
  let .LetPr target update := last.it | throw "context insertion needs an output binding"
  let .UpdE _ path replacement := update.it | throw "context insertion must update a record"
  let selected ← fieldPath env contextType path
  let frameType := Q.t (Q.varT frame.name [])
  unless typEq selected.endpoint.it (if isLocal then .IterT frameType .List else frameType.it) do
    throw "context insertion path does not select the shared map representation"
  let .LetPr binding _ := (← premiseAt premises 1).it
    | throw "context insertion needs a frame projection"
  let frameName ← if isLocal then listName binding else varName binding
  let mut extraNames := [frameName, outputName]
  let mut frameVar := sourceVar frameName frameType.it
  let mut initialPremises := [Q.pr (.IfPr (Q.e (.MatchE scope (.CaseP scopeCase)) .BoolT))]
  let mut expectedReplacement := replacement
  if isLocal then
    let xs := listVariable frameName frameType selected.endpoint.it
    let .LetPr pattern _ := (← premiseAt premises 3).it
      | throw "context insertion local branch needs a cons binding"
    let .ConsE head tail := pattern.it | throw "context insertion local branch needs a cons"
    let headName ← varName head
    let tailName ← listName tail
    let .ConsE newHead _ := replacement.it
      | throw "context insertion local replacement needs a cons"
    let newName ← varName newHead
    extraNames := extraNames ++ [headName, tailName, newName]
    frameVar := sourceVar headName frameType.it
    let tail := listVariable tailName frameType frameType.it
    expectedReplacement := Q.e (.ConsE (sourceVar newName frameType.it) tail) selected.endpoint.it
    initialPremises := initialPremises ++ [Q.pr (.LetPr xs (project context selected)),
      Q.pr (.IfPr (Q.e (.MatchE xs (.ListP .Cons)) .BoolT)),
      Q.pr (.LetPr (Q.e (.ConsE frameVar tail) selected.endpoint.it) xs)]
  else
    initialPremises := initialPremises ++ [Q.pr (.LetPr frameVar (project context selected))]
  let offset := if isLocal then 4 else 2
  let .IfPr rejection := (← premiseAt premises offset).it
    | throw "context insertion needs an ordered duplicate check"
  let .UnE .NotOp .BoolT member := rejection.it
    | throw "context insertion duplicate guard must negate membership"
  let .CallE memberId _ [domainArg, _] := member.it
    | throw "context insertion membership needs two arguments"
  let .ExpA domainExp := domainArg.it | throw "context insertion domain must be an expression"
  let .CallE domainId _ _ := domainExp.it | throw "context insertion needs domain projection"
  let .VarT set [setKey] := domainExp.note
    | throw "context insertion domain result must be a unary container"
  unless set.it == frame.set && typEq setKey.it key.it do
    throw "context insertion domain type differs from key container"
  let .LetPr newFrame call := (← premiseAt premises (offset + 1)).it
    | throw "context insertion needs a map operation binding"
  let newName ← varName newFrame
  if isLocal then
    let .ConsE newHead _ := expectedReplacement.it
      | throw "context insertion local replacement must be a cons"
    unless (← varName newHead) == newName do
      throw "context insertion local update does not use the inserted frame"
  if !isLocal then extraNames := extraNames ++ [newName]
  distinct (names ++ extraNames)
  let .CallE insertId _ _ := call.it | throw "context insertion update must be a call"
  let builtin ← declaration env insertId.it
  unless insertId.it == "add_map" do throw "context insertion needs the actual add_map primitive"
  let _ ← BuiltinCertificates.checkSupport env builtin
  let callType := Q.varT frame.map [key, payload]
  let domainCall := Q.e (.CallE domainId [key, payload] [Q.ar (.ExpA frameVar)])
    (Q.varT frame.set [key])
  let membership := Q.e (.CallE memberId [key]
    [Q.ar (.ExpA domainCall), Q.ar (.ExpA keyVar)]) .BoolT
  let insert := Q.e (.CallE insertId [key, payload]
    [Q.ar (.ExpA frameVar), Q.ar (.ExpA keyVar), Q.ar (.ExpA valueVar)]) callType
  let updated := sourceVar newName frameType.it
  let suffix := [Q.pr (.IfPr (Q.e (.UnE .NotOp .BoolT membership) .BoolT)),
    Q.pr (.LetPr updated insert),
    Q.pr (.LetPr (sourceVar outputName contextType.it)
      (Q.e (.UpdE context path (if isLocal then expectedReplacement else updated)) contextType.it))]
  let expected := Q.cl ([scope, context, keyVar, valueVar].map (fun e => Q.ar (.ExpA e)))
    (sourceVar outputName contextType.it) (initialPremises ++ suffix)
  unless sameExp target (sourceVar outputName contextType.it) &&
      sameClause clause expected do throw "context insertion body differs from exact checked recipe"
  pure ⟨selected, scopeCase, ctor, memberId.it, domainId.it, insertId.it⟩

/-- Recognize ordered insertion into two scalar map fields and one local map-list head.
All source constructors, type arguments, paths, guards and updates are checked; compiled
preservation remains a separate obligation. Guard callees may reject or fail arbitrarily. -/
def insertPlan (env : Env) (d : Lang.Al.def) : Except String InsertPlan := do
  unless env.mode == .pure do throw "context producer needs pure execution"
  let .FuncDecD name [] [.mk (.ExpP scope) _ _, .mk (.ExpP context) _ _,
      .mk (.ExpP key) _ _, .mk (.ExpP payload) _ _] result [first, second, third] none [] := d.it
    | throw "context insertion needs four monomorphic inputs and three ordered clauses"
  unless typEq result.it context.it do throw "context insertion changes the context type"
  let (_, _, premises) := first.it
  let some last := premises.getLast? | throw "context insertion has no final update"
  let .LetPr _ body := last.it | throw "context insertion output must be bound"
  let .UpdE _ path _ := body.it | throw "context insertion must update a record"
  let firstPath ← fieldPath env context path
  let frame ← checkedFrame env firstPath.endpoint
  unless typEq frame.key.it key.it && typEq frame.payload.it payload.it do
    throw "context insertion argument types disagree with frame alias"
  let branches ← [(false, first), (false, second), (true, third)].mapM fun (isLocal, c) =>
    insertBranch env context scope key payload frame isLocal c
  let [b0, b1, b2] := branches | throw "context insertion branch count differs"
  let paths := branches.map (·.path)
  unless (paths.map (fun p => Names.atomName p.outer.it)).eraseDups.length == 3 &&
      firstPath.context.fields.length == 3 &&
      (branches.map (·.constructorName)).eraseDups.length == 3 do
    throw "context insertion needs three distinct context layers and scope constructors"
  unless b1.path.layer.fields.length == 1 &&
      b2.path.layer.fields.length == 1 do
    throw "context insertion block and local layers must contain only their selected field"
  unless branches.all (fun b => b.membership == b0.membership &&
      b.domain == b0.domain && b.insertion == b0.insertion) do
    throw "context insertion clauses disagree on callees"
  pure ⟨name.it, ← nominal scope, branches.map (·.constructorName), paths, frame,
    b0.membership, b0.domain, b0.insertion⟩

end P4SpecTec.Codegen.ProducerContexts
