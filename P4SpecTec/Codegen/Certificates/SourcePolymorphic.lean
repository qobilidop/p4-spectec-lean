import P4SpecTec.Codegen.Certificates.SourceBuiltin
import P4SpecTec.Codegen.Certificates.SourcePolymorphicRepeat

/-!
Source-domain contracts for structurally checked polymorphic membership, pair projections,
empty containers, Boolean choice and natural repetition.
Parameter codecs remain explicit, and source-domain preservation adds no equality law to the
independent execution correspondence certificates.
-/

namespace P4SpecTec.Codegen.SourcePolymorphic
open P4SpecTec.Lang.Il P4SpecTec.Codegen.SourceBuiltinCertificates

/-- A supported polymorphic operation with independent source input and output domains. -/
structure Plan where
  /-- Declared parameter names, in source order. -/
  parameters : List String
  /-- Actual source input contracts. -/
  inputs : List Field
  /-- Actual source result contract. -/
  output : Field
  /-- The projected pair component; absent for all other supported operations. -/
  projection : Option Nat
  /-- Declared list container whose empty constructor is the whole result, if any. -/
  emptyContainer : Option String
  /-- Whether two Boolean-guarded clauses return the corresponding parameter. -/
  booleanChoice : Bool
  /-- Whether the actual definition is natural repetition of an admitted input. -/
  repetition : Bool

/-- A clause selecting one value parameter when the Boolean parameter has this value. -/
private def choiceBranch? (parameters : List String) (expected : Bool)
    (selected : Nat) (clause : clause) : Bool := Id.run do
  let (arguments, output, premises) := clause.it
  let [bArg, tArg, fArg] := arguments | return false
  let .ExpA b := bArg.it | return false
  let .ExpA t := tArg.it | return false
  let .ExpA f := fArg.it | return false
  let .VarE bName := b.it | return false
  let .VarE tName := t.it | return false
  let .VarE fName := f.it | return false
  unless BuiltinCertificates.shape parameters b.note == "bool" &&
      BuiltinCertificates.shape parameters t.note == "$0" &&
      BuiltinCertificates.shape parameters f.note == "$0" do return false
  let [premise] := premises | return false
  let .IfPr condition := premise.it | return false
  let .CmpE .EqOp .BoolT lhs rhs := condition.it | return false
  let .VarE conditionName := lhs.it | return false
  let .BoolE conditionValue := rhs.it | return false
  let .VarE outputName := output.it | return false
  return bName.it != tName.it && bName.it != fName.it && tName.it != fName.it &&
    bName.it == conditionName.it && conditionValue == expected &&
    BuiltinCertificates.shape parameters condition.note == "bool" &&
    BuiltinCertificates.shape parameters lhs.note == "bool" &&
    BuiltinCertificates.shape parameters rhs.note == "bool" &&
    BuiltinCertificates.shape parameters output.note == "$0" &&
    outputName.it == (if selected == 1 then tName.it else fName.it)

/-- Recognize the complete two-clause source choice, independently of its callable name. -/
private def booleanChoice (parameters : List String) (inputs : List param)
    (result : typ) (clauses : List clause) : Bool :=
  parameters.length == 1 &&
  BuiltinCertificates.shape parameters result.it == "$0" &&
  (inputs.map fun p => match p.it with
    | .ExpP type => BuiltinCertificates.shape parameters type.it
    | _ => "callback") == ["bool", "$0", "$0"] &&
  match clauses with
  | [whenTrue, whenFalse] =>
    choiceBranch? parameters true 1 whenTrue &&
      choiceBranch? parameters false 2 whenFalse
  | _ => false

/-- Recognize a zero-input empty container by its declared shape and exact expression,
including the map alias's underlying paired-list container. -/
private def emptyContainer? (env : Env) (parameters : List String)
    (inputs : List param) (result : typ) (clauses : List clause) :
    Option String := do
  guard inputs.isEmpty
  let [clause] := clauses | none
  let (arguments, output, premises) := clause.it
  guard (arguments.isEmpty && premises.isEmpty)
  let .VarT resultName _ := result.it | none
  let declaration ← env.defs.find? fun d => match d.it with
    | .TypD name .. => name.it == resultName.it
    | _ => false
  let (outer, elementShape) ←
    if parameters.length == 1 &&
        BuiltinCertificates.shape parameters result.it == s!"{resultName.it}($0)" then do
      let (_, constructor) ← (RepresentationContainers.listShape env declaration).toOption
      let .Brack left (.Arg _) right := constructor.nottyp.it | none
      guard (left.it == .LBrace && right.it == .RBrace)
      some (resultName.it, "$0")
    else if parameters.length == 2 &&
        BuiltinCertificates.shape parameters result.it == s!"{resultName.it}($0,$1)" then do
      let (_, _, outer, inner) ← (RepresentationMaps.checkSupport env declaration).toOption
      let outerDeclaration ← env.defs.find? fun d => match d.it with
        | .TypD name .. => name.it == outer.it
        | _ => false
      let (_, constructor) ←
        (RepresentationContainers.listShape env outerDeclaration).toOption
      let .Brack left (.Arg _) right := constructor.nottyp.it | none
      guard (left.it == .LBrace && right.it == .RBrace)
      some (outer.it, s!"{inner.it}($0,$1)")
    else none
  let .CaseE (.Brack left (.Arg list) right) := output.it | none
  guard (left.it == .LBrace && right.it == .RBrace)
  let .ListE [] := list.it | none
  guard (BuiltinCertificates.shape parameters output.note ==
    s!"{outer}({elementShape})")
  guard (BuiltinCertificates.shape parameters list.note ==
    s!"list({elementShape})")
  some outer

/-- Recognize the actual defined operation using checked nominal codecs. -/
def planWithKnown (env : Env) (known : String → Option RepresentationFields.NominalContract)
    (d : Lang.Al.def) : Except String Plan := do
  unless env.mode == .pure do throw "source polymorphic contracts require pure execution"
  let .FuncDecD _ parameters inputs result clauses none _ := d.it
    | throw "source polymorphic contract needs a defined function"
  let parameters := parameters.map (·.it)
  unless !parameters.isEmpty && parameters.eraseDups.length == parameters.length &&
      parameters.all (fun name => !env.types.contains name) do
    throw "source polymorphic parameters must be distinct and fresh"
  let repetition := SourcePolymorphicRepeat.recognizes d
  let emptyContainer := emptyContainer? env parameters inputs result clauses
  let booleanChoice := booleanChoice parameters inputs result clauses
  let projection ← if emptyContainer.isSome || booleanChoice || repetition then pure none
    else if Validate.polymorphicMembership env d then pure none
    else if Validate.polymorphicPairProjection env d then do
      unless parameters.length == 2 && inputs.length == 1 do
        throw "source projection needs one two-parameter map"
      let [.mk (.ExpP input) _ _] := inputs | throw "source projection input is not first-order"
      unless BuiltinCertificates.shape parameters input.it == "map($0,$1)" do
        throw "source projection input is not the declared map"
      match BuiltinCertificates.shape parameters result.it with
      | "set($0)" => pure (some 0)
      | "set($1)" => pure (some 1)
      | _ => throw "source projection result is not a parameter set"
    else throw "unsupported polymorphic source operation"
  let inputs ← inputs.mapM fun p => match p.it with
    | .ExpP type => fieldWithKnown env known parameters type
    | _ => throw "source polymorphic callback is unsupported"
  let output ← fieldWithKnown env known parameters result
  return { parameters, inputs, output, projection, emptyContainer, booleanChoice, repetition }

/-- Recognize a standalone defined operation, resolving named codecs recursively. -/
def plan (env : Env) (d : Lang.Al.def) : Except String Plan := do
  planWithKnown env (namedKnown env) d

/-- Exact source coverage and successful-output contract for the selected defined operation. -/
def theoremType (env : Env) (d : Lang.Al.def) : Except String String := do
  let p ← plan env d
  return domainType env d p.parameters p.inputs p.output

/-- Complete source codecs required by the selected signature. -/
def dependencies (env : Env) (d : Lang.Al.def) : Except String (List String) := do
  let p ← plan env d
  return ((p.inputs ++ [p.output]).flatMap (·.dependencies)).eraseDups

/-- Reusable proof dependencies, independent of generated source codec sidecars. -/
def supportImports : List String := SourceBuiltinCertificates.supportImports

/-- Emit actual coverage witnesses and a proof about successful outputs from a resolved plan. -/
private def declarationsOfPlan (env : Env) (d : Lang.Al.def) (p : Plan) :
    Except String String := do
  let introLine := "intro " ++ " ".intercalate
    (p.inputs.zipIdx.flatMap fun (_, i) => [s!"p{i}", s!"hp{i}"]) ++ " result run\n"
  let encoding := "apply " ++ p.output.toContract.encodingProof
    (p.output.source env) p.output.codec ++ " result\n"
  let body ← if let some container := p.emptyContainer then
      pure ("simp only [" ++ env.q (Names.funcName d.it.id.it) ++
        ", ExceptT.run, pure, ExceptT.pure] at run\n" ++
        "cases Except.ok.inj (Option.some.inj run)\n" ++
        "simp [" ++ env.q (Names.typeName container) ++ ".admitted]")
    else if p.repetition then
      pure (SourcePolymorphicRepeat.proof (env.q (Names.funcName d.it.id.it)))
    else if p.booleanChoice then
      let functionName := env.q (Names.funcName d.it.id.it)
      pure ("cases p0 with\n" ++
        "| false =>\n" ++
        "  simp [" ++ functionName ++ ", Eval.check] at run\n" ++
        "  subst result\n" ++
        "  exact hp2\n" ++
        "| true =>\n" ++
        "  simp [" ++ functionName ++ ", Eval.check] at run\n" ++
        "  subst result\n" ++
        "  exact hp1")
    else match p.projection with
    | none => pure "trivial"
    | some selected =>
      let projection := if selected == 0 then ".1" else ".2"
      pure ("rcases p0 with ⟨xs⟩\n" ++
        "simp only [" ++ env.q (Names.funcName d.it.id.it) ++
        ", List.mapM_pure] at run\n" ++
        "cases Except.ok.inj (Option.some.inj run)\n" ++
        "intro value member\n" ++
        "obtain ⟨entry, originalMember, rfl⟩ := List.mem_map.mp member\n" ++
        "obtain ⟨entry, pairMember, rfl⟩ := List.mem_map.mp originalMember\n" ++
        "cases entry with | colon k v => exact (hp0 _ pairMember)" ++ projection)
  return domainDeclaration env d p.parameters p.inputs p.output (introLine ++ encoding ++ body)

/-- Emit actual coverage witnesses and successful-output proof for a standalone operation. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String String := do
  declarationsOfPlan env d (← plan env d)

/-- Render proof, exact statement and dependencies from one catalog-backed operation plan. -/
def complete (env : Env) (known : String → Option RepresentationFields.NominalContract)
    (d : Lang.Al.def) : Except String (String × String × List String) := do
  let p ← planWithKnown env known d
  return (← declarationsOfPlan env d p,
    domainType env d p.parameters p.inputs p.output,
    ((p.inputs ++ [p.output]).flatMap (·.dependencies)).eraseDups)

end P4SpecTec.Codegen.SourcePolymorphic
