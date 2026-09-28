import P4SpecTec.Codegen.Certificates.RunSound
import P4SpecTec.Codegen.Graph

/-!
Refinement theorems (design section 5.1, rung 3): per definition `d`, the
statement that the AL interpreter run on the quoted definition `d.al`
refines the generated code, discharged by `refine_al`
(`Tactic/Refine.lean`). A recursion group gets one theorem by strong
induction on the interpreter's fuel, with one conjunct per member, and a
corollary per member. The fragment the tactic covers is decided here,
syntactically (`unsupported`): a definition outside it gets no theorem
and is listed in the generated module with its reason, so that nothing is
`sorry`ed and the coverage is visible.
-/

namespace P4SpecTec.Codegen.Validate

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types
open P4SpecTec.Codegen.Exp
open P4SpecTec.Codegen.Funcs
open P4SpecTec.Codegen.Props

/-! ## The fragment -/

/-- A single membership clause with no calls or premises, admitting the actual
canonical equality law for each represented type parameter. This deliberately
leaves arbitrary polymorphic bodies outside the certified fragment. -/
def polymorphicMembership (env : Env) (d : Lang.Al.def) : Bool :=
  match d.it with
  | .FuncDecD _ tparams params ret [clause] none _ =>
    let (arguments, output, premises) := clause.it
    let direct := match output.it with
      | .MemE a b => (iterVar? a).isSome && (iterVar? b).isSome
      | _ => false
    !tparams.isEmpty && (tparams.map (·.it)).eraseDups.length == tparams.length &&
      tparams.all (fun p => !env.types.contains p.it) &&
      params.all (fun p => match p.it with | .ExpP .. => true | _ => false) &&
      arguments.length == params.length && typEq ret.it .BoolT &&
      premises.isEmpty && direct && (callsOfDef d).isEmpty
  | _ => false

/-- A pure polymorphic constructor projection over one checked paired list pattern.
The output selects an actual pattern binding; other iterated bodies remain excluded. -/
def polymorphicPairProjection (env : Env) (d : Lang.Al.def) : Bool :=
  match d.it with
  | .FuncDecD _ tparams params _ [clause] none _ =>
    let (arguments, output, premises) := clause.it
    let shape : Option Bool := do
      let [argument] := arguments | none
      let .ExpA pattern := argument.it | none
      let .CaseE inputCase := pattern.it | none
      let [inputField] := P4SpecTec.Domain.Mixfix.args inputCase | none
      let (left, right) ← pairIterationVars? inputField
      let .CaseE outputCase := output.it | none
      let [outputField] := P4SpecTec.Domain.Mixfix.args outputCase | none
      let (selected, iterations) ← iterVar? outputField
      pure ((selected == left.id.it || selected == right.id.it) && iterations == [.List])
    !tparams.isEmpty && (tparams.map (·.it)).eraseDups.length == tparams.length &&
      tparams.all (fun p => !env.types.contains p.it) && params.length == 1 &&
      params.all (fun p => match p.it with | .ExpP .. => true | _ => false) &&
      premises.isEmpty && (callsOfDef d).isEmpty && shape.getD false
  | _ => false

/-- Polymorphic clauses without premises or calls. Selection is syntactic only; the
remaining expression forms pass the ordinary fragment checks, and the kernel-checked
certificate carries the actual type registration through its freshness hypotheses. -/
def polymorphicPure (env : Env) (d : Lang.Al.def) : Bool :=
  match d.it with
  | .FuncDecD _ tparams params _ clauses none _ =>
    !tparams.isEmpty && !clauses.isEmpty &&
      (tparams.map (·.it)).eraseDups.length == tparams.length &&
      tparams.all (fun p => !env.types.contains p.it) &&
      params.all (fun p => match p.it with | .ExpP .. => true | _ => false) &&
      clauses.all (fun clause => let (arguments, _, premises) := clause.it
        arguments.length == params.length && premises.isEmpty) &&
      (callsOfDef d).isEmpty
  | _ => false

/-- Closed call type syntax uses known constructor names with their exact source arities.
Higher-order types and free type parameters need separate contracts. This checks syntax;
compiled dictionaries and the actual caller proof still establish the operation contract. -/
partial def closedCallType (env : Env) : typ' → Bool
  | .BoolT | .TextT | .NumT .NatT | .NumT .IntT => true
  | .VarT name arguments => match env.types.get? name.it with
    | some info => info.tparams.length == arguments.length &&
      arguments.all (fun t => closedCallType env t.it)
    | none => false
  | .TupleT types => types.all (fun t => closedCallType env t.it)
  | .IterT element _ => closedCallType env element.it
  | _ => false

/-- Monomorphic call sites have explicit closed type arguments and exact actual callee arities. -/
partial def closedTypedCalls (env : Env) (d : Lang.Al.def) : Bool :=
  let monomorphic := match d.it with
    | .FuncDecD _ parameters .. => parameters.isEmpty
    | .RelD .. | .TableDecD .. => true
    | _ => false
  let rec supported (e : exp) : Bool :=
    let direct := match e.it with
      | .CallE name types arguments => match env.funcs.get? name.it with
        | some info => info.tparams.length == types.length &&
          types.all (fun t => closedCallType env t.it) &&
          info.params.length == arguments.length &&
          arguments.all (fun a => match a.it with | .ExpA _ => true | _ => false)
        | none => false
      | _ => true
    direct && (pairsOfExp.children e).all supported
  monomorphic && (expsOfDef d).all supported

/-- Scalar cast targets use named monomorphic constructors or the exact numeric boundary. -/
def scalarCastType (env : Env) : typ' → Bool
  | .NumT .NatT | .NumT .IntT => true
  | .VarT name [] => (env.types.get? name.it).any (fun info => info.tparams.isEmpty)
  | _ => false

/-- Check every nested scalar cast and subtype guard in the actual source expression. -/
partial def scalarTypeCheckExp (env : Env) (e : exp) : Bool :=
  let direct := match e.it with
    | .UpCastE target value =>
      match target.it, value.note with
      | .VarT .., .VarT .. => scalarCastType env target.it && scalarCastType env value.note
      | .NumT .IntT, .NumT .NatT => true
      | _, _ => false
    | .DownCastE target value =>
      match target.it, value.note with
      | .NumT .NatT, .NumT .IntT => true
      | .VarT .., .VarT .. => scalarCastType env target.it && scalarCastType env value.note
      | _, _ => false
    | .SubE _ target (.MixopSC _) => scalarCastType env target.it
    | .SubE _ target (.RecurseSC nested) =>
      typEq target.it (.NumT .NatT) && typEq nested.it (.NumT .NatT)
    | .SubE .. => false
    | _ => true
  direct && (pairsOfExp.children e).all (scalarTypeCheckExp env)

/-- Select the checked scalar subtype fragment from source syntax, without operation names.
Recursive checking is admitted only at the exact Nat boundary; named outer-notation checks
use the actual quoted mixfix descriptor. Other recursive guards remain excluded. -/
def scalarTypeChecks (env : Env) (d : Lang.Al.def) : Bool :=
  (expsOfDef d).all (scalarTypeCheckExp env)

/-- The first expression form outside the fragment, in `e`, if any. -/
partial def unsupportedExp (e : exp) (membership : Bool := false)
    (pairProjection : Bool := false) (typedCalls : Bool := false)
    (scalarChecks : Bool := false) (columnElements : Bool := false) : Option String :=
  let here : Option String := match e.it with
    | .UpCastE .. => if scalarChecks then none else some "upcast"
    | .DownCastE .. => if scalarChecks then none else some "downcast"
    | .SubE .. => if scalarChecks then none else some "subtype check"
    | .MemE .. => if membership then none else some "membership"
    | .IdxE .. => some "indexing"
    | .SliceE .. => some "slicing"
    | .UpdE _ p _ => if (dotPath p).isSome then none else some "path update with indexing"
    | .IterE .. => if (iterVar? e).isSome || columnElements ||
        (pairProjection && (pairIterationVars? e).isSome) then none
      else some "iterated expression"
    | .CallE _ targs _ => if targs.isEmpty || typedCalls then none
      else some "call with type arguments"
    | _ => none
  match here with
  | some r => some r
  | none => (pairsOfExp.children e).findSome? (fun e =>
      unsupportedExp e membership pairProjection typedCalls scalarChecks columnElements)

/-- A defined relation whose source arguments are all inputs has no output bindings. -/
def zeroOutputRelation (env : Env) (name : String) : Bool :=
  (env.rels.get? name).any fun info => !info.extern &&
    info.inputs.length == info.args.length &&
    (List.range info.args.length).all info.inputs.contains

private def listLengthVariable (e : exp) : Option String := do
  let .LenE value := e.it | none
  let (name, iterations) ← iterVar? value
  if iterations == [.List] then some name else none

private def equalListLengths (left right : String) (p : prem) : Bool :=
  match p.it with
  | .IfPr condition => match condition.it with
    | .CmpE .EqOp .BoolT a b =>
      (listLengthVariable a == some left && listLengthVariable b == some right) ||
        (listLengthVariable a == some right && listLengthVariable b == some left)
    | _ => false
  | _ => false

/-- Ordered list iteration currently composes only a defined zero-output relation call.
Two columns require their exact preceding length guard; binding outputs, nested and
optional iterations need separate driver support. -/
def relationIterationPrem (env : Env) (previous : List prem) (p : prem) : Bool :=
  match p.it with
  | .IterPr inner (.mk .List bound []) =>
    if bound.length != 1 && bound.length != 2 then false
    else if (bound.map (·.id.it)).eraseDups.length != bound.length then false
    else if bound.any (fun v => !v.iters.isEmpty) then false
    else match inner.it with
      | .IfHoldPr name pattern =>
        let arguments := Mixfix.args pattern
        let parameterInputs := arguments.length == bound.length &&
          (arguments.zip bound).all fun (e, v) =>
            match e.it with
            | .VarE name => name.it == v.id.it && typEq e.note v.typ.it
            | _ => false
        zeroOutputRelation env name.it && parameterInputs &&
          (env.rels.get? name.it).any (fun info => info.args.length == arguments.length) &&
          match bound with
          | [a, b] => previous.any (equalListLengths a.id.it b.id.it)
          | [_] => true
          | _ => false
      | _ => false
  | .IterPr .. => false
  | _ => true

/-- Select the complete zero-output relation/list-premise fragment from source syntax. -/
def relationListIteration (env : Env) (d : Lang.Al.def) : Bool :=
  match d.it with
  | .RelD name _ _ groups none _ =>
    let sequences := groups.flatMap fun group =>
      let (_, (_, _, common), paths) := group.it
      common :: paths.map (fun (_, premises, _) => common ++ premises)
    let hasIteration := sequences.any fun ps => ps.any fun p =>
      match p.it with | .IterPr .. => true | _ => false
    zeroOutputRelation env name.it && hasIteration && sequences.all (fun ps =>
      ps.zipIdx.all fun (p, index) => relationIterationPrem env (ps.take index) p)
  | _ => false

/-- The first premise form outside the fragment, in `p`, if any. -/
partial def unsupportedPrem (p : prem) (membership : Bool := false)
    (pairProjection : Bool := false) (typedCalls : Bool := false)
    (scalarChecks : Bool := false) (relationIteration : Bool := false) : Option String :=
  match p.it with
  | .IterPr .. => if relationIteration then
      (expsOfPrem p).findSome? (fun e =>
        unsupportedExp e membership pairProjection typedCalls scalarChecks)
    else some "iterated premise"
  | _ => (expsOfPrem p).findSome? (fun e =>
      unsupportedExp e membership pairProjection typedCalls scalarChecks)

/-- Detect actual callable recursion, including a source-derived mutual cycle. -/
def recursiveFunction (env : Env) (d : Lang.Al.def) : Bool :=
  match d.it with
  | .FuncDecD .. =>
    let edges := Std.HashMap.ofList
      ((env.defs.map fun definition => (definition.it.id.it, callsOfDef definition)) ++
        [(d.it.id.it, callsOfDef d)])
    (callsOfDef d).any (fun callee => (Graph.reachable edges callee).contains d.it.id.it)
  | _ => false

private def sameColumn (left right : Lang.Il.var) : Bool :=
  left.id.it == right.id.it && typEq left.typ.it right.typ.it &&
    left.iters.isEmpty && right.iters.isEmpty

private def columnVariable (e : exp) (v : Lang.Il.var) : Bool :=
  match e.it with
  | .VarE name => name.it == v.id.it && typEq e.note v.typ.it && v.iters.isEmpty
  | _ => false

private def distinctColumns (env : Env) (variables : List Lang.Il.var) : Bool :=
  (variables.map (·.id.it)).eraseDups.length == variables.length &&
    variables.all (fun v => v.iters.isEmpty && closedCallType env v.typ.it)

private def flatColumnCase (e : exp) (variables : List Lang.Il.var) : Bool :=
  match e.it with
  | .CaseE (.Seq parts) =>
    let arguments := Mixfix.args (.Seq parts)
    parts.all (fun part => match part with | .Atom _ | .Arg _ => true | _ => false) &&
      arguments.length == variables.length &&
      (arguments.filterMap fun arg => match arg.it with
        | .VarE name => some name.it | _ => none).eraseDups.length == variables.length &&
      arguments.all (fun arg => variables.any (columnVariable arg))
  | _ => false

/-- Select the checked extraction, element-call and reconstruction column pipeline.
The final two inputs must share the actual first-stage lineage; unrelated or overwritten
columns, nested/optional iterations and additional outputs stay excluded. -/
def columnPipeline (env : Env) (first second third : prem) : Bool := Id.run do
  let .IterPr extract (.mk .List [input] [left, right]) := first.it | return false
  let .LetPr pattern value := extract.it | return false
  if !distinctColumns env [input] || !distinctColumns env [left, right] ||
      !columnVariable value input || !typEq pattern.note input.typ.it ||
      !flatColumnCase pattern [left, right] then return false
  let .IterPr element (.mk .List [selected] [produced]) := second.it | return false
  let .LetPr output call := element.it | return false
  let .CallE callee [] [argument] := call.it | return false
  let .ExpA argument := argument.it | return false
  if !distinctColumns env [selected] || !distinctColumns env [produced] ||
      !columnVariable output produced || !columnVariable argument selected ||
      !typEq call.note produced.typ.it then return false
  let some info := env.funcs.get? callee.it | return false
  let [.ExpP parameter] := info.params | return false
  if info.kind != .defined || !info.tparams.isEmpty ||
      !typEq parameter.it selected.typ.it || !typEq info.ret produced.typ.it then return false
  let mate ← if sameColumn selected left then pure right
    else if sameColumn selected right then pure left else return false
  if [input, left, right].any (fun v => v.id.it == produced.id.it) then return false
  let .IterPr construct (.mk .List bound [result]) := third.it | return false
  let .LetPr output value := construct.it | return false
  if bound.length != 2 || !distinctColumns env bound || !distinctColumns env [result] ||
      !bound.all (fun v => sameColumn v mate || sameColumn v produced) ||
      bound.any (fun v => v.id.it == result.id.it) || !columnVariable output result ||
      !typEq value.note result.typ.it || !flatColumnCase value bound then return false
  return true

/-- The output-column driver currently composes a single self-recursive function.
A distinct callable returning to this definition would require the mutual column driver. -/
def singletonRecursiveFunction (env : Env) (d : Lang.Al.def) : Bool :=
  let name := d.it.id.it
  let calls := callsOfDef d
  let edges := Std.HashMap.ofList
    ((env.defs.map fun definition => (definition.it.id.it, callsOfDef definition)) ++
      [(name, calls)])
  recursiveFunction env d && calls.contains name &&
    !calls.any (fun callee => callee != name && (Graph.reachable edges callee).contains name)

/-- An expression and all its subexpressions, outermost first. -/
private partial def subExps (e : exp) : List exp :=
  e :: (pairsOfExp.children e).flatMap subExps

/-- An element-wise expression over extracted columns: a call of a defined monomorphic
function, or a comparison, on column variables, iterated over one or two zipped columns. -/
private def columnElementExp (env : Env) (columns : List String) (e : exp) : Bool :=
  let columnVar (a : exp) : Bool := match a.it with
    | .VarE name => columns.contains name.it
    | _ => false
  match e.it with
  | .IterE body (.mk .List vars) =>
    (vars.length == 1 || vars.length == 2) &&
      vars.all (fun v => columns.contains v.id.it && v.iters.isEmpty) &&
      match body.it with
      | .CallE callee [] arguments => (env.funcs.get? callee.it).any (fun info =>
          info.kind == .defined && info.tparams.isEmpty) &&
        arguments.all fun a => match a.it with | .ExpA a => columnVar a | _ => false
      | .CmpE _ _ a b => columnVar a && columnVar b
      | _ => false
  | _ => true

/-- Functions whose list premises only extract two columns from a list variable, and whose
other iterations are element-wise calls or comparisons over those columns (`bin_eq`).
A recursive call may occur only inside such an element-wise call (self-recursion). -/
def functionExtractionColumns (env : Env) (d : Lang.Al.def) : Bool :=
  match d.it with
  | .FuncDecD _ [] params _ clauses none _ =>
    let clauseSupported (clause : Lang.Il.clause) : Bool := Id.run do
      let (arguments, output, premises) := clause.it
      let mut columns : List String := []
      for p in premises do
        match p.it with
        | .IterPr extract (.mk .List [input] outputs) =>
          let .LetPr pattern value := extract.it | return false
          if outputs.length != 2 || !distinctColumns env [input] ||
              !distinctColumns env outputs || !columnVariable value input ||
              !typEq pattern.note input.typ.it || !flatColumnCase pattern outputs then
            return false
          columns := columns ++ outputs.map (·.id.it)
        | .IterPr .. => return false
        | _ => pure ()
      let iterated := (output :: premises.flatMap expsOfPrem).flatMap fun e =>
        (subExps e).filter fun e => match e.it with
          | .IterE _ _ => (iterVar? e).isNone
          | _ => false
      return arguments.length == params.length &&
        iterated.all (columnElementExp env columns)
    (recursiveFunction env d → singletonRecursiveFunction env d) &&
      params.all (fun p => match p.it with | .ExpP _ => true | _ => false) &&
      clauses.any (fun clause => let (_, _, ps) := clause.it
        ps.any fun p => match p.it with | .IterPr .. => true | _ => false) &&
      clauses.all clauseSupported
  | _ => false

/-- Singleton recursive monomorphic functions may use the checked list-column pipeline.
Every iterated clause has exactly one contiguous pipeline, and scalar clauses are retained.
Other list traversals need their own composition evidence before entering this fragment. -/
def functionListColumns (env : Env) (d : Lang.Al.def) : Bool :=
  match d.it with
  | .FuncDecD _ [] params _ clauses none _ =>
    let clauseSupported (clause : Lang.Il.clause) :=
      let (arguments, _, premises) := clause.it
      let indices := premises.zipIdx.filterMap fun (p, i) => match p.it with
        | .IterPr .. => some i | _ => none
      arguments.length == params.length && match indices with
      | [] => true
      | [a, b, c] => b == a + 1 && c == b + 1 &&
        match premises[a]?, premises[b]?, premises[c]? with
        | some first, some second, some third => columnPipeline env first second third
        | _, _, _ => false
      | _ => false
    singletonRecursiveFunction env d && params.length == 1 && requiresColumnsOf d &&
      params.all (fun p => match p.it with | .ExpP _ => true | _ => false) &&
      clauses.all clauseSupported
  | _ => false

/-- Find a source variable use recursively, independent of its printed generated name. -/
partial def usesVariable (name : String) (e : exp) : Bool :=
  (match e.it with | .VarE identifier => identifier.it == name | _ => false) ||
    (pairsOfExp.children e).any (usesVariable name)

/-- A checked downcast whose binding is unused needs separate constant-branch composition. -/
def unusedDowncastBinding (d : Lang.Al.def) : Bool :=
  let clauseUnsupported (clause : Lang.Il.clause) : Bool := Id.run do
    let (_, output, premises) := clause.it
    for (premise, index) in premises.zipIdx do
      match premise.it with
      | .LetPr binding value =>
        if let .VarE name := binding.it then
          if let .DownCastE .. := value.it then
            let later := [output] ++ ((premises.drop (index + 1)).flatMap expsOfPrem)
            if !later.any (usesVariable name.it) then return true
      | _ => pure ()
    return false
  match d.it with
  | .FuncDecD _ _ _ _ clauses alternative _ =>
    clauses.any clauseUnsupported || alternative.any clauseUnsupported
  | _ => false

/-- Why `d` is outside the fragment, if it is. -/
def unsupported (env : Env) (externs : List String) (d : Lang.Al.def)
    (certifiedBuiltins : List String := []) : Option String := Id.run do
  if env.mode == .freshState then return some "stateful refinement is not implemented"
  let membership := polymorphicMembership env d
  let pairProjection := polymorphicPairProjection env d
  let pureClauses := polymorphicPure env d
  let typedCalls := closedTypedCalls env d
  let scalarChecks := scalarTypeChecks env d
  let relationIteration := relationListIteration env d
  let columns := functionListColumns env d || functionExtractionColumns env d
  if recursiveFunction env d && !(registrationNames env d).isEmpty then
    return some "recursive function registration-freshness proof is not implemented"
  if unusedDowncastBinding d then
    return some "unused downcast binding composition is not implemented"
  if requiresTypeRulesOf d && (iterationRelationOf env d).isSome then
    return some "combined subtype and paired iteration proof is not implemented"
  let calls := callsOfDef d
  if calls.any externs.contains then return some "calls an extern"
  if calls.any fun c => match env.funcs.get? c with
      | some info => info.kind == .builtin && !certifiedBuiltins.contains c
      | none => false then return some "calls a builtin"
  if calls.any certifiedBuiltins.contains && !typedCalls then
    return some "builtin caller type or value arguments are unsupported"
  let prems : List prem := match d.it with
    | .RelD _ _ _ groups eg _ =>
      groups.flatMap (fun g =>
        let (_, (_, _, ps), paths) := g.it
        ps ++ paths.flatMap fun (_, ps, _) => ps) ++ (match eg with
        | some e => let (_, (_, _, ps), (_, ps', _)) := e.it; ps ++ ps'
        | none => [])
    | .FuncDecD _ _ _ _ clauses ec _ =>
      clauses.flatMap (fun c => let (_, _, ps) := c.it; ps) ++ (match ec with
        | some c => let (_, _, ps) := c.it; ps
        | none => [])
    | .TableDecD _ _ _ rows _ => rows.flatMap fun r => let (_, _, _, ps) := r.it; ps
    | _ => []
  match d.it with
  | .RelD _ _ _ _ (some _) _ => return some "else group"
  | .FuncDecD _ tparams params _ _ _ _ =>
    if !tparams.isEmpty && !(membership || pairProjection || pureClauses) then
      return some "type parameters"
    if params.any fun p => match p.it with | .DefP .. => true | _ => false then
      return some "function-typed parameter"
  | .TableDecD _ params .. =>
    if params.any fun p => match p.it with | .DefP .. => true | _ => false then
      return some "function-typed parameter"
  | .RelD .. => pure ()
  | _ => return some "not a definition with a body"
  if let some r := prems.findSome? (fun p =>
      unsupportedPrem p membership pairProjection typedCalls scalarChecks
        (relationIteration || columns)) then return some r
  -- the extraction predicate has already checked every iterated element expression
  let columnElements := functionExtractionColumns env d
  if let some r := (expsOfDef d).findSome? (fun e =>
      unsupportedExp e membership pairProjection typedCalls scalarChecks columnElements) then
    return some r
  none

/-! ## Statements -/

/-- The value relation of a member's results: `Rel` for a function, the
outputs against the tuple's values for a relation. -/
def resultRel (m : Member) : Format :=
  if !m.isRel then Format.text "Rel"
  else
    let vals := match m.nOuts with
      | 0 => []
      | 1 => [Format.text "toValue o"]
      | n => (projections n).map fun p => Format.text ("toValue o" ++ p)
    let binder := if m.nOuts == 0 then "(_ : Unit)" else "(o : " ++ (render m.ret.fmt) ++ ")"
    Format.paren (Format.group (Format.nest 2 (Format.text ("fun vs " ++ binder ++ " =>") ++
      Format.line ++ "Outs vs [" ++ Format.joinSep vals (Format.text ", ") ++ "]")))

/-- Raw AL type arguments in declaration order; their representation contracts are separate. -/
def typeArgumentNames (m : Member) : List String :=
  (List.range m.tparams.length).map fun i => s!"t{i}"

/-- Generated type dictionaries, including the actual source membership equality law. -/
def typeBinders (m : Member) : Format :=
  if m.tparams.isEmpty then Format.nil else
    Format.text
      ("{" ++ " ".intercalate (m.tparams.map Names.tparamName) ++ " : Type}") ++
    Format.join (m.tparams.map fun p =>
      let name := Names.tparamName p
      Format.line ++ Format.text s!"[ToValue {name}] [BEq {name}]" ++
        (if m.valueEquality then
          Format.line ++ Format.text s!"[Representation.ValueBEq {name}]" else Format.nil))

/-- Raw type arguments and global freshness required by actual parameter registration. -/
def typeArgumentBinders (m : Member) : Format :=
  let arguments := if m.tparams.isEmpty then Format.nil else
    Format.line ++ Format.text
      ("(" ++ " ".intercalate (typeArgumentNames m) ++ " : Lang.Il.typ)")
  arguments ++ Format.join ((m.typeFreshness.zip (List.range m.typeFreshness.length)).map
    fun (p, i) =>
    Format.line ++ Format.text s!"(ht{i} : ctx.global.tdtbl.get? {p.quote} = none)")

/-- The interpreter's invocation of the member on values `v0, v1, ...`. -/
def invocation (m : Member) : Format :=
  let vs := (List.range m.params.length).map fun i => s!"v{i}"
  let list := "[" ++ ", ".intercalate vs ++ "]"
  let head := if m.isRel then "Interp_al.Interp.invoke_rel" else "Interp_al.Interp.invoke_func"
  let targs := if m.isRel then Format.nil else
    Format.line ++ Format.text ("[" ++ ", ".intercalate (typeArgumentNames m) ++ "]")
  Format.paren (Format.group (Format.nest 2 (Format.text (head ++ " fuel cfg internal ctx") ++
    Format.line ++ Format.text s!"(Q.i {m.id.quote})" ++ targs ++ Format.line ++
    Format.text list)))

/-- The generated computation. -/
def generated (m : Member) : Format :=
  let ps := paramNames m.params.length
  let types := m.tparams.map fun p =>
    Term.atom ("(" ++ Names.tparamName p ++ " := " ++ Names.tparamName p ++ ")")
  Format.paren (Format.text "ExceptT.mk " ++ (Term.call m.defName (types ++ ps.map Term.atom)).arg)

/-- The `Refines` conclusion. -/
def conclusion (m : Member) : Format :=
  Format.group (Format.nest 2 (Format.text "Refines " ++ resultRel m ++ Format.line ++
    invocation m ++ Format.line ++ generated m))

/-- The pinned empty print-hint table, stated only when the callable closure reaches `print_`. -/
def printHintsBinder (m : Member) : Format :=
  if m.printHints then Format.text "(hhints : cfg.printHints = []) " else Format.nil

/-- The configuration hypothesis names passed on to a member statement, in binder order. -/
def configArguments (m : Member) : List String :=
  let functionEnv := if m.isRel && m.requiresTypeRules then "_hfenv" else "hfenv"
  ["cfg", "ctx", "internal", "hguard"] ++ (if m.printHints then ["hhints"] else []) ++
    [functionEnv, "hspec"]

/-- The binders after the fuel: the configuration, the context, the
values, the generated values and their relations. -/
def binders (lib : String) (m : Member) : Format :=
  let n := m.params.length
  let vs := (List.range n).map fun i => s!"v{i}"
  let ps := paramNames n
  let values := if n == 0 then Format.nil
    else Format.line ++ Format.text ("(" ++ " ".intercalate vs ++ " : Lang.Il.value)")
  let rels := Format.join ((List.range n).map fun i =>
    Format.line ++ Format.text s!"(h{i} : Rel v{i} {ps.getD i ""})")
  let functionEnv := if m.isRel && m.requiresTypeRules then "_hfenv" else "hfenv"
  typeBinders m ++ (if m.tparams.isEmpty then Format.nil else Format.line) ++
    Format.text "(cfg : Interp_al.Interp.Config) (ctx : Interp_al.Ctx.t) (internal : Bool)" ++
    Format.line ++ Format.text "(hguard : cfg.guard = false) " ++ printHintsBinder m ++
    Format.text s!"({functionEnv} : ctx.local.fenv = [])" ++
    Format.line ++ Format.text s!"(hspec : HoldsSpec {lib}.spec ctx.global)" ++
    typeArgumentBinders m ++ values ++ paramBinders m.params ++ rels

/-- All per-member refinement binders, including fuel, after a break point. -/
private def refinementBinders (lib : String) (m : Member) : Format :=
  Format.line ++ Format.text "(fuel : Nat)" ++ Format.line ++ binders lib m

/-- The closed type of an emitted per-member refinement theorem, including
fuel, invocation configuration, environment and related-input hypotheses. -/
def refinementType (lib : String) (m : Member) : Format :=
  Format.group (Format.nest 4 (Format.text "∀" ++ refinementBinders lib m ++ "," ++
    Format.line ++ conclusion m))

/-- The statement of a member inside a group theorem, for a fuel `fuel`. -/
def groupStatement (lib : String) (m : Member) : Format :=
  let n := m.params.length
  let vs := (List.range n).map fun i => s!"v{i}"
  let ps := paramNames n
  let values := if n == 0 then Format.nil
    else Format.text ("(" ++ " ".intercalate vs ++ " : Lang.Il.value)")
  let params := Format.join ((ps.zip m.params).map fun (p, t) =>
    Format.line ++ Format.text ("(" ++ p ++ " : ") ++ t.fmt ++ ")")
  let rels := Format.join ((List.range n).map fun i =>
    Format.line ++ Format.text s!"Rel v{i} {ps.getD i ""} →")
  Format.paren (Format.group (Format.nest 2 (
    Format.text "∀ (cfg : Interp_al.Interp.Config) (ctx : Interp_al.Ctx.t) (internal : Bool)," ++
    Format.line ++ Format.text s!"cfg.guard = false → " ++
    (if m.printHints then Format.text "cfg.printHints = [] → " else Format.nil) ++
    Format.text "ctx.local.fenv = [] →" ++
    Format.line ++ Format.text s!"HoldsSpec {lib}.spec ctx.global →" ++
    Format.join (m.typeFreshness.map fun name =>
      Format.line ++ Format.text s!"ctx.global.tdtbl.get? {name.quote} = none →") ++
    (if n == 0 then Format.nil else Format.line ++ Format.text "∀ " ++ values ++ params ++ ",") ++
    rels ++ Format.line ++ conclusion m)))

/-- The arguments a corollary passes on to the group statement, each
after a break point. -/
def corollaryArgs (m : Member) : Format :=
  let n := m.params.length
  let vs := (List.range n).map fun i => s!"v{i}"
  let hs := (List.range n).map fun i => s!"h{i}"
  let fresh := (List.range m.typeFreshness.length).map fun i => s!"ht{i}"
  Format.joinSep ((configArguments m ++ fresh ++ vs ++
    paramNames n ++ hs).map Format.text) Format.line

/-- The audit of a theorem's axioms. -/
def audit (name : String) : Format := Format.text ("#audit_axioms " ++ name)

/-- The forward driver invocation, with an explicit source-derived iteration relation. -/
def forwardProof (m : Member) : Format :=
  if m.requiresColumns then Format.text "refine_al (columns)" else
  match m.iterationRelation with
  | none => Format.text (if m.requiresTypeRules || m.requiresStructureRules
      then "refine_al (subtypes)" else "refine_al")
  | some relation => Format.group (Format.nest 2 (
      Format.text "refine_al (iteration :=" ++ Format.line ++ relation ++ ")"))

/-- The theorems of a group, or the reasons its members have none. -/
def groupTheorems (lib : String) (recursive : Bool) (members : List Member)
    (reasons : List (String × String)) : List Format := Id.run do
  if !reasons.isEmpty then
    -- one line per definition and reason, grouped by definition
    let ids := (reasons.map (·.1)).eraseDups
    return ids.map fun i =>
      let rs := (reasons.filter (·.1 == i)).map (·.2)
      Format.text s!"-- no refinement theorem: {i}" ++
        Format.nest 4 (Format.join (rs.map fun r => Format.text ("\n--   " ++ r)))
  if members.isEmpty then return []
  if !recursive then
    return members.flatMap fun m =>
      [Format.group (Format.nest 4 (Format.text ("theorem " ++ m.localName.replace ".run" "" ++
          ".refines") ++ refinementBinders lib m ++ " :" ++
          Format.line ++ conclusion m ++ " :=")) ++
        Format.nest 2 (Format.line ++ "by " ++ forwardProof m),
       audit (m.defName.replace ".run" "" ++ ".refines")]
  let first := members.head!
  let groupName := first.localName.replace ".run" "" ++ ".refines_group"
  let stmts := members.map (groupStatement lib)
  let proofs := if members.length == 1 then (forwardProof first).pretty 100
    else "exact ⟨" ++
      ", ".intercalate (members.map fun m => "by " ++ (forwardProof m).pretty 100) ++ "⟩"
  let groupThm := Format.group (Format.nest 4 (Format.text ("theorem " ++ groupName ++ " :") ++
      Format.line ++ Format.text "∀ (fuel : Nat)," ++
      Format.nest 2 (Format.line ++ Format.joinSep stmts (Format.text " ∧" ++ Format.line)) ++
      " := by")) ++
    Format.nest 2 (Format.line ++ Format.text "intro fuel" ++ Format.line ++
      Format.text "induction fuel using Nat.strongRecOn with" ++ Format.line ++
      Format.text s!"| ind fuel ih => {proofs}")
  let mut out := [groupThm, audit (lib ++ "." ++ groupName)]
  let n := members.length
  for (m, k) in members.zip (List.range n) do
    let proj := String.join ((List.range k).map fun _ => ".2") ++ (if k < n - 1 then ".1" else "")
    let name := m.localName.replace ".run" "" ++ ".refines"
    out := out ++ [Format.group (Format.nest 4 (Format.text ("theorem " ++ name) ++
        refinementBinders lib m ++ " :" ++
        Format.line ++ conclusion m ++ " :=")) ++
      Format.nest 2 (Format.line ++ Format.group (Format.nest 2 (
        Format.text s!"({lib}.{groupName} fuel){proj}" ++ Format.line ++ corollaryArgs m))),
      audit (m.defName.replace ".run" "" ++ ".refines")]
  out

end P4SpecTec.Codegen.Validate
