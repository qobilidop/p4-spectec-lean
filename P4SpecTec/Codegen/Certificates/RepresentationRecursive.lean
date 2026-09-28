import P4SpecTec.Codegen.Certificates.RepresentationField
import P4SpecTec.Codegen.Graph

/-!
Source-derived descriptors for recursive representation proof emission. These plans
bind a finite source-family closure to the actual generated decoder expressions and
encoder helpers. A plan alone is not a codec certificate: constructor composition
and complete source-derivation proofs must still be emitted and checked.
-/

namespace P4SpecTec.Codegen.RepresentationRecursive

open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Util.Source P4SpecTec.Codegen.Types
open RepresentationFields

/-- One closed source-family occurrence in a recursive certificate plan. -/
structure Family where
  /-- The actual source type; family identity ignores only source-region metadata. -/
  source : typ
  /-- The generated carrier after recursive-group alias unfolding. -/
  carrier : String
  /-- The actual field-context decoder expression, including inline specialization. -/
  decoder : String
  /-- The actual generated encoder function or container helper expression. -/
  encoder : String
  /-- Actual encoder equation names needed to expose this family's constructor. -/
  encoderUnfolding : List String := []
  /-- The source declaration for a locally expanded nominal family. -/
  declaration : Option Lang.Al.def
  /-- The source definition instantiated with the closed type arguments. -/
  body : Option deftyp'
  /-- A previously checked leaf contract; local recursive families never assume one. -/
  leaf : Option Contract
  /-- Positional child-family indices from the source body, preserving constructor order. -/
  children : List Nat
  /-- The actual named decoder consumes a fuel layer before its body. -/
  guarded : Bool
  /-- The generated carrier has an explicit runtime-only alternative. -/
  runtimeExtended : Bool

/-- A recursive group and the finite closed source forms its proof must handle. -/
structure Plan where
  /-- Actual source recursion-group names, in generator order. -/
  members : List String
  /-- The closed source families, with roots first and then source traversal order. -/
  families : Array Family
  /-- The root-family index for every actual named group member. -/
  roots : List (String × Nat)
  /-- Existing nominal codec dependencies used as independent proof leaves. -/
  dependencies : List String
  /-- Actual encoder helper names recovered using the compiler's helper planner. -/
  encoderHelpers : List String

/-- The generated raw-extern constructor of a runtime-extended carrier. -/
def runtimeExternValue (env : Env) (name : String) : String :=
  env.q (Names.typeName name) ++ "." ++ Representation.rawExternCtor

private def declaration (env : Env) (name : String) : Except String Lang.Al.def := do
  let declarations := env.defs.filter fun d => match d.it with
    | .TypD actual .. | .ExternTypD actual .. => actual.it == name
    | _ => false
  match declarations with
  | [d] => pure d
  | [] => throw s!"recursive source family has no type declaration: {name}"
  | _ => throw s!"recursive source family has ambiguous type declarations: {name}"

private def dependencies (env : Env) (name : String) : List String :=
  match env.types[name]? with
  | some info => match info.deftyp with
    | some body => (Env.deftypRefs body).eraseDups.filter fun dependency =>
      !info.tparams.contains dependency && env.types.contains dependency
    | none => []
  | none => []

/-- Find the actual source SCC, retaining self edges and respecting bound type parameters. -/
def groupOf (env : Env) (name : String) : Except String (List String) := do
  let names := env.defs.filterMap fun d => match d.it with
    | .TypD name .. | .ExternTypD name .. => some name.it
    | _ => none
  let some group := (Graph.sccs names (dependencies env)).find? (·.contains name)
    | throw s!"recursive source family is unknown: {name}"
  if !Graph.isRecursive group (dependencies env) then
    throw s!"source family is acyclic: {name}"
  pure group

private def fields : deftyp' → List typ
  | .PlainT t => [t]
  | .StructT fields => fields.map (·.2)
  | .VariantT cases => cases.flatMap fun c => Mixfix.args c.nottyp.it

private partial def validateCarrier (env : Env) (seen : List String) (t : typ') :
    Except String Unit := do
  match t with
  | .VarT name args =>
    if let some info := env.types[name.it]? then
      if !info.tparams.isEmpty && (groupOf env name.it).isOk then
        throw s!"recursive polymorphic carriers are not implemented: {name.it}"
    if env.isAlias name.it then
      if seen.contains name.it then throw s!"recursive source alias carrier cycle: {name.it}"
      let some (.PlainT body) := env.instantiate name.it (args.map (·.it))
        | throw s!"recursive source alias cannot be instantiated: {name.it}"
      validateCarrier env (name.it :: seen) body.it
    else
      for arg in args do validateCarrier env seen arg.it
  | .IterT element _ => validateCarrier env seen element.it
  | .TupleT _ => throw "recursive source tuple fields are not implemented"
  | .FuncT .. => throw "recursive source function fields are not implemented"
  | _ => pure ()

private def replayEncoders (env : Env) (group : List String) :
    Except String HelperState := do
  let some first := group.head? | throw "recursive source group is empty"
  let mut state : HelperState := { prefix_ := env.q (Names.typeName first) ++ "." }
  for name in group do
    let d ← declaration env name
    let .TypD _ [] definition _ := d.it
      | throw "recursive source codec currently needs monomorphic defined group members"
    for t in fields definition.it do
      validateCarrier env [] t.it
      let (_, next) := (Types.toValueTerm env group t.it (.atom "x")).run state
      state := next
  pure state

private def validateBody (name : String) (body : deftyp') : Except String Unit := do
  match body with
  | .VariantT cases =>
    if cases.isEmpty then throw s!"recursive source variant is empty: {name}"
    for c in cases do
      if (cases.filter fun other => Mixfix.eq_mixop c.nottyp.it other.nottyp.it).length != 1 then
        throw s!"recursive source constructors share a decoder mixop: {name}"
  | .StructT fields =>
    if (fields.map fun (a, _) => Names.fieldName a.it).eraseDups.length != fields.length then
      throw s!"recursive source record has duplicate generated fields: {name}"
    for (a, _) in fields do
      let .Keyword _ := a.it
        | throw s!"recursive source record has a non-keyword encoder label: {name}"
  | .PlainT _ => pure ()

private def instantiatedBody (env : Env) (name : String) (args : List typ) :
    Except String (Lang.Al.def × deftyp') := do
  let d ← declaration env name
  let .TypD _ parameters _definition _ := d.it
    | throw s!"opaque recursive source family needs an independent external domain: {name}"
  if parameters.length != args.length then throw s!"recursive source arity mismatch: {name}"
  if (parameters.map (·.it)).eraseDups.length != parameters.length then
    throw s!"recursive source parameters require distinct names: {name}"
  let some body := env.instantiate name (args.map (·.it))
    | throw s!"recursive source definition cannot be instantiated: {name}"
  validateBody name body
  pure (d, body)

private def familyIndex (families : Array Family) (t : typ) : Option Nat :=
  (families.findIdx? fun family => Types.typEq family.source.it t.it)

private def skeletalFamily (env : Env) (members : List String) (state : HelperState)
    (t : typ) : Except String Family := do
  validateCarrier env [] t.it
  let carrier := (Types.typTerm env [Types.unfoldAll] t.it).fmt.pretty
  let decoder := (Types.ofValueTerm env members t.it (.atom "v")).fmt.pretty
  let (encoder, encoderState) := (Types.toValueTerm env members t.it (.atom "x")).run state
  if encoderState.requested.length != state.requested.length then
    throw "recursive proof requested an encoder helper outside the actual generated group"
  let encoderUnfolding ← match t.it with
    | .VarT name [] =>
      if members.contains name.it then pure [env.q (toValueName name.it)] else pure []
    | _ =>
      if Types.mentions members t.it then
        let key := render (Types.typTerm env [] t.it).fmt
        let some (_, index, _) := state.requested.find? (·.1 == key)
          | throw "recursive encoder equation is absent from the actual helper planner"
        pure [s!"{state.prefix_}toValue_{index}"]
      else pure []
  let guarded := match t.it with
    | .VarT name _ => members.contains name.it || !Types.mentions members t.it
    | _ => false
  let runtimeExtended := match t.it with
    | .VarT name _ => env.representation.hasRawExtern name.it
    | _ => false
  pure { source := t, carrier, decoder := s!"fun fuel v => {decoder}"
         encoder := s!"fun x => {encoder.fmt.pretty}", encoderUnfolding
         declaration := none, body := none, leaf := none, children := [], guarded, runtimeExtended }

/-- Derive a closed recursive source descriptor from declarations and actual codegen plumbing.
Every nonrecursive proof leaf must already have an independently checked codec. -/
def derive (env : Env) (known : String → Option NominalContract) (name : String) :
    Except String Plan := do
  let members ← groupOf env name
  let encoderState ← replayEncoders env members
  let mut families := #[]
  let mut roots := []
  for name in members do
    let t := mkPhrase (.VarT (mkPhrase name) [])
    let family ← skeletalFamily env members encoderState t
    roots := roots ++ [(name, families.size)]
    families := families.push family
  let mut pending := 0
  let mut used := []
  while pending < families.size do
    let some family := families[pending]? | throw "recursive family queue invariant failed"
    let t := family.source
    let syntaxChildren := match t.it with
      | .VarT _ arguments => arguments
      | .IterT element _ => [element]
      | _ => []
    for child in syntaxChildren do
      if (familyIndex families child).isNone then
        families := families.push (← skeletalFamily env members encoderState child)
    let root := match t.it with | .VarT name _ => members.contains name.it | _ => false
    let leaf := if root || Types.mentions members t.it then none
      else (RepresentationFields.resolve env known t).toOption
    if let some contract := leaf then
      families := families.set! pending
        { family with
          leaf := some contract
          encoder := contract.encoder
          decoder := contract.decoder }
      used := used ++ contract.dependencies
    else
      let (declaration, body, children) ← match t.it with
        | .IterT element _ => pure (none, none, [element])
        | .VarT name args => do
          let (d, body) ← instantiatedBody env name.it args
          if !members.contains name.it && !Types.mentions members t.it then
            throw s!"recursive source dependency needs an existing codec: {name.it}"
          pure (some d, some body, fields body)
        | .TupleT _ => throw "recursive source tuple fields are not implemented"
        | .FuncT .. => throw "recursive source function fields are not implemented"
        | _ => throw "recursive source primitive codec is unavailable"
      let mut childIndices := []
      for child in children do
        let index ← match familyIndex families child with
          | some index => pure index
          | none => do
            let next ← skeletalFamily env members encoderState child
            let index := families.size
            families := families.push next
            pure index
        childIndices := childIndices ++ [index]
      families := families.set! pending
        { family with declaration, body, children := childIndices }
    pending := pending + 1
  pure { members, families, roots, dependencies := used.eraseDups
         encoderHelpers := encoderState.requested.map fun (_, index, _) =>
           s!"{encoderState.prefix_}toValue_{index}" }

private def indexOf (plan : Plan) (t : typ) : Except String Nat := do
  let some index := familyIndex plan.families t
    | throw "recursive source syntax is absent from its finite family closure"
  pure index

private def matchingConstructor (plan : Plan) (index : Nat) (t : typ) :
    Except String String := do
  let target := s!".f{index}"
  match t.it with
  | .BoolT => pure s!"  | f{index} : Matches .BoolT {target}"
  | .NumT kind =>
    let kind := if kind == .NatT then ".NatT" else ".IntT"
    pure s!"  | f{index} : Matches (.NumT {kind}) {target}"
  | .TextT => pure s!"  | f{index} : Matches .TextT {target}"
  | .VarT name arguments =>
    let names := (List.range arguments.length).map (fun i => s!"arg{i}")
    let types := if names.isEmpty then "" else " (" ++ " ".intercalate names ++ " : typ)"
    let children ← (arguments.zipIdx).mapM fun (arg, position) => do
      let family ← indexOf plan arg
      pure s!" (h{position} : Matches arg{position}.it .f{family})"
    pure (s!"  | f{index} (name : id){types} " ++
      s!"(nameEq : name.it = {(Reify.str name.it).fmt.pretty})" ++ String.join children ++
      s!" : Matches (.VarT name [{", ".intercalate names}]) {target}")
  | .IterT element kind =>
    let child ← indexOf plan element
    let kind := if kind == .List then ".List" else ".Opt"
    pure (s!"  | f{index} (element : typ) (matching : Matches element.it .f{child}) : " ++
      s!"Matches (.IterT element {kind}) {target}")
  | _ => throw "recursive syntax matcher does not support this source form"

private def matchingSubstitution (index : Nat) (t : typ) : Except String String := do
  match t.it with
  | .BoolT => pure s!"  | f{index} => rw [substitution.boolResult]; exact .f{index}"
  | .NumT _ => pure s!"  | f{index} => rw [substitution.numResult]; exact .f{index}"
  | .TextT => pure s!"  | f{index} => rw [substitution.textResult]; exact .f{index}"
  | .VarT _ [] => pure (s!"  | f{index} name nameEq =>\n" ++
      s!"    rw [substitution.emptyNamedResult name]; exact .f{index} name nameEq")
  | .VarT _ arguments =>
    let names := (List.range arguments.length).map (fun i => s!"arg{i}")
    let hypotheses := (List.range arguments.length).map (fun i => s!"h{i}")
    let inductions := (List.range arguments.length).map (fun i => s!"ih{i}")
    let mut proof := s!"  | f{index} name " ++ " ".intercalate names ++ " nameEq " ++
      " ".intercalate (hypotheses ++ inductions) ++ " =>\n" ++
      "    obtain ⟨args, rfl, arguments⟩ := substitution.namedArguments name [" ++
      ", ".intercalate names ++ "] rfl\n"
    let mut indent := "    "
    let mut tail := "arguments"
    for position in List.range arguments.length do
      proof := proof ++ indent ++ s!"cases {tail} with\n" ++ indent ++
        s!"| cons sub{position} rest{position} =>\n"
      indent := indent ++ "  "
      tail := s!"rest{position}"
    let children := (List.range arguments.length).map (fun i => s!"(ih{i} sub{i})")
    pure (proof ++ indent ++ s!"cases {tail}\n" ++ indent ++ s!"exact .f{index} name " ++
      " ".intercalate (List.replicate arguments.length "_") ++ " nameEq " ++
      " ".intercalate children)
  | .IterT _ kind =>
    let kind := if kind == .List then ".List" else ".Opt"
    pure (s!"  | f{index} element matching ih =>\n" ++
      s!"    obtain ⟨result, rfl, sub⟩ := substitution.iterResult element {kind}\n" ++
      s!"    exact .f{index} result (ih sub)")
  | _ => throw "recursive syntax substitution is not implemented"

private partial def matchingProof (plan : Plan) (t : typ) : Except String String := do
  let index ← indexOf plan t
  match t.it with
  | .BoolT | .NumT _ | .TextT => pure s!".f{index}"
  | .VarT name arguments =>
    let children ← arguments.mapM (matchingProof plan)
    let names := arguments.map (fun t => "(" ++ (Reify.typ t).fmt.pretty ++ ")")
    pure (s!".f{index} (Q.i {(Reify.str name.it).fmt.pretty}) " ++
      " ".intercalate names ++ " rfl " ++
      " ".intercalate (children.map (fun p => "(" ++ p ++ ")")))
  | .IterT element _ =>
    let child ← matchingProof plan element
    pure (s!".f{index} (" ++ (Reify.typ element).fmt.pretty ++ s!") ({child})")
  | _ => throw "recursive source matching proof does not support this source form"

/-- Emit the finite source-family dispatcher, exact contextual dictionaries and a
metadata-independent syntax matcher preserved by source empty substitution.
These checked helpers do not themselves establish any representation codec. -/
def familyDeclarations (plan : Plan) (namespaceName : String) : Except String Std.Format := do
  let families := plan.families.toList.zipIdx
  let constructors := families.map (fun (_, index) => s!"  | f{index}")
  let carriers := families.map (fun (family, index) => s!"  | .f{index} => {family.carrier}")
  let sources := families.map fun (family, index) =>
    s!"  | .f{index} => (" ++ (Reify.typ family.source).fmt.pretty ++ ").it"
  let sourceProofs ← families.mapM fun (family, index) => do
    pure (s!"  | f{index} => exact " ++ (← matchingProof plan family.source))
  let encoders := families.map (fun (family, index) => s!"  | .f{index} => {family.encoder}")
  let decoders := families.map (fun (family, index) => s!"  | .f{index} => {family.decoder}")
  let matchConstructors ← families.mapM fun (family, index) =>
    matchingConstructor plan index family.source
  let substitutions ← families.mapM fun (family, index) =>
    matchingSubstitution index family.source
  let text := s!"namespace {namespaceName}\n\n" ++
    "/-- Closed source families required by the actual recursive declaration group. -/\n" ++
    "inductive Family where\n" ++ "\n".intercalate constructors ++ "\n\n" ++
    "/-- Exact generated carriers, including their instantiated container forms. -/\n" ++
    "abbrev Carrier : Family → Type\n" ++ "\n".intercalate carriers ++ "\n\n" ++
    "/-- Exact encoders recovered from the actual compiler helper traversal. -/\n" ++
    "def encode : (family : Family) → Carrier family → value\n" ++
    "\n".intercalate encoders ++ "\n\n" ++
    "/-- Exact decoders in recursive field context; specialization retains its fuel policy. -/\n" ++
    "def decode : (family : Family) → Nat → value → Option (Carrier family)\n" ++
    "\n".intercalate decoders ++ "\n\n" ++
    "/-- Source syntax membership preserves all semantic names and ignores only metadata. -/\n" ++
    "inductive Matches : typ' → Family → Prop where\n" ++
    "\n".intercalate matchConstructors ++ "\n\n" ++
    "/-- Empty source substitution retains finite-family syntax membership. -/\n" ++
    "theorem Matches.emptySubstitution {input result : typ'} {family : Family}\n" ++
    "    (matching : Matches input family)\n" ++
    "    (substitution : Representation.Source.Substitutes [] input result) :\n" ++
    "    Matches result family := by\n" ++
    "  induction matching generalizing result with\n" ++
    "\n".intercalate substitutions ++ "\n\n" ++
    "#audit_axioms Matches.emptySubstitution\n\n" ++
    "/-- Actual closed source phrases indexed by the descriptor. -/\n" ++
    "def source : Family → typ'\n" ++ "\n".intercalate sources ++ "\n\n" ++
    "/-- Each actual descriptor phrase belongs to its finite source family. -/\n" ++
    "theorem sourceMatches (family : Family) : Matches (source family) family := by\n" ++
    "  cases family with\n" ++ "\n".intercalate sourceProofs ++ "\n\n" ++
    s!"#audit_axioms sourceMatches\n\nend {namespaceName}"
  pure (Std.Format.text (boundedLines text))

end P4SpecTec.Codegen.RepresentationRecursive
