import P4SpecTec.Codegen.Certificates.Builtin
import P4SpecTec.Codegen.Certificates.Representation

/-!
Full source input coverage and successful output preservation for actual builtin signatures.
Legal parameter codecs are explicit, and every composite dictionary is fixed at emission.
These contracts complement, rather than replace, the independently checked dispatch equations.
-/

namespace P4SpecTec.Codegen.SourceBuiltinCertificates
open P4SpecTec.Lang.Il P4SpecTec.Codegen.Types RepresentationFields

/-- A source field after substituting legal parameter instances. -/
structure Field extends Contract where
  /-- Exact instantiated source phrase, including the caller's parameter metadata. -/
  sourceType : String

/-- Independent grammar predicate of an instantiated field. -/
def Field.source (field : Field) (env : Env) : String :=
  s!"Representation.Source.Valid {env.lib}.spec Representation.Source.externDomain " ++
    s!"({field.sourceType}).it"

private def parenthesize (text : String) : String := "(" ++ text ++ ")"

private def namedKnown (env : Env) (name : String) : Option NominalContract := do
  let d ← env.defs.find? fun d => match d.it with
    | .TypD identifier .. => identifier.it == name | _ => false
  (← (RepresentationCertificates.plan env d).toOption).nominal

/-- Resolve arbitrary legal parameters and the source containers used by builtin signatures.
Closed leaves use the same checked nominal registry as ordinary source-entry certificates. -/
partial def field (env : Env) (parameters : List String) (type : typ) : Except String Field := do
  if let .VarT name [] := type.it then
    if let some index := parameters.idxOf? name.it then
      return {
        carrier := s!"α{index}"
        encoder := s!"@ToValue.toValue α{index} inferInstance"
        decoder := s!"@OfValue.ofValue α{index} inferInstance"
        admitted := s!"A{index}"
        codec := s!"c{index}"
        dependencies := []
        sourceType := s!"t{index}" }
  match type.it with
  | .IterT element kind =>
    let child ← field env parameters element
    let container := if kind == .List then "List" else "Option"
    let codec := if kind == .List then "listCodec" else "optionCodec"
    let carrier := s!"{container} ({child.carrier})"
    let kindText := if kind == .List then ".List" else ".Opt"
    return {
      carrier
      encoder := s!"@ToValue.toValue ({carrier}) " ++
        s!"(@P4SpecTec.Prelude.instToValue{container} ({child.carrier}) ⟨{child.encoder}⟩)"
      decoder := s!"@OfValue.ofValue ({carrier}) " ++
        s!"(@P4SpecTec.Prelude.instOfValue{container} ({child.carrier}) ⟨{child.decoder}⟩)"
      admitted := s!"fun xs : {carrier} => ∀ x ∈ xs, ({child.admitted}) x"
      codec := s!"@Representation.Source.{codec} {env.lib}.spec " ++
        "Representation.Source.externDomain " ++
        s!"({child.carrier}) ⟨{child.encoder}⟩ ⟨{child.decoder}⟩ " ++
        s!"({child.sourceType}) ({child.admitted}) ({child.codec})"
      dependencies := child.dependencies
      sourceType := s!"Q.t (.IterT ({child.sourceType}) {kindText})" }
  | .VarT name arguments =>
    if arguments.isEmpty then
      let contract ← resolve env (namedKnown env) type
      return { contract with sourceType := (Reify.typ type).fmt.pretty }
    let some declaration := env.defs.find? (fun d => match d.it with
      | .TypD identifier .. => identifier.it == name.it | _ => false)
      | throw "unknown parameterized source domain"
    let arity ← if (RepresentationContainers.pairShape env declaration).isOk then pure 2
      else if (RepresentationContainers.listShape env declaration).isOk then pure 1
      else if (RepresentationMaps.checkSupport env declaration).isOk then pure 2
      else throw "unsupported parameterized source codec"
    unless arity == arguments.length do throw "source codec type arity differs"
    let children ← arguments.mapM (field env parameters)
    let q := env.q (Names.typeName name.it)
    let carriers := children.map (parenthesize ·.carrier)
    let predicates := children.map (parenthesize ·.admitted)
    let encoders := children.map (fun c => "⟨" ++ c.encoder ++ "⟩")
    let decoders := children.map (fun c => "⟨" ++ c.decoder ++ "⟩")
    let instances := children.flatMap (fun c => ["⟨" ++ c.encoder ++ "⟩", "⟨" ++ c.decoder ++ "⟩"])
    let sourceTypes := children.map (parenthesize ·.sourceType)
    let admitted ← match RepresentationMaps.checkSupport env declaration with
      | .ok (_, _, outer, inner) => pure (
          "@" ++ env.q (Names.typeName outer.it) ++ ".admitted (" ++
          env.q (Names.typeName inner.it) ++ " " ++ " ".intercalate carriers ++ ") (" ++
          "@" ++ env.q (Names.typeName inner.it) ++ ".admitted " ++
          " ".intercalate (carriers ++ predicates) ++ ")")
      | .error _ => pure ("@" ++ q ++ ".admitted " ++ " ".intercalate (carriers ++ predicates))
    return {
      carrier := q ++ " " ++ " ".intercalate carriers
      encoder := "@" ++ q ++ ".toValue " ++ " ".intercalate (carriers ++ encoders)
      decoder := "@" ++ q ++ ".ofValue " ++ " ".intercalate (carriers ++ decoders)
      admitted
      codec := "@" ++ q ++ ".codec " ++ " ".intercalate
        (carriers ++ instances ++ sourceTypes ++ predicates ++ children.map (parenthesize ·.codec))
      dependencies := (name.it :: children.flatMap (·.dependencies)).eraseDups
      sourceType := "Q.t (Q.varT " ++ name.it.quote ++ " [" ++
        ", ".intercalate sourceTypes ++ "])" }
  | .TupleT [leftType, rightType] =>
    let left ← field env parameters leftType
    let right ← field env parameters rightType
    let carrier := s!"({left.carrier}) × ({right.carrier})"
    return {
      carrier
      encoder := s!"@Representation.Source.pairEncoder ({left.carrier}) ({right.carrier}) " ++
        s!"⟨{left.encoder}⟩ ⟨{right.encoder}⟩"
      decoder := s!"@Representation.Source.pairDecoder ({left.carrier}) ({right.carrier}) " ++
        s!"⟨{left.decoder}⟩ ⟨{right.decoder}⟩"
      admitted := s!"fun p : {carrier} => ({left.admitted}) p.1 ∧ ({right.admitted}) p.2"
      codec := s!"@Representation.Source.pairCodec {env.lib}.spec " ++
        s!"Representation.Source.externDomain ({left.carrier}) ({right.carrier}) " ++
        s!"⟨{left.encoder}⟩ ⟨{left.decoder}⟩ ⟨{right.encoder}⟩ ⟨{right.decoder}⟩ " ++
        s!"({left.sourceType}) ({right.sourceType}) ({left.admitted}) ({right.admitted}) " ++
        s!"({left.codec}) ({right.codec})"
      dependencies := (left.dependencies ++ right.dependencies).eraseDups
      sourceType := s!"Q.t (.TupleT [({left.sourceType}), ({right.sourceType})])" }
  | .TupleT _ => throw "source tuple domain requires exactly two fields"
  | _ =>
    let contract ← resolve env (namedKnown env) type
    return { contract with sourceType := (Reify.typ type).fmt.pretty }

/-- Actual input and result contracts, after signature and source carrier validation. -/
def fields (env : Env) (d : Lang.Al.def) : Except String (List String × List Field × Field) := do
  BuiltinCertificates.checkSupport env d
  let .BuiltinDecD _ parameters inputs result _ := d.it | throw "not a builtin"
  let parameters := parameters.map (·.it)
  let inputs ← inputs.mapM fun p => match p.it with
    | .ExpP t => field env parameters t
    | _ => throw "source builtin callback is unsupported"
  return (parameters, inputs, ← field env parameters result)

private def parameterBinders (env : Env) (parameters : List String) : String :=
  String.join ((List.range parameters.length).map fun i =>
    " {" ++ s!"α{i} : Type" ++ "} " ++ s!"[ToValue α{i}] [OfValue α{i}] [BEq α{i}] " ++
    s!"(t{i} : Lang.Il.typ) (A{i} : α{i} → Prop) " ++
    s!"(c{i} : Representation.Codec (Representation.Source.Valid {env.lib}.spec " ++
    s!"Representation.Source.externDomain t{i}.it) A{i})")

private def coverageType (env : Env) (inputs : List Field) : String :=
  "∀ " ++ String.join (inputs.zipIdx.map fun (f, i) =>
    s!"(v{i} : Lang.Il.value) (hv{i} : ({f.source env}) v{i}) ") ++ ", " ++
  String.join (inputs.zipIdx.map fun (f, i) => s!"∃ p{i} : {f.carrier}, ") ++
  " ∧ ".intercalate (inputs.zipIdx.flatMap fun (f, i) =>
    [s!"({f.admitted}) p{i}", s!"@Rel ({f.carrier}) ⟨{f.encoder}⟩ v{i} p{i}"])

private def outputType (env : Env) (d : Lang.Al.def) (inputs : List Field)
    (output : Field) : String :=
  "∀ " ++ String.join (inputs.zipIdx.map fun (f, i) =>
    s!"(p{i} : {f.carrier}) (hp{i} : ({f.admitted}) p{i}) ") ++
  s!"(result : {output.carrier}), " ++ env.q (Names.funcName d.it.id.it) ++ " " ++
  " ".intercalate (inputs.zipIdx.map fun (_, i) => s!"p{i}") ++
  s!" = some (.ok result) → ({output.source env}) (({output.encoder}) result)"

/-- Close source coverage and output obligations over their explicit legal parameter codecs. -/
def domainType (env : Env) (d : Lang.Al.def) (parameters : List String)
    (inputs : List Field) (output : Field) : String :=
  let binders := parameterBinders env parameters
  let body := "(" ++ coverageType env inputs ++ ") ∧ (" ++ outputType env d inputs output ++ ")"
  if parameters.isEmpty then body else "∀ " ++ binders ++ ", " ++ body

/-- Exact full-domain statement: source input coverage and all admitted-input successful outputs. -/
def theoremType (env : Env) (d : Lang.Al.def) : Except String String := do
  let (parameters, inputs, output) ← fields env d
  return domainType env d parameters inputs output

/-- Nominal source codecs used in the exact signature, including the result codec. -/
def dependencies (env : Env) (d : Lang.Al.def) : Except String (List String) := do
  let (_, inputs, output) ← fields env d
  return ((inputs ++ [output]).flatMap (·.dependencies)).eraseDups

/-- Operation proof support; named source sidecar dependencies are reported separately. -/
def supportImports : List String :=
  ["P4SpecTec.Refine.SourceBuiltin", "P4SpecTec.Refine.ProducerMap",
    "P4SpecTec.Refine.Representation.SourceTuple", "P4SpecTec.Tactic.Audit"]

private def coverageProof (env : Env) (inputs : List Field) : String := Id.run do
  let mut proof := "intro " ++ " ".intercalate
    (inputs.zipIdx.flatMap fun (_, i) => [s!"v{i}", s!"hv{i}"]) ++ "\n"
  for (f, i) in inputs.zipIdx do
    proof := proof ++ s!"obtain ⟨p{i}, hp{i}, hr{i}⟩ :=\n" ++
      s!"  (@Representation.Codec.adequate ({f.carrier}) ⟨{f.encoder}⟩ ⟨{f.decoder}⟩ " ++
      s!"({f.source env}) ({f.admitted}) ({f.codec})).coverage v{i} hv{i}\n"
  return proof ++ "exact ⟨" ++ ", ".intercalate
    ((inputs.zipIdx.map fun (_, i) => s!"p{i}") ++
      inputs.zipIdx.flatMap (fun (_, i) => [s!"hp{i}", s!"hr{i}"])) ++ "⟩"

private def identifyOutput (env : Env) (d : Lang.Al.def) : String :=
  "simp only [" ++ env.q (Names.funcName d.it.id.it) ++
    ", ExceptT.run, pure, ExceptT.pure] at run\ncases Except.ok.inj (Option.some.inj run)\n"

private def outputProof (env : Env) (d : Lang.Al.def) (inputs : List Field)
    (output : Field) : Except String String := do
  let introLine := "intro " ++ " ".intercalate
    (inputs.zipIdx.flatMap fun (_, i) => [s!"p{i}", s!"hp{i}"]) ++ " result run\n"
  let encoding := "apply " ++ output.toContract.encodingProof (output.source env) output.codec ++
    " result\n"
  let id := d.it.id.it
  let some signature := BuiltinCertificates.signature id | throw "unsupported builtin"
  if ["text", "bool", "int", "nat"].contains signature.output then
    return introLine ++ encoding ++ "trivial"
  if signature.output == "bits" then
    return introLine ++ encoding ++ "exact " ++ env.q "bits.admittedAll" ++ " result"
  match id with
  | "rev_" => return introLine ++ encoding ++ identifyOutput env d ++
      "exact SourceBuiltin.reversePreserves A0 p0 hp0"
  | "intersect_set" | "union_set" | "diff_set" =>
    let op := if id == "intersect_set" then "intersectPreserves" else
      if id == "union_set" then "unionPreserves" else "diffPreserves"
    return introLine ++ encoding ++ "rcases p0 with ⟨xs⟩\nrcases p1 with ⟨ys⟩\n" ++
      identifyOutput env d ++ s!"exact SourceBuiltin.{op} A0 xs ys hp0" ++
      (if id == "union_set" then " hp1" else "")
  | "unions_set" => return introLine ++ encoding ++ identifyOutput env d ++
      "apply SourceBuiltin.unionsPreserves\nintro xs member\n" ++
      "obtain ⟨entry, originalMember, rfl⟩ := List.mem_map.mp member\n" ++
      "cases entry with | lbrace_rbrace xs => exact hp0 _ originalMember"
  | "find_map" => return introLine ++ encoding ++ "rcases p0 with ⟨xs⟩\n" ++
      identifyOutput env d ++ "intro value found\n" ++
      "apply SourceBuiltin.findPreserves A1 p1 _ ?_ value " ++
      "found\nintro entry member\n" ++
      "obtain ⟨entry, originalMember, rfl⟩ := List.mem_map.mp member\n" ++
      "cases entry with | colon k v => exact (hp0 _ originalMember).2"
  | "find_maps" => return introLine ++ encoding ++ identifyOutput env d ++
      "intro value found\napply SourceBuiltin.findMapsPreserves A1 p1 _ ?_ value " ++
      "found\nintro entries outer entry inner\n" ++
      "obtain ⟨m, originalOuter, rfl⟩ := List.mem_map.mp outer\n" ++
      "cases m with | lbrace_rbrace xs =>\n" ++
      "  obtain ⟨entry, originalInner, rfl⟩ := List.mem_map.mp inner\n" ++
      "  cases entry with | colon k v => exact (hp0 _ originalOuter _ originalInner).2"
  | "add_map" | "update_map" => return introLine ++ encoding ++
      "rcases p0 with ⟨xs⟩\n" ++ identifyOutput env d ++
      "intro entry member\nobtain ⟨⟨k, v⟩, pairMember, rfl⟩ := List.mem_map.mp member\n" ++
      "have accepted := ProducerMap.update (fun p : α0 × α1 => A0 p.1 ∧ A1 p.2) " ++
      "_ p1 p2 ?_ ⟨hp1, hp2⟩ (k, v) pairMember\n" ++
      "· exact accepted\n· intro entry member\n" ++
      "  obtain ⟨entry, originalMember, rfl⟩ := List.mem_map.mp member\n" ++
      "  cases entry with | colon k v => exact hp0 _ originalMember"
  | "assoc_" => return introLine ++ encoding ++ identifyOutput env d ++
      "intro value found\nexact SourceBuiltin.assocPreserves A1 p0 p1 " ++
      "(fun pair member => (hp1 pair member).2) value found"
  | _ => throw s!"no successful-output proof for builtin {id}"

/-- Emit the common source-domain proof shell around an independently checked producer proof. -/
def domainDeclaration (env : Env) (d : Lang.Al.def) (parameters : List String)
    (inputs : List Field) (output : Field) (producerProof : String) : String := Id.run do
  let statement := domainType env d parameters inputs output
  let proof := "constructor\n· " ++ (coverageProof env inputs).replace "\n" "\n  " ++
    "\n· " ++ producerProof.replace "\n" "\n  "
  let introLine := if parameters.isEmpty then "" else "intro " ++ " ".intercalate
    ((List.range parameters.length).flatMap fun i =>
      [s!"α{i}", s!"_tv{i}", s!"_ov{i}", s!"_eq{i}", s!"t{i}", s!"A{i}", s!"c{i}"]) ++ "\n"
  let name := Names.funcName d.it.id.it ++ ".sourceDomain"
  return boundedLines (
    "/-- Full source coverage and source validity of admitted successful outputs. -/\n" ++
    s!"theorem {name} : {statement} := by\n  " ++
    (introLine ++ proof).replace "\n" "\n  " ++ s!"\n\n#audit_axioms {name}\n")

/-- Emit source coverage and independently valid successful outputs for a checked builtin. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String String := do
  let (parameters, inputs, output) ← fields env d
  return domainDeclaration env d parameters inputs output (← outputProof env d inputs output)

end P4SpecTec.Codegen.SourceBuiltinCertificates
