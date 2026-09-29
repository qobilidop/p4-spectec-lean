import P4SpecTec.Codegen.Certificates.RepresentationMap
import P4SpecTec.Codegen.Reify
import P4SpecTec.Codegen.Types

/-!
Field contracts used by source representation certificate emitters. Every contract
fixes the exact source phrase and generated encoder/decoder dictionaries. Named
dependencies are supplied by the certificate plan, never inferred from decoder success.
-/

namespace P4SpecTec.Codegen.RepresentationFields

open P4SpecTec.Lang.Il P4SpecTec.Codegen.Types

/-- A previously checked nominal codec and its independently stated input admission. -/
structure NominalContract where
  /-- A term proving the codec on the complete named `Source.Valid` domain. -/
  codec : String
  /-- The admitted generated inputs, including any explicit source/runtime restriction. -/
  admitted : String

/-- Exact dictionaries and source obligations for one generated field occurrence. -/
structure Contract where
  /-- The generated Lean carrier. -/
  carrier : String
  /-- The exact field encoder. -/
  encoder : String
  /-- The exact field decoder, with its fuel argument still present. -/
  decoder : String
  /-- The independently stated generated input admission predicate. -/
  admitted : String
  /-- A proof of the codec over the actual quoted source type. -/
  codec : String
  /-- Nominal codec dependencies needed by the enclosing certificate. -/
  dependencies : List String

/-- The independent source predicate for a field in the actual compiled specification. -/
def source (env : Env) (t : typ) : String :=
  "Representation.Source.Valid " ++ env.lib ++ ".spec " ++ env.domainTerm ++ " " ++
    "(" ++ (Reify.typ t).fmt.pretty ++ ").it"

/-- A codec type with fully explicit dictionaries, avoiding reducible alias capture. -/
def Contract.type (contract : Contract) (source : String) : String :=
  s!"@Representation.Codec ({contract.carrier}) ⟨{contract.encoder}⟩ " ++
    s!"⟨{contract.decoder}⟩ ({source}) ({contract.admitted})"

/-- Project encoding validity with the field's exact dictionaries still fixed. -/
def Contract.encodingProof (contract : Contract) (source proof : String) : String :=
  s!"@Representation.Codec.encodingValid ({contract.carrier}) ⟨{contract.encoder}⟩ " ++
    s!"⟨{contract.decoder}⟩ ({source}) ({contract.admitted}) ({proof})"

private def Contract.decoderProof (contract : Contract) (source proof : String) : String :=
  s!"@Representation.Codec.decoder ({contract.carrier}) ⟨{contract.encoder}⟩ " ++
    s!"⟨{contract.decoder}⟩ ({source}) ({contract.admitted}) ({proof})"

/-- Project faithful actual decoding without synthesizing a later reducible alias instance. -/
def Contract.soundProof (contract : Contract) (source proof : String) : String :=
  s!"@Representation.DecoderCorrect.sound ({contract.carrier}) ⟨{contract.encoder}⟩ " ++
    s!"({source}) ({contract.admitted}) ({contract.decoder}) " ++
    s!"({contract.decoderProof source proof})"

/-- Project stable sufficient decoding with exact named encoder and decoder dictionaries. -/
def Contract.sufficientProof (contract : Contract) (source proof : String) : String :=
  s!"@Representation.DecoderCorrect.sufficient ({contract.carrier}) ⟨{contract.encoder}⟩ " ++
    s!"({source}) ({contract.admitted}) ({contract.decoder}) " ++
    s!"({contract.decoderProof source proof})"

private def primitive (env : Env) (kind carrier instanceName : String) : Contract :=
  { carrier
    encoder := s!"@ToValue.toValue {carrier} P4SpecTec.Prelude.instToValue{instanceName}"
    decoder := s!"@OfValue.ofValue {carrier} P4SpecTec.Prelude.instOfValue{instanceName}"
    admitted := s!"fun _ : {carrier} => True"
    codec := s!"@Representation.Source.{kind}Codec {env.lib}.spec " ++ env.domainTerm
    dependencies := [] }

private def scalarSubstitutionResult (t : typ) (proof : String) : Except String String :=
  match t.it with
  | .BoolT => pure (proof ++ ".boolResult")
  | .NumT _ => pure (proof ++ ".numResult")
  | .TextT => pure (proof ++ ".textResult")
  | .VarT name [] => pure (proof ++ ".emptyNamedResult (Q.i " ++
      (Reify.str name.it).fmt.pretty ++ ")")
  | _ => throw "nested type-argument substitution needs a structural domain transport"

private partial def substitutionBody (t : typ) : Except String String := do
  match t.it with
  | .BoolT => pure "simpa only [substitution.boolResult] using valid"
  | .NumT _ => pure "simpa only [substitution.numResult] using valid"
  | .TextT => pure "simpa only [substitution.textResult] using valid"
  | .VarT name [] =>
    pure ("rw [substitution.emptyNamedResult (Q.i " ++ (Reify.str name.it).fmt.pretty ++
      ")] at valid\nexact valid")
  | .IterT element kind =>
    let child ← substitutionBody element
    let kind := if kind == .List then ".List" else ".Opt"
    pure ("obtain ⟨element, shape, substitution⟩ := substitution.iterResult " ++
      "(" ++ (Reify.typ element).fmt.pretty ++ ") " ++ kind ++ "\n" ++
      "rw [shape] at valid\n" ++
      "apply Representation.Source.Valid.iterDomain ?_ valid\n" ++
      "intro v valid\n" ++ child)
  | .VarT name arguments =>
    let results ← (arguments.zipIdx).mapM (fun (arg, index) =>
      scalarSubstitutionResult arg s!"substitution{index}")
    let mut proof := "obtain ⟨arguments, shape, substitutions⟩ := " ++
      "substitution.namedArguments (Q.i " ++ (Reify.str name.it).fmt.pretty ++ ") " ++
      (Reify.lst (arguments.map Reify.typ)).arg.pretty ++ " rfl\n" ++
      "rw [shape] at valid\n"
    let mut indent := ""
    let mut tail := "substitutions"
    for index in List.range arguments.length do
      proof := proof ++ indent ++ "cases " ++ tail ++ " with\n" ++ indent ++
        s!"| cons substitution{index} rest{index} =>\n"
      indent := indent ++ "  "
      tail := s!"rest{index}"
    proof := proof ++ indent ++ "cases " ++ tail ++ "\n" ++ indent ++
      "apply valid.arguments\n" ++ indent ++
      "simp only [List.map_cons, List.map_nil, " ++ ", ".intercalate results ++ "]"
    pure proof
  | .TupleT _ => throw "source tuple substitution transport is not implemented"
  | .FuncT .. => throw "source function substitution transport is not implemented"

/-- Emit domain transport for empty substitution without equating source-region metadata.
The proof takes an instantiated type, its substitution derivation and a valid payload. -/
def normalizeSubstitution (t : typ) : Except String String := do
  let body ← substitutionBody t
  pure ("(by\n  intro actual substitution v valid\n  " ++
    body.replace "\n" "\n  " ++ ")")

/-- A finite empty-substitution derivation for the supported closed field fragment. -/
partial def identitySubstitution (t : typ) : Except String String := do
  match t.it with
  | .BoolT => pure "Representation.Source.Substitutes.bool"
  | .NumT .NatT => pure "Representation.Source.Substitutes.num .NatT"
  | .NumT .IntT => pure "Representation.Source.Substitutes.num .IntT"
  | .TextT => pure "Representation.Source.Substitutes.text"
  | .VarT name arguments => do
    let children ← arguments.mapM identitySubstitution
    let payload := children.foldr (fun child tail => ".cons (" ++ child ++ ") (" ++ tail ++ ")")
      ".nil"
    let args := (Reify.lst (arguments.map Reify.typ)).arg.pretty
    pure ("Representation.Source.Substitutes.named (Q.i " ++
      (Reify.str name.it).fmt.pretty ++ ") " ++ args ++ " " ++ args ++ " rfl (" ++ payload ++ ")")
  | .IterT element kind =>
    let child ← identitySubstitution element
    let element := "(" ++ (Reify.typ element).fmt.pretty ++ ")"
    let kind := if kind == .List then ".List" else ".Opt"
    pure s!"Representation.Source.Substitutes.iter {element} {element} {kind} ({child})"
  | _ => throw "source field identity substitution is not implemented"

/-- Resolve primitive, closed nominal and nested list/option field occurrences.
The caller supplies checked named codecs; open parameters and unproved dependencies fail. -/
partial def resolve (env : Env) (known : String → Option NominalContract) (t : typ) :
    Except String Contract := do
  match t.it with
  | .BoolT => pure (primitive env "bool" "Bool" "Bool")
  | .NumT .NatT => pure (primitive env "nat" "Nat" "Nat")
  | .NumT .IntT => pure (primitive env "int" "Int" "Int")
  | .TextT => pure (primitive env "text" "ByteText" "ByteText")
  | .VarT name [] =>
    let some info := env.types[name.it]? | throw s!"unknown source field {name.it}"
    if !info.tparams.isEmpty then throw s!"open source field parameters in {name.it}"
    if info.deftyp.isNone then
      unless env.defs.any (fun d => match d.it with
          | .ExternTypD identifier .. => identifier.it == name.it
          | _ => false) do throw s!"source field {name.it} has no external declaration"
      return { carrier := env.q (Names.typeName name.it)
               encoder := "@ToValue.toValue ExternValue P4SpecTec.Prelude.instToValueExternValue"
               decoder := "@OfValue.ofValue ExternValue P4SpecTec.Prelude.instOfValueExternValue"
               admitted := "fun _ : ExternValue => True"
               codec := env.liftRuntime (env.q (Names.typeName name.it))
                 "@ToValue.toValue ExternValue P4SpecTec.Prelude.instToValueExternValue"
                 "@OfValue.ofValue ExternValue P4SpecTec.Prelude.instOfValueExternValue"
                 (s!"@Representation.Source.externalCodec {env.lib}.spec " ++
                   "(Q.i " ++ (Reify.str name.it).fmt.pretty ++ ") (by rfl)")
               dependencies := [] }
    let some contract := known name.it | throw s!"unproved source field codec {name.it}"
    let qualified := env.q (Names.typeName name.it)
    pure { carrier := qualified
           encoder := qualified ++ ".toValue"
           decoder := qualified ++ ".ofValue"
           admitted := contract.admitted
           codec := contract.codec
           dependencies := [name.it] }
  | .IterT element kind =>
    let child ← resolve env known element
    let container := if kind == .List then "List" else "Option"
    let codec := if kind == .List then "listCodec" else "optionCodec"
    let instanceName := if kind == .List then "List" else "Option"
    let carrier := s!"{container} ({child.carrier})"
    let encoder := s!"@ToValue.toValue ({carrier}) " ++
      s!"(@P4SpecTec.Prelude.instToValue{instanceName} ({child.carrier}) ⟨{child.encoder}⟩)"
    let decoder := s!"@OfValue.ofValue ({carrier}) " ++
      s!"(@P4SpecTec.Prelude.instOfValue{instanceName} ({child.carrier}) ⟨{child.decoder}⟩)"
    pure { carrier, encoder, decoder
           admitted := s!"fun xs : {carrier} => ∀ x ∈ xs, ({child.admitted}) x"
           codec := s!"@Representation.Source.{codec} {env.lib}.spec " ++
             env.domainTerm ++ " " ++
             s!"({child.carrier}) ⟨{child.encoder}⟩ ⟨{child.decoder}⟩ " ++
             s!"({(Reify.typ element).fmt.pretty}) ({child.admitted}) ({child.codec})"
           dependencies := child.dependencies }
  | .VarT name arguments =>
    let some declaration := env.defs.find? (fun d => match d.it with
      | .TypD typeName .. => typeName.it == name.it
      | _ => false) | throw s!"unknown parameterized source field {name.it}"
    let arity ← if (RepresentationContainers.pairShape env declaration).isOk then pure 2
      else if (RepresentationContainers.listShape env declaration).isOk then pure 1
      else if (RepresentationMaps.checkSupport env declaration).isOk then pure 2
      else throw s!"source field {name.it} needs a supported complete parameterized codec"
    if arguments.length != arity then throw s!"source field {name.it} has wrong type arity"
    let children ← arguments.mapM (resolve env known)
    let qualified := env.q (Names.typeName name.it)
    let carriers := children.map (fun c => "(" ++ c.carrier ++ ")")
    let encoders := children.map (fun c => "⟨" ++ c.encoder ++ "⟩")
    let decoders := children.map (fun c => "⟨" ++ c.decoder ++ "⟩")
    let predicates := children.map (fun c => "(" ++ c.admitted ++ ")")
    let instances := children.flatMap (fun c => ["⟨" ++ c.encoder ++ "⟩", "⟨" ++ c.decoder ++ "⟩"])
    let sourceTypes := arguments.map (fun t => "(" ++ (Reify.typ t).fmt.pretty ++ ")")
    let proofs := children.map (fun c => "(" ++ c.codec ++ ")")
    let carrier := qualified ++ " " ++ " ".intercalate carriers
    let admitted ← match RepresentationMaps.checkSupport env declaration with
      | .ok (_, _, outer, inner) => pure (
          "@" ++ env.q (Names.typeName outer.it) ++ ".admitted (" ++
          env.q (Names.typeName inner.it) ++ " " ++ " ".intercalate carriers ++ ") (" ++
          "@" ++ env.q (Names.typeName inner.it) ++ ".admitted " ++
          " ".intercalate (carriers ++ predicates) ++ ")")
      | .error _ => pure ("@" ++ qualified ++ ".admitted " ++
          " ".intercalate (carriers ++ predicates))
    pure { carrier
           encoder := "@" ++ qualified ++ ".toValue " ++ " ".intercalate (carriers ++ encoders)
           decoder := "@" ++ qualified ++ ".ofValue " ++ " ".intercalate (carriers ++ decoders)
           admitted
           codec := "@" ++ qualified ++ "." ++ env.part "codec" ++ " " ++
             " ".intercalate (carriers ++ instances ++ sourceTypes ++ predicates ++ proofs)
           dependencies := (name.it :: children.flatMap (·.dependencies)).eraseDups }
  | .TupleT [] =>
    pure { carrier := "Unit"
           encoder := "@ToValue.toValue Unit (inferInstance : ToValue Unit)"
           decoder := "Representation.Source.unitDecoder"
           admitted := "fun _ : Unit => True"
           codec := "@Representation.Source.unitCodec " ++ env.lib ++
             ".spec " ++ env.domainTerm
           dependencies := [] }
  | .TupleT [left, right] =>
    if let .TupleT (_ :: _ :: _) := env.resolve right.it then
      throw "source tuple right carrier would flatten a hidden product"
    let a ← resolve env known left
    let b ← resolve env known right
    let carrier := s!"({a.carrier}) × ({b.carrier})"
    let instances := s!"({a.carrier}) ({b.carrier}) ⟨{a.encoder}⟩ ⟨{a.decoder}⟩ " ++
      s!"⟨{b.encoder}⟩ ⟨{b.decoder}⟩"
    pure { carrier
           encoder := s!"@Representation.Source.pairEncoder ({a.carrier}) ({b.carrier}) " ++
             s!"⟨{a.encoder}⟩ ⟨{b.encoder}⟩"
           decoder := s!"@Representation.Source.pairDecoder ({a.carrier}) ({b.carrier}) " ++
             s!"⟨{a.decoder}⟩ ⟨{b.decoder}⟩"
           admitted := s!"fun p : {carrier} => ({a.admitted}) p.1 ∧ ({b.admitted}) p.2"
           codec := "@Representation.Source.pairCodec " ++ env.lib ++
             ".spec " ++ env.domainTerm ++ " " ++ instances ++
             s!" ({(Reify.typ left).fmt.pretty}) ({(Reify.typ right).fmt.pretty}) " ++
             s!"({a.admitted}) ({b.admitted}) ({a.codec}) ({b.codec})"
           dependencies := (a.dependencies ++ b.dependencies).eraseDups }
  | .TupleT _ => throw "source tuple field codec needs exact zero or two fields"
  | .FuncT .. => throw "source function field codec is not implemented"

end P4SpecTec.Codegen.RepresentationFields
