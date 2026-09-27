import P4SpecTec.Codegen.Certificates.RepresentationField
import P4SpecTec.Codegen.Graph
import P4SpecTec.Codegen.Reify

/-!
Certificates for complete monomorphic source aliases over checked field contracts. The source
domain follows the actual quoted declarations; the decoder proof composes the named
alias dictionaries with a checked fuel layer for each declared alias.
-/

namespace P4SpecTec.Codegen.RepresentationAliases

open Std (Format)
open P4SpecTec.Lang.Il

private partial def chain (env : Env) (seen : List String) (name : String) :
    Except String (List (String × typ)) := do
  if seen.contains name then throw "source alias cycle"
  if env.representation.hasRawExtern name then
    throw "source alias requires separate runtime admission"
  let some info := env.types[name]? | throw s!"unknown source alias {name}"
  if !info.tparams.isEmpty then throw "source alias requires parameter codecs"
  let some (.PlainT target) := info.deftyp | throw "source alias does not have a plain body"
  match target.it with
  | .TextT => pure [(name, target)]
  | .VarT next [] => do
    let tail ← chain env (name :: seen) next.it
    pure ((name, target) :: tail)
  | _ => throw "source alias does not end in byte text"

/-- Verify that every alias in the complete source chain is monomorphic and ends in text. -/
def checkSupport (env : Env) (d : Lang.Al.def) : Except String (List (String × typ)) := do
  let .TypD name [] definition _ := d.it | throw "source alias needs a monomorphic declaration"
  let .PlainT _ := definition.it | throw "source alias needs a plain body"
  chain env [] name.it

/-- The obligation fixes named encoder and decoder dictionaries despite reducible aliases. -/
def codecType (env : Env) (d : Lang.Al.def) : Except String Format := do
  let _ ← checkSupport env d
  let name := env.q (Names.typeName d.it.id.it)
  pure (Format.text (s!"@Refine.Representation.Codec {name} ⟨{name}.toValue⟩ " ++
    s!"⟨{name}.ofValue⟩ {name}.source (fun _ : {name} => True)"))

/-- Emit a source-grammar bridge and the actual named decoder's complete codec contract. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String Format := do
  let aliases ← checkSupport env d
  let name := Names.typeName d.it.id.it
  let qualified := env.q name
  let idText := (Reify.str d.it.id.it).fmt.pretty
  let mut steps := ""
  for (aliasName, target) in aliases do
    let id := (Reify.str aliasName).fmt.pretty
    let targetText := (Reify.typ target).arg.pretty
    match target.it with
    | .TextT =>
      steps := steps ++ s!"  exact Representation.Source.textAliasIff (Q.i {id}) " ++
        s!"{targetText} (by rfl) rfl v\n"
    | .VarT next [] =>
      let nextId := (Reify.str next.it).fmt.pretty
      steps := steps ++ s!"  rw [Representation.Source.plainAliasIff (Q.i {id}) " ++
        s!"{targetText} (by rfl)\n" ++
        s!"    (fun _ h => h.emptyNamedResult (Q.i {nextId}))\n" ++
        s!"    (Representation.Source.Substitutes.named (Q.i {nextId}) [] [] rfl .nil)]\n"
    | _ => throw "unexpected checked source alias shape"
  let text := "/-- The complete source alias grammar in the actual quoted specification. -/\n" ++
    s!"def {name}.source (v : Lang.Il.value) : Prop :=\n" ++
    s!"  Representation.Source.Valid {env.lib}.spec Representation.Source.externDomain " ++
    s!"(Q.varT {idText} []) v\n\n" ++
    "/-- The declared source alias has exactly the byte-text tag domain. -/\n" ++
    s!"theorem {name}.sourceIff (v : Lang.Il.value) :\n" ++
    s!"    {qualified}.source v ↔ Representation.Shape.text v := by\n" ++
    s!"  unfold {qualified}.source\n" ++ steps ++
    s!"\n#audit_axioms {qualified}.sourceIff\n\n" ++
    "/-- Admitted encodings are valid and the named decoder is sound and sufficient. -/\n" ++
    s!"theorem {name}.codec : " ++ (← codecType env d).pretty ++ " := by\n" ++
    s!"  letI : ToValue {qualified} := ⟨{qualified}.toValue⟩\n" ++
    s!"  letI : OfValue {qualified} := ⟨{qualified}.ofValue⟩\n" ++
    "  constructor\n" ++
    "  · intro x _\n" ++
    s!"    apply ({qualified}.sourceIff _).mpr\n" ++
    "    exact ⟨x, rfl⟩\n" ++
    "  ·\n" ++
    s!"    have hs : {qualified}.source = Representation.Shape.text :=\n" ++
    s!"      funext fun v => propext ({qualified}.sourceIff v)\n" ++
    "    rw [hs]\n" ++
    "    repeat first\n" ++
    "      | exact @Representation.Codec.decoder ByteText instToValueByteText " ++
      "instOfValueByteText\n" ++
    "          Representation.Shape.text (fun _ => True) Representation.textCodec\n" ++
    "      | apply Representation.DecoderCorrect.delay\n" ++
    s!"\n#audit_axioms {qualified}.codec"
  pure (Format.text (boundedLines text))

/-- Resolve a complete acyclic monomorphic alias body against checked field contracts. -/
def fieldSupport (env : Env) (known : String → Option RepresentationFields.NominalContract)
    (d : Lang.Al.def) : Except String (typ × RepresentationFields.Contract) := do
  let .TypD name [] definition _ := d.it
    | throw "source alias needs a monomorphic declaration"
  if env.representation.hasRawExtern name.it then
    throw "source alias needs separate source/runtime admission"
  let .PlainT target := definition.it | throw "source alias needs a plain body"
  let edges := Std.HashMap.ofList (env.defs.filterMap fun d => match d.it with
    | .TypD name _ body _ => some (name.it, Env.deftypRefs body.it)
    | _ => none)
  for dependency in Env.typeRefs target.it do
    if (Graph.reachable edges dependency).contains name.it then
      throw "source alias needs an acyclic dependency graph"
  let contract ← RepresentationFields.resolve env known target
  let _ ← RepresentationFields.normalizeSubstitution target
  let _ ← RepresentationFields.identitySubstitution target
  return (target, contract)

/-- Exact named codec obligation for a resolved alias body. -/
def fieldCodecType (env : Env) (known : String → Option RepresentationFields.NominalContract)
    (d : Lang.Al.def) : Except String Format := do
  let _ ← fieldSupport env known d
  let name := env.q (Names.typeName d.it.id.it)
  pure (Format.text (s!"@Refine.Representation.Codec {name} ⟨{name}.toValue⟩ " ++
    s!"⟨{name}.ofValue⟩ {name}.source {name}.admitted"))

/-- Emit full alias-domain transport and the actual named decoder's extra fuel layer. -/
def fieldDeclarations (env : Env) (known : String → Option RepresentationFields.NominalContract)
    (d : Lang.Al.def) : Except String Format := do
  let (target, contract) ← fieldSupport env known d
  let name := Names.typeName d.it.id.it
  let qualified := env.q name
  let sourceId := (Reify.str d.it.id.it).fmt.pretty
  let targetType := (Reify.typ target).arg.pretty
  let fieldSource := RepresentationFields.source env target
  let normalize ← RepresentationFields.normalizeSubstitution target
  let identity ← RepresentationFields.identitySubstitution target
  let text := "/-- The complete independent source alias grammar. -/\n" ++
    s!"def {name}.source (v : Lang.Il.value) : Prop :=\n" ++
    s!"  Representation.Source.Valid {env.lib}.spec Representation.Source.externDomain " ++
    s!"(Q.varT {sourceId} []) v\n\n" ++
    "/-- Alias admission is the independently stated body admission. -/\n" ++
    s!"def {name}.admitted : {qualified} → Prop := {contract.admitted}\n\n" ++
    s!"private theorem {name}.bodyCodec : {contract.type fieldSource} :=\n" ++
    s!"  {contract.codec}\n\n#audit_axioms {qualified}.bodyCodec\n\n" ++
    s!"private theorem {name}.sourceIff (v : Lang.Il.value) :\n" ++
    s!"    {qualified}.source v ↔ ({fieldSource}) v := by\n" ++
    s!"  exact Representation.Source.plainAliasDomainIff (Q.i {sourceId}) {targetType}\n" ++
    s!"    (by rfl) {normalize} ({identity}) v\n\n" ++
    s!"#audit_axioms {qualified}.sourceIff\n\n" ++
    "/-- The alias encoder has exactly its declared body's independent source domain. -/\n" ++
    s!"theorem {name}.encodingSourceIff (x : {qualified}) :\n" ++
    s!"    {qualified}.source ({qualified}.toValue x) ↔ " ++
    s!"({fieldSource}) (({contract.encoder}) x) :=\n" ++
    s!"  {qualified}.sourceIff _\n\n#audit_axioms {qualified}.encodingSourceIff\n\n" ++
    "/-- Complete alias codec, with the declared alias fuel frame retained. -/\n" ++
    s!"theorem {name}.codec : " ++ (← fieldCodecType env known d).pretty ++ " := by\n" ++
    s!"  refine @Representation.Codec.mk {qualified} ⟨{qualified}.toValue⟩\n" ++
    s!"    ⟨{qualified}.ofValue⟩ _ _ ?_ ?_\n" ++
    "  · intro x hx\n" ++
    s!"    apply ({qualified}.sourceIff _).mpr\n" ++
    s!"    exact ({contract.encodingProof fieldSource (qualified ++ ".bodyCodec")}) x hx\n" ++
    "  · constructor\n" ++
    "    · intro fuel v x hv hd\n" ++
    "      cases fuel with\n" ++
    "      | zero => cases hd\n" ++
    "      | succ fuel =>\n" ++
    s!"        exact ({contract.soundProof fieldSource (qualified ++ ".bodyCodec")})\n" ++
    s!"          fuel v x (({qualified}.sourceIff v).mp hv) hd\n" ++
    "    · intro v hv\n" ++
    s!"      obtain ⟨x, bound, result⟩ := ({contract.sufficientProof fieldSource
      (qualified ++ ".bodyCodec")})\n" ++
    s!"        v (({qualified}.sourceIff v).mp hv)\n" ++
    "      refine ⟨x, bound + 1, ?_⟩\n" ++
    "      intro fuel hbound\n" ++
    "      cases fuel with\n" ++
    "      | zero => omega\n" ++
    "      | succ fuel => exact result fuel (by omega)\n\n" ++
    s!"#audit_axioms {qualified}.codec"
  pure (Format.text (boundedLines text))

end P4SpecTec.Codegen.RepresentationAliases
