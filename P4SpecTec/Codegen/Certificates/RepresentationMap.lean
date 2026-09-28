import P4SpecTec.Codegen.Certificates.RepresentationContainer

/-! Complete polymorphic alias codecs composed from checked positional container codecs. -/

namespace P4SpecTec.Codegen.RepresentationMaps

open Std (Format)
open P4SpecTec.Lang.Il P4SpecTec.Codegen.Types

/-- Check a two-parameter alias to a source list container of positional pairs. -/
def checkSupport (env : Env) (d : Lang.Al.def) :
    Except String (id × id × id × id) := do
  let .TypD name [left, right] definition _ := d.it
    | throw "composite alias codec needs two source parameters"
  if left.it == right.it then throw "composite alias codec needs distinct parameters"
  if env.representation.hasRawExtern name.it then
    throw "composite alias codec needs separate source/runtime admission"
  let .PlainT target := definition.it | throw "composite alias codec needs a plain body"
  let .VarT outer [innerType] := target.it
    | throw "composite alias codec needs a unary container target"
  let .VarT inner [leftType, rightType] := innerType.it
    | throw "composite alias codec needs a positional binary element"
  if !typEq leftType.it (.VarT left []) || !typEq rightType.it (.VarT right []) then
    throw "composite alias codec needs direct parameters in declaration order"
  let some outerDeclaration := env.defs.find? (fun d => d.it.id.it == outer.it)
    | throw "composite alias codec needs its outer source declaration"
  let some innerDeclaration := env.defs.find? (fun d => d.it.id.it == inner.it)
    | throw "composite alias codec needs its element source declaration"
  let _ ← RepresentationContainers.listShape env outerDeclaration
  let _ ← RepresentationContainers.pairShape env innerDeclaration
  return (left, right, outer, inner)

private def proofTemplate : String :=
  "private theorem NAME.sourceValid {spec externalDomain} (keyType valueType : Lang.Il.typ) (v " ++
  ": Lang.Il.value)\n" ++
  "    (declared : body spec SOURCE_ID = some ([Q.i LEFT_ID, Q.i RIGHT_ID], .PlainT\n" ++
  "      (Q.t (Q.varT LIST_ID [Q.t (Q.varT PAIR_ID\n" ++
  "        [Q.t (Q.varT LEFT_ID []), Q.t (Q.varT RIGHT_ID [])])]))))\n" ++
  "    (payload : Valid spec externalDomain\n" ++
  "      (Q.varT LIST_ID [Q.t (Q.varT PAIR_ID [keyType, valueType])]) v) :\n" ++
  "    Valid spec externalDomain (Q.varT SOURCE_ID [keyType, valueType]) v := by\n" ++
  "  refine .alias (Q.i SOURCE_ID) [keyType, valueType] [Q.i LEFT_ID, Q.i RIGHT_ID] _\n" ++
  "    (Q.t (Q.varT LIST_ID [Q.t (Q.varT PAIR_ID [keyType, valueType])])) v declared\n" ++
  "    ⟨rfl, .cons ?_ .nil⟩ payload\n" ++
  "  refine .named (Q.i LIST_ID) _ _ rfl (.cons ?_ .nil)\n" ++
  "  refine .named (Q.i PAIR_ID) _ _ rfl (.cons ?_ (.cons ?_ .nil))\n" ++
  "  · exact .bound (Q.i LEFT_ID) keyType.it rfl\n" ++
  "  · exact .bound (Q.i RIGHT_ID) valueType.it rfl\n" ++
  "\n" ++
  "#audit_axioms NAME.sourceValid\n\n" ++
  "private theorem NAME.sourcePayload {spec externalDomain} (keyType valueType : Lang.Il.typ) " ++
  "(v : Lang.Il.value)\n" ++
  "    (declared : body spec SOURCE_ID = some ([Q.i LEFT_ID, Q.i RIGHT_ID], .PlainT\n" ++
  "      (Q.t (Q.varT LIST_ID [Q.t (Q.varT PAIR_ID\n" ++
  "        [Q.t (Q.varT LEFT_ID []), Q.t (Q.varT RIGHT_ID [])])]))))\n" ++
  "    (valid : Valid spec externalDomain (Q.varT SOURCE_ID [keyType, valueType]) v)\n" ++
  "    (sourceOnly : Representation.Source.Domain.SourceOnly externalDomain SOURCE_ID := by\n" ++
  "      source_only) :\n" ++
  "    ∃ keyType' valueType' : typ, keyType'.it = keyType.it ∧ valueType'.it = valueType.it ∧\n" ++
  "      Valid spec externalDomain\n" ++
  "        (Q.varT LIST_ID [Q.t (Q.varT PAIR_ID [keyType', valueType'])]) v := by\n" ++
  "  obtain ⟨instantiated, fields, payload⟩ := valid.plainPayload declared sourceOnly\n" ++
  "  obtain ⟨_, fields⟩ := fields\n" ++
  "  cases fields with\n" ++
  "  | cons sub rest =>\n" ++
  "    cases rest\n" ++
  "    obtain ⟨setArgs, result, arguments⟩ := sub.namedArguments (Q.i LIST_ID) _ rfl\n" ++
  "    cases arguments with\n" ++
  "    | cons pairSub rest =>\n" ++
  "      cases rest\n" ++
  "      obtain ⟨pairArgs, pairResult, pairArguments⟩ :=\n" ++
  "        pairSub.namedArguments (Q.i PAIR_ID) _ rfl\n" ++
  "      cases pairArguments with\n" ++
  "      | cons keySub rest =>\n" ++
  "        cases rest with\n" ++
  "        | cons itemSub rest =>\n" ++
  "          cases rest\n" ++
  "          have hk := keySub.boundResult (Q.i LEFT_ID) rfl\n" ++
  "          have hv := itemSub.boundResult (Q.i RIGHT_ID) rfl\n" ++
  "          refine ⟨_, _, hk, hv, ?_⟩\n" ++
  "          rw [result] at payload\n" ++
  "          apply payload.arguments\n" ++
  "          simpa only [List.map_cons, List.map_nil, Q.t, Util.Source.mkPhrase] using\n" ++
  "            congrArg (fun t : typ' => [t]) pairResult\n" ++
  "\n" ++
  "#audit_axioms NAME.sourcePayload\n\n" ++
  "/-- Every legal parameter codec yields the exact declared composite alias codec. -/\n" ++
  "theorem NAME.codec {α β : Type} [ToValue α] [OfValue α] [ToValue β] [OfValue β]\n" ++
  "    (leftType rightType : Lang.Il.typ) (left : α → Prop) (right : β → Prop)\n" ++
  "    (leftCodec : Representation.Codec (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain" ++
  " leftType.it) left)\n" ++
  "    (rightCodec : Representation.Codec\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain rightType.it) right) :\n" ++
  "    @Representation.Codec (QUALIFIED α β) ⟨QUALIFIED.toValue⟩\n" ++
  "      ⟨QUALIFIED.ofValue⟩\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain (Q.varT SOURCE_ID [leftType, " ++
  "rightType]))\n" ++
  "      (LIST_QUALIFIED.admitted (PAIR_QUALIFIED.admitted left right)) := by\n" ++
  "  letI : OfValue (LIST_QUALIFIED (PAIR_QUALIFIED α β)) :=\n" ++
  "    ⟨LIST_QUALIFIED.ofValue⟩\n" ++
  "  have innerCodec (a b : Lang.Il.typ) (ha : a.it = leftType.it) (hb : b.it = rightType.it) " ++
  ":=\n" ++
  "    LIST_QUALIFIED.codec (Q.t (Q.varT PAIR_ID [a,b]))\n" ++
  "      (PAIR_QUALIFIED.admitted left right)\n" ++
  "      (PAIR_QUALIFIED.codec a b left right (by simpa only [ha] using leftCodec)\n" ++
  "        (by simpa only [hb] using rightCodec))\n" ++
  "  refine @Representation.Codec.mk _ ⟨QUALIFIED.toValue⟩\n" ++
  "    ⟨QUALIFIED.ofValue⟩ _ _ ?_ ?_\n" ++
  "  · intro x hx\n" ++
  "    apply NAME.sourceValid leftType rightType _ (by rfl)\n" ++
  "    exact (@Representation.Codec.encodingValid _ _ _ _ _\n" ++
  "      (innerCodec leftType rightType rfl rfl)) x hx\n" ++
  "  · constructor\n" ++
  "    · intro fuel v x hv hd\n" ++
  "      obtain ⟨a, b, ha, hb, payload⟩ := NAME.sourcePayload leftType rightType v (by rfl) hv\n" ++
  "      cases fuel with\n" ++
  "      | zero => cases hd\n" ++
  "      | succ fuel =>\n" ++
  "        exact (@Representation.Codec.decoder _ _ _ _ _ (innerCodec a b ha hb)).sound fuel v " ++
  "x payload hd\n" ++
  "    · intro v hv\n" ++
  "      obtain ⟨a, b, ha, hb, payload⟩ := NAME.sourcePayload leftType rightType v (by rfl) hv\n" ++
  "      obtain ⟨x, bound, result⟩ := (@Representation.Codec.decoder _ _ _ _ _ (innerCodec a b " ++
  "ha hb)).sufficient v payload\n" ++
  "      refine ⟨x, bound + 1, ?_⟩\n" ++
  "      intro fuel hbound\n" ++
  "      cases fuel with\n" ++
  "      | zero => omega\n" ++
  "      | succ fuel => exact result fuel (by omega)\n" ++
  "#audit_axioms QUALIFIED.codec\n"

private def contractTemplate : String :=
  "∀ {α β : Type} [ToValue α] [OfValue α] [ToValue β] [OfValue β]\n" ++
  "    (leftType rightType : Lang.Il.typ) (left : α → Prop) (right : β → Prop)\n" ++
  "    (leftCodec : Representation.Codec (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain" ++
  " leftType.it) left)\n" ++
  "    (rightCodec : Representation.Codec\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain rightType.it) right),\n" ++
  "    @Representation.Codec (QUALIFIED α β) ⟨QUALIFIED.toValue⟩\n" ++
  "      ⟨QUALIFIED.ofValue⟩\n" ++
  "      (Representation.Source.Valid LIB.spec " ++
  "Representation.Source.externDomain (Q.varT SOURCE_ID [leftType, " ++
  "rightType]))\n" ++
  "      (LIST_QUALIFIED.admitted (PAIR_QUALIFIED.admitted left right))"

private def instantiate (env : Env) (d : Lang.Al.def) (template : String) :
    Except String String := do
  let (left, right, outer, inner) ← checkSupport env d
  let name := Names.typeName d.it.id.it
  let some info := env.types[outer.it]? | throw "source map outer type missing"
  let some (.VariantT cases) := info.deftyp | throw "source map outer type is not a variant"
  let some constructor := (Types.ctorNames cases).head? | throw "source map outer type is empty"
  return template
    |>.replace "LIST_CTOR" constructor
    |>.replace "PAIR_QUALIFIED" (env.q (Names.typeName inner.it))
    |>.replace "LIST_QUALIFIED" (env.q (Names.typeName outer.it))
    |>.replace "QUALIFIED" (env.q name)
    |>.replace "SOURCE_ID" (Reify.str d.it.id.it).fmt.pretty
    |>.replace "PAIR_ID" (Reify.str inner.it).fmt.pretty
    |>.replace "LIST_ID" (Reify.str outer.it).fmt.pretty
    |>.replace "LEFT_ID" (Reify.str left.it).fmt.pretty
    |>.replace "RIGHT_ID" (Reify.str right.it).fmt.pretty
    |>.replace "NAME" name
    |>.replace "LIB" env.lib

/-- Source container codec sidecars required to compose this alias certificate. -/
def dependencies (env : Env) (d : Lang.Al.def) : Except String (List String) := do
  let (_, _, outer, inner) ← checkSupport env d
  return [outer.it, inner.it]

/-- Exact complete codec obligation, with all source parameter domains universally quantified. -/
def codecType (env : Env) (d : Lang.Al.def) : Except String Format := do
  return Format.text (← instantiate env d contractTemplate)

private def encodingTemplate : String := "
/-- Encoded map validity is exactly independent validity of its encoded keys and values. -/
theorem NAME.encodingSourceIff {α β : Type} [ToValue α] [ToValue β]
    (leftType rightType : Lang.Il.typ) (x : QUALIFIED α β) :
    Valid LIB.spec Representation.Source.externDomain
      (Q.varT SOURCE_ID [leftType, rightType]) (QUALIFIED.toValue x) ↔
    LIST_QUALIFIED.admitted (PAIR_QUALIFIED.admitted
      (fun a => Valid LIB.spec Representation.Source.externDomain leftType.it (ToValue.toValue a))
      (fun b => Valid LIB.spec Representation.Source.externDomain
        rightType.it (ToValue.toValue b))) x := by
  cases x with
  | LIST_CTOR entries =>
    constructor
    · intro valid
      obtain ⟨a, b, ha, hb, payload⟩ := NAME.sourcePayload leftType rightType _ (by rfl) valid
      have accepted := (LIST_QUALIFIED.encodingSourceIff (Q.t (Q.varT PAIR_ID [a, b])) _).mp payload
      intro entry member
      have pairAccepted := (PAIR_QUALIFIED.encodingSourceIff a b entry).mp (accepted entry member)
      simpa only [ha, hb] using pairAccepted
    · intro accepted
      apply NAME.sourceValid leftType rightType _ (by rfl)
      apply (LIST_QUALIFIED.encodingSourceIff (Q.t (Q.varT PAIR_ID [leftType, rightType])) _).mpr
      intro entry member
      exact (PAIR_QUALIFIED.encodingSourceIff leftType rightType entry).mpr (accepted entry member)

#audit_axioms NAME.encodingSourceIff
"

/-- Emit the declared alias proof and preserve its actual decoder's extra fuel layer. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String Format := do
  let proof ← instantiate env d
    (proofTemplate.trimAsciiEnd.toString ++ "\n\n" ++ encodingTemplate.trimAscii.toString)
  return Format.text (boundedLines ("open Lang.Il Domain Representation.Source\n\n" ++ proof))

end P4SpecTec.Codegen.RepresentationMaps
