import P4SpecTec.Codegen.Certificates.RepresentationField
import P4SpecTec.Codegen.Graph

/-!
Complete source codecs for acyclic monomorphic single-constructor variants. The
supported constructor has one field whose complete source codec is separately checked.
Other constructor shapes remain explicit gaps, rather than partial family certificates.
-/

namespace P4SpecTec.Codegen.RepresentationVariants

open Std (Format)
open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Codegen.Types

/-- Validate a complete variant and resolve its independently specified field codec. -/
def checkSupport (env : Env) (d : Lang.Al.def)
    (known : String → Option RepresentationFields.NominalContract := fun _ => none) :
    Except String (typcase × typ × RepresentationFields.Contract) := do
  let .TypD name [] definition _ := d.it
    | throw "variant codec needs a monomorphic source declaration"
  if env.representation.hasRawExtern name.it then
    throw "variant codec needs separate source/runtime admission"
  let .VariantT [constructor] := definition.it
    | throw "variant codec currently needs one complete source constructor"
  let [field] := Mixfix.args constructor.nottyp.it
    | throw "variant codec currently needs one source field"
  let edges := Std.HashMap.ofList (env.defs.filterMap fun d =>
    match d.it with
    | .TypD name _ body _ => some (name.it, Env.deftypRefs body.it)
    | _ => none)
  for dependency in Env.typeRefs field.it do
    if (Graph.reachable edges dependency).contains name.it then
      throw "variant codec needs an acyclic source dependency graph"
  let contract ← RepresentationFields.resolve env known field
  let _ ← RepresentationFields.normalizeSubstitution field
  let _ ← RepresentationFields.identitySubstitution field
  return (constructor, field, contract)

/-- Exact full-domain codec type with explicit nominal dictionaries. -/
def codecType (env : Env) (d : Lang.Al.def)
    (known : String → Option RepresentationFields.NominalContract := fun _ => none) :
    Except String Format := do
  let _ ← checkSupport env d known
  let name := env.q (Names.typeName d.it.id.it)
  return Format.text (s!"@Refine.Representation.Codec {name} ⟨{name}.toValue⟩ " ++
    s!"⟨{name}.ofValue⟩ {name}.source {name}.admitted")

private def proofTemplate : String :=
  "/-- The complete independent source grammar of the quoted " ++
  "variant. -/\n" ++
  "def NAME.source (v : Lang.Il.value) : Prop :=\n" ++
  "  Representation.Source.Valid LIB.spec Representation.Source.externDomain\n" ++
  "    (Q.varT SOURCE_ID []) v\n" ++
  "private theorem NAME.sourceFields (v : Lang.Il.value) (hv : " ++
  "NAME.source v) :\n" ++
  "    ∃ tree : Mixfix.t Lang.Il.value, v.it = .CaseV tree ∧\n" ++
  "      Mixfix.eq_mixop tree MIXOP = true ∧\n" ++
  "      ∃ text : Lang.Il.value, Mixfix.args tree = [text] ∧\n" ++
  "        FIELD_SOURCE text := by\n" ++
  "  have normalize : ∀ actual : Lang.Il.typ,\n" ++
  "      Representation.Source.Substitutes [] (FIELD_TYPE).it " ++
  "actual.it →\n" ++
  "      ∀ v, Representation.Source.Valid LIB.spec Representation.Source.externDomain" ++
  "\n" ++
  "        actual.it v → FIELD_SOURCE v := NORMALIZE\n" ++
  "  obtain ⟨constructor, member, fields, instantiated, tree, shape, " ++
  "matching, valid⟩ :=\n" ++
  "    hv.variantPayload (Q.i SOURCE_ID) [] []\n" ++
  "      [SOURCE_CASE]\n" ++
  "      v (by rfl)\n" ++
  "  simp only [List.mem_cons, List.not_mem_nil, or_false] at " ++
  "member\n" ++
  "  subst constructor\n" ++
  "  dsimp [Representation.Source.instantiatedFields, Q.tc, Q.nt, " ++
  "Q.t, Lang.Il.typcase.nottyp,\n" ++
  "    P4SpecTec.Util.Source.mkPhrase, Mixfix.args] at instantiated\n" ++
  "  repeat' first\n" ++
  "    | simp only [Mixfix.args] at instantiated\n" ++
  "    | dsimp only [List.flatMap, List.append, List.map, " ++
  "List.flatten] at instantiated\n" ++
  "  rcases instantiated with ⟨_, instantiated⟩\n" ++
  "  cases instantiated with\n" ++
  "  | cons first rest =>\n" ++
  "    cases rest\n" ++
  "    generalize hargs : Mixfix.args tree = args at valid\n" ++
  "    cases valid with\n" ++
  "    | cons type text types values head tail =>\n" ++
  "      cases tail\n" ++
  "      have head := normalize _ first text head\n" ++
  "      exact ⟨tree, shape, Representation.Source.mixopTrans tree _ " ++
  "_ matching rfl, text, hargs, head⟩\n" ++
  "\n" ++
  "#audit_axioms QUALIFIED.sourceFields\n" ++
  "\n" ++
  "/-- Admission is inherited from the independently specified field " ++
  "contract. -/\n" ++
  "def NAME.admitted : QUALIFIED → Prop\n" ++
  "  | .CTOR x => (FIELD_ADMITTED) x\n" ++
  "\n" ++
  "/-- The full source codec fixes the actual named encoder and " ++
  "decoder dictionaries. -/\n" ++
  "theorem NAME.codec :\n" ++
  "    @Representation.Codec QUALIFIED ⟨QUALIFIED.toValue⟩ " ++
  "⟨QUALIFIED.ofValue⟩\n" ++
  "      NAME.source NAME.admitted := by\n" ++
  "  letI : ToValue QUALIFIED := ⟨QUALIFIED.toValue⟩\n" ++
  "  letI : OfValue QUALIFIED := ⟨QUALIFIED.ofValue⟩\n" ++
  "  letI : ToValue (FIELD_CARRIER) := ⟨FIELD_ENCODER⟩\n" ++
  "  letI : OfValue (FIELD_CARRIER) := ⟨FIELD_DECODER⟩\n" ++
  "  have childCodec : FIELD_CODEC_TYPE := FIELD_CODEC\n" ++
  "  refine { encodingValid := ?_, decoder := { sound := ?_, " ++
  "sufficient := ?_ } }\n" ++
  "  · intro x hx\n" ++
  "    cases x with\n" ++
  "    | CTOR text =>\n" ++
  "      change (FIELD_ADMITTED) text at hx\n" ++
  "      apply Representation.Source.ConstructorDomain.valid\n" ++
  "        (Q.i SOURCE_ID) [] []\n" ++
  "        [SOURCE_CASE]\n" ++
  "        (SOURCE_CASE)\n" ++
  "        [FIELD_TYPE] _ (by rfl) (by simp)\n" ++
  "        (by\n" ++
  "          refine ⟨rfl, ?_⟩\n" ++
  "          dsimp [Q.tc, Q.nt, Q.t, Lang.Il.typcase.nottyp,\n" ++
  "            P4SpecTec.Util.Source.mkPhrase, Mixfix.args]\n" ++
  "          repeat' first\n" ++
  "            | simp only [Mixfix.args]\n" ++
  "            | dsimp only [List.flatMap, List.append, List.map, " ++
  "List.flatten]\n" ++
  "          change List.Forall₂ (fun a b : Lang.Il.typ =>\n" ++
  "            Representation.Source.Substitutes [] a.it b.it) " ++
  "[FIELD_TYPE] [FIELD_TYPE]\n" ++
  "          exact .cons FIELD_IDENTITY .nil)\n" ++
  "      refine ⟨RENDERED_TEXT,\n" ++
  "        rfl, rfl, ?_⟩\n" ++
  "      repeat' first\n" ++
  "        | simp only [Mixfix.args]\n" ++
  "        | dsimp only [List.flatMap, List.append, List.map, " ++
  "List.flatten]\n" ++
  "      exact .cons (FIELD_TYPE) ((FIELD_ENCODER) text) [] [] " ++
  "(childCodec.encodingValid text hx) .nil\n" ++
  "  · intro fuel v x hv hd\n" ++
  "    obtain ⟨tree, shape, matching, text, fields, valid⟩ := " ++
  "NAME.sourceFields v hv\n" ++
  "    have args : Prelude.Value.caseArgs tree\n" ++
  "        MIXOP = some [text] := by\n" ++
  "      change Mixfix.eq_mixop tree\n" ++
  "        MIXOP = true at matching\n" ++
  "      simp only [Prelude.Value.caseArgs, matching, ite_true, " ++
  "fields]\n" ++
  "    cases fuel with\n" ++
  "    | zero => cases hd\n" ++
  "    | succ fuel =>\n" ++
  "      simp only [OfValue.ofValue, QUALIFIED.ofValue, shape, args] " ++
  "at hd\n" ++
  "      cases decoded : (FIELD_DECODER) fuel text with\n" ++
  "      | none =>\n" ++
  "        change ((FIELD_DECODER) fuel text).bind (fun r => some " ++
  "(QUALIFIED.CTOR r)) = some x at hd\n" ++
  "        rw [decoded] at hd\n" ++
  "        cases hd\n" ++
  "      | some result =>\n" ++
  "        change ((FIELD_DECODER) fuel text).bind (fun r => some " ++
  "(QUALIFIED.CTOR r)) = some x at hd\n" ++
  "        rw [decoded] at hd\n" ++
  "        change some (QUALIFIED.CTOR result) = some x at hd\n" ++
  "        cases Option.some.inj hd\n" ++
  "        have related := childCodec.decoder.sound fuel text result " ++
  "valid decoded\n" ++
  "        constructor\n" ++
  "        · exact related.1\n" ++
  "        ·\n" ++
  "          change Rel v (QUALIFIED.toValue (.CTOR result))\n" ++
  "          apply Representation.Source.caseRelation (rendered :=\n" ++
  "            RENDERED_RESULT)\n" ++
  "            shape rfl\n" ++
  "          · exact Representation.Source.mixopTrans tree _ _ " ++
  "matching rfl\n" ++
  "          · rw [fields]\n" ++
  "            repeat' first\n" ++
  "              | simp only [Mixfix.args]\n" ++
  "              | dsimp only [List.flatMap, List.append, List.map, " ++
  "List.flatten]\n" ++
  "            dsimp only [canons]\n" ++
  "            exact congrArg (fun c => [c]) related.2\n" ++
  "  · intro v hv\n" ++
  "    obtain ⟨tree, shape, matching, text, fields, valid⟩ := " ++
  "NAME.sourceFields v hv\n" ++
  "    obtain ⟨result, bound, stable⟩ := " ++
  "childCodec.decoder.sufficient text valid\n" ++
  "    change ∀ fuel, bound ≤ fuel → (FIELD_DECODER) fuel text =\n" ++
  "      some result at stable\n" ++
  "    refine ⟨ .CTOR result, bound + 1, ?_⟩\n" ++
  "    intro fuel large\n" ++
  "    cases fuel with\n" ++
  "    | zero => omega\n" ++
  "    | succ fuel =>\n" ++
  "      have args : Prelude.Value.caseArgs tree\n" ++
  "          MIXOP = some [text] := by\n" ++
  "        change Mixfix.eq_mixop tree\n" ++
  "          MIXOP = true at matching\n" ++
  "        simp only [Prelude.Value.caseArgs, matching, ite_true, " ++
  "fields]\n" ++
  "      simp only [OfValue.ofValue, QUALIFIED.ofValue, shape, " ++
  "args]\n" ++
  "      change ((FIELD_DECODER) fuel text).bind (fun r => some " ++
  "(QUALIFIED.CTOR r)) = _\n" ++
  "      rw [stable fuel (by omega)]\n" ++
  "      rfl\n" ++
  "\n" ++
  "#audit_axioms QUALIFIED.codec\n"

/-- Emit the checked complete constructor codec, preserving field admission and fuel. -/
def declarations (env : Env) (d : Lang.Al.def)
    (known : String → Option RepresentationFields.NominalContract := fun _ => none) :
    Except String Format := do
  let (constructor, field, contract) ← checkSupport env d known
  let name := Names.typeName d.it.id.it
  let qualified := env.q name
  let ctor := (ctorNames [constructor]).head!
  -- A typcase term is extracted directly, preserving the source constructor recipe.
  let .VariantT [c] := (match d.it with | .TypD _ _ body _ => body.it | _ => .VariantT [])
    | throw "variant source constructor disappeared"
  let (origin, arguments) := match c.typorigin.it with | .mk origin arguments => (origin, arguments)
  let sourceCase := (Term.call "Q.tc" [Reify.mixfix c.nottyp.it Reify.typ,
    Reify.str origin.it, Reify.lst (arguments.map Reify.typ)]).fmt.pretty 1000000
  let mixop := Mixfix.to_mixop constructor.nottyp.it
  let source := RepresentationFields.source env field
  let rendered (valueName : String) :=
    (mixfixTerm mixop [.atom (s!"(({contract.encoder}) {valueName})")]).fmt.pretty 1000000
  let text := proofTemplate
    |>.replace "FIELD_CODEC_TYPE" (contract.type source)
    |>.replace "FIELD_CODEC" contract.codec
    |>.replace "FIELD_CARRIER" contract.carrier
    |>.replace "FIELD_ENCODER" contract.encoder
    |>.replace "FIELD_DECODER" contract.decoder
    |>.replace "FIELD_ADMITTED" contract.admitted
    |>.replace "FIELD_IDENTITY" ("(" ++ (← RepresentationFields.identitySubstitution field) ++ ")")
    |>.replace "FIELD_SOURCE" ("(" ++ source ++ ")")
    |>.replace "FIELD_TYPE" ("(" ++ (Reify.typ field).fmt.pretty 1000000 ++ ")")
    |>.replace "NORMALIZE" (← RepresentationFields.normalizeSubstitution field)
    |>.replace "RENDERED_TEXT" (rendered "text")
    |>.replace "RENDERED_RESULT" (rendered "result")
    |>.replace "SOURCE_CASE" sourceCase
    |>.replace "SOURCE_ID" ((Reify.str d.it.id.it).fmt.pretty 1000000)
    |>.replace "MIXOP" ((mixopTerm mixop).fmt.pretty 1000000)
    |>.replace "QUALIFIED" qualified
    |>.replace "NAME" name
    |>.replace "CTOR" ctor
    |>.replace "LIB" env.lib
    |>.replace "Mixfix." "Domain.Mixfix."
  return Format.text (boundedLines (text.replace "\nprivate theorem"
    "\n\nprivate theorem" |>.replace "\n/--" "\n\n/--"))

end P4SpecTec.Codegen.RepresentationVariants
