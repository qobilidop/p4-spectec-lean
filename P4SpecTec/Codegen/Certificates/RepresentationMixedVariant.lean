import P4SpecTec.Codegen.Certificates.RepresentationConstructor
import P4SpecTec.Codegen.Certificates.RepresentationField
import P4SpecTec.Codegen.Graph

/-!
Complete source codecs for finite acyclic monomorphic variants. Every positional field
has an independently checked source codec; actual constructor order and grammar remain
unchanged. This is our own certificate generation, not an upstream mirror.
-/

namespace P4SpecTec.Codegen.RepresentationMixedVariants

open Std (Format)
open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Codegen.Types
open RepresentationFields

/-- A complete source constructor and its independently checked positional fields. -/
structure Constructor where
  /-- Exact quoted constructor recipe. -/
  source : typcase
  /-- All source fields, in their actual positional order, with complete codecs. -/
  fields : List (typ × Contract)

/-- Reject incomplete, ambiguous or cyclic finite constructor families. -/
def checkSupport (env : Env) (d : Lang.Al.def)
    (known : String → Option NominalContract := fun _ => none) :
    Except String (List Constructor) := do
  let .TypD name [] definition _ := d.it
    | throw "variant codec needs a monomorphic source declaration"
  if env.representation.hasRawExtern name.it then
    throw "variant codec needs separate source/runtime admission"
  let .VariantT constructors := definition.it
    | throw "variant codec needs a complete source variant"
  if constructors.isEmpty then throw "variant codec needs a nonempty source constructor family"
  for (constructor, i) in constructors.zipIdx do
    for (other, j) in constructors.zipIdx do
      if i != j && Mixfix.eq_mixop constructor.nottyp.it other.nottyp.it then
        throw "variant codec needs disjoint source constructor notations"
  let edges := Std.HashMap.ofList (env.defs.filterMap fun d =>
    match d.it with
    | .TypD name _ body _ => some (name.it, Env.deftypRefs body.it)
    | _ => none)
  constructors.mapM fun constructor => do
    let fields ← (Mixfix.args constructor.nottyp.it).mapM fun field => do
      for dependency in Env.typeRefs field.it do
        if (Graph.reachable edges dependency).contains name.it then
          throw "variant codec needs an acyclic source dependency graph"
      let contract ← resolve env known field
      let _ ← normalizeSubstitution field
      let _ ← identitySubstitution field
      pure (field, contract)
    return { source := constructor, fields }

/-- Semantic support imported by every emitted complete variant certificate. -/
def supportImports : List String :=
  ["P4SpecTec.Refine.Representation.SourceCodec",
   "P4SpecTec.Refine.Representation.SourceExtern",
   "P4SpecTec.Refine.Representation.SourceVariant", "P4SpecTec.Tactic.Audit"]

/-- The exact full-domain codec type fixes both actual named dictionaries. -/
def codecType (env : Env) (d : Lang.Al.def)
    (known : String → Option NominalContract := fun _ => none) : Except String Format := do
  let _ ← checkSupport env d known
  let name := env.q (Names.typeName d.it.id.it)
  return Format.text (s!"@Refine.Representation.Codec {name} ⟨{name}.toValue⟩ " ++
    s!"⟨{name}.ofValue⟩ {name}.{env.part "source"} {name}.{env.part "admitted"}")

private def sourceTerm (c : typcase) : String :=
  let (origin, arguments) := match c.typorigin.it with | .mk origin arguments => (origin, arguments)
  (Term.call "Q.tc" [Reify.mixfix c.nottyp.it Reify.typ,
    Reify.str origin.it, Reify.lst (arguments.map Reify.typ)]).fmt.pretty 1000000

private def indent (text : String) : String :=
  "  " ++ text.trimAsciiEnd.toString.replace "\n" "\n  "

private def listText (terms : List String) : String := "[" ++ ", ".intercalate terms ++ "]"

private def tupleText (terms : List String) : String := "⟨" ++ ", ".intercalate terms ++ "⟩"

private def indexNames (prefixName : String) (count : Nat) : List String :=
  (List.range count).map fun index => prefixName ++ toString index

private def consProof (terms : List String) : String :=
  terms.foldr (fun term tail => s!".cons ({term}) ({tail})") ".nil"

private def reduceArguments (location : String := "") : String :=
  "repeat' first\n" ++
  s!"  | simp only [Domain.Mixfix.args]{location}\n" ++
  s!"  | dsimp only [List.flatMap, List.append, List.map, List.flatten]{location}\n"

private def substitutionUnwrap (index count : Nat) (body : String) : String :=
  match count with
  | 0 => "cases tail\n" ++ body
  | count + 1 =>
    let substitutions := if index == 0 then "sub" else "tail"
    s!"cases {substitutions} with\n| cons sub{index} tail =>\n" ++
      indent (substitutionUnwrap (index + 1) count body)

private def valuesUnwrap (index count : Nat) (body : String) : String :=
  match count with
  | 0 => "cases tail\n" ++ body
  | count + 1 =>
    let values := if index == 0 then "valid" else "tail"
    s!"cases {values} with\n| cons _ v{index} _ _ p{index} tail =>\n" ++
      indent (valuesUnwrap (index + 1) count body)

private def decoderUnwrap (fields : List (typ × Contract)) (index : Nat)
    (body : String) : String :=
  match fields with
  | [] => body
  | (_, field) :: fields =>
    let prior := indexNames "d" (index + 1)
    s!"cases d{index} : ({field.decoder}) fuel v{index} with\n" ++
      "| none => simp [" ++ ", ".intercalate prior ++ "] at decoded\n" ++
      s!"| some x{index} =>\n" ++ indent (decoderUnwrap fields (index + 1) body)

private def fieldProofName (name : String) (constructor field : Nat) : String :=
  s!"{name}.fieldCodec{constructor}_{field}"

private def substitutionName (name : String) (constructor field : Nat) : String :=
  s!"{name}.fieldSubstitution{constructor}_{field}"

private def constructorTerm (qualified ctor : String) (args : List String) : String :=
  "(" ++ " ".intercalate (s!"{qualified}.{ctor}" :: args) ++ ")"

private def decodedFields (qualified ctor : String) (fields : List (typ × Contract)) : String :=
  fields.zipIdx.foldr (fun ((_, field), index) tail =>
    s!"(({field.decoder}) fuel v{index}).bind (fun x{index} => {tail})")
    ("some " ++ constructorTerm qualified ctor (indexNames "x" fields.length))

private def payloadBranch (name : String) (index : Nat) (c : Constructor) : String :=
  let transfers := c.fields.zipIdx.map fun (_, i) =>
    s!"{substitutionName name index i} _ sub{i}"
  "dsimp [Representation.Source.instantiatedFields, Q.tc, Q.nt, Q.t,\n" ++
  "  Lang.Il.typcase.nottyp, P4SpecTec.Util.Source.mkPhrase] at sub\n" ++
  reduceArguments " at sub" ++ "obtain ⟨_, sub⟩ := sub\n" ++
  (if c.fields.isEmpty then
    "cases sub\n" ++
    "dsimp [Q.tc, Q.nt, Q.t, Lang.Il.typcase.nottyp, P4SpecTec.Util.Source.mkPhrase]\n" ++
    reduceArguments ++ "exact .nil"
  else substitutionUnwrap 0 c.fields.length (
    "dsimp [Q.tc, Q.nt, Q.t, Lang.Il.typcase.nottyp, P4SpecTec.Util.Source.mkPhrase]\n" ++
    reduceArguments ++ "exact " ++ consProof transfers))

private def branchInputs (c : Constructor) (body : String) : String :=
  "dsimp [Q.tc, Q.nt, Q.t, Lang.Il.typcase.nottyp, P4SpecTec.Util.Source.mkPhrase] at valid\n" ++
  reduceArguments " at valid" ++
  "generalize hargs : Domain.Mixfix.args tree = args at valid\n" ++
  (if c.fields.isEmpty then "cases valid\n" ++ body
    else valuesUnwrap 0 c.fields.length body)

/-- Emit the complete actual constructor family with exact field codecs and failure boundaries. -/
def declarations (env : Env) (d : Lang.Al.def)
    (known : String → Option NominalContract := fun _ => none) : Except String Format := do
  let constructors ← checkSupport env d known
  let name := Names.typeName d.it.id.it
  let qualified := env.q name
  let source := env.part "source"
  let admitted := env.part "admitted"
  let codec := env.part "codec"
  let id := "(Q.i " ++ (Reify.str d.it.id.it).fmt.pretty 1000000 ++ ")"
  let sourceId := (Reify.str d.it.id.it).fmt.pretty 1000000
  let cases := listText (constructors.map (sourceTerm ·.source))
  let names := ctorNames (constructors.map (·.source))
  let mut fieldProofs := ""
  let mut decoders := ""
  let mut admissions := ""
  let mut payload := ""
  let mut encoding := ""
  let mut sound := ""
  let mut sufficient := ""
  for ((c, ctor), index) in (constructors.zip names).zipIdx do
    let count := c.fields.length
    let xs := indexNames "x" count
    let raw := indexNames "v" count
    let admitNames := indexNames "admitted" count
    let typed := constructorTerm qualified ctor xs
    let fieldTypes := listText (c.fields.map fun (t, _) => (Reify.typ t).fmt.pretty 1000000)
    let mixop := Mixfix.to_mixop c.source.nottyp.it
    let rendered := (mixfixTerm mixop (c.fields.zipIdx.map fun ((_, field), i) =>
      .atom (s!"(({field.encoder}) x{i})"))).fmt.pretty 1000000
    let admission := " ∧ ".intercalate ((c.fields.zipIdx.map fun ((_, field), i) =>
      s!"({field.admitted}) x{i}") ++ ["True"])
    admissions := admissions ++ "  | " ++ " ".intercalate (s!".{ctor}" :: xs) ++
      s!" => {admission}\n"
    let mut identities := []
    let mut fieldEncodings := []
    let mut enough := ""
    let mut faithful := ""
    let mut stable := ""
    for ((t, field), i) in c.fields.zipIdx do
      let fieldSource := RepresentationFields.source env t
      let proof := fieldProofName name index i
      let substitution := substitutionName name index i
      fieldProofs := fieldProofs ++
        "/-- The exact positional field codec on its independent source grammar. -/\n" ++
        s!"private theorem {proof} : {field.type fieldSource} :=\n" ++ indent field.codec ++
        s!"\n\n#audit_axioms {qualified}.fieldCodec{index}_{i}\n\n" ++
        "/-- Empty substitution preserves the complete independent field domain. -/\n" ++
        s!"private theorem {substitution} : ∀ actual,\n" ++
        s!"    Representation.Source.Substitutes [] ({(Reify.typ t).fmt.pretty 1000000}).it " ++
        "actual → ∀ v,\n" ++
        s!"    Representation.Source.Valid {env.lib}.spec " ++
        s!"{env.domainTerm} actual v → ({fieldSource}) v :=\n" ++
        indent (← normalizeSubstitution t) ++
        s!"\n\n#audit_axioms {qualified}.fieldSubstitution{index}_{i}\n\n"
      identities := identities ++ [← identitySubstitution t]
      fieldEncodings := fieldEncodings ++ [s!".cons _ _ _ _ " ++
        s!"(({field.encodingProof fieldSource proof}) x{i} admitted{i})"]
      faithful := faithful ++ s!"obtain ⟨admitted{i}, related{i}⟩ :=\n" ++
        indent (s!"({field.soundProof fieldSource proof}) fuel v{i} x{i} p{i} d{i}") ++ "\n" ++
        s!"have canonical{i} : canon v{i} = canon (({field.encoder}) x{i}) := related{i}\n"
      stable := stable ++ s!"obtain ⟨x{i}, b{i}, h{i}⟩ :=\n" ++
        indent (s!"({field.sufficientProof fieldSource proof}) v{i} p{i}") ++ "\n"
      enough := enough ++ s!"have enough{i} : b{i} ≤ fuel := by omega\n"
    payload := payload ++ "  ·\n" ++ indent (indent (payloadBranch name index c)) ++ "\n"
    let decoder ← RepresentationConstructors.declaration s!"{name}.decode{index}" {
      notations := constructors.map fun c => Mixfix.to_mixop c.source.nottyp.it
      selected := index
      arguments := raw
      decoder := s!"{qualified}.ofValue (fuel + 1) v"
      outcome := decodedFields qualified ctor c.fields
      unfolding := [s!"{qualified}.ofValue"]
      children := c.fields.zipIdx.map fun ((_, field), i) => s!"({field.decoder}) fuel v{i}" }
    decoders := decoders ++ decoder
    let encodedFields := fieldEncodings.foldr (fun head tail => s!"{head} ({tail})") ".nil"
    let encode := s!"dsimp only [{qualified}.{admitted}] at hx\n" ++
      (if c.fields.isEmpty then "" else
        "obtain " ++ tupleText (admitNames ++ ["_"]) ++ " := hx\n") ++
      s!"apply Representation.Source.ConstructorDomain.valid {id} [] [] " ++
      s!"{name}.sourceCases ({sourceTerm c.source}) {fieldTypes} _ (by rfl)\n" ++
      indent (s!"(by simp [{name}.sourceCases])\n" ++
        "(by\n" ++ indent (
          "refine ⟨rfl, ?_⟩\n" ++
          "dsimp [Q.tc, Q.nt, Q.t, Lang.Il.typcase.nottyp, P4SpecTec.Util.Source.mkPhrase]\n" ++
          reduceArguments ++ "exact " ++ consProof identities) ++ ")") ++ "\n" ++
      s!"refine ⟨{rendered}, rfl, rfl, ?_⟩\n" ++ reduceArguments ++ "exact " ++ encodedFields
    encoding := encoding ++ "  | " ++ " ".intercalate (ctor :: xs) ++ " =>\n" ++
      indent (indent encode) ++ "\n"
    let decodeCall := " ".intercalate (s!"{name}.decode{index}" :: "fuel" :: "v" :: "tree" ::
      raw ++ ["shape", "(Representation.Source.mixopTrans tree _ _ matching rfl)", "hargs"])
    let canonical := (indexNames "canonical" count).foldr (fun h tail =>
      s!"congr (congrArg List.cons ({h})) ({tail})") "rfl"
    let finalSound :=
      (if c.fields.isEmpty then "" else "simp only [" ++
        ", ".intercalate (indexNames "d" count) ++ "] at decoded\n") ++
      "have same := Option.some.inj decoded\nsubst x\n" ++ faithful ++
      "refine ⟨" ++ (if c.fields.isEmpty then "trivial" else
        tupleText (admitNames ++ ["trivial"])) ++ ", ?_⟩\n" ++
      s!"change Rel v ({qualified}.toValue {typed})\n" ++
      s!"apply Representation.Source.caseRelation (rendered := {rendered}) shape rfl\n" ++
      "· exact Representation.Source.mixopTrans tree _ _ matching rfl\n" ++
      "· rw [hargs]\n" ++ indent (reduceArguments ++ "all_goals\n" ++
        indent ("dsimp only [canons]\nexact " ++ canonical))
    let soundBody := s!"rw [{decodeCall}] at decoded\n" ++
      (if c.fields.isEmpty then finalSound else decoderUnwrap c.fields 0 finalSound)
    sound := sound ++ "·\n" ++ indent (branchInputs c soundBody) ++ "\n"
    let bound := (indexNames "b" count).foldr (fun head tail => s!"max {head} ({tail})") "0"
    let enoughBody := enough ++ s!"change {qualified}.ofValue (fuel + 1) v = _\n" ++
      s!"rw [{decodeCall}]\n" ++
      (if c.fields.isEmpty then "all_goals rfl" else "rw [" ++ ", ".intercalate (
        (List.range count).map fun i => s!"h{i} fuel enough{i}") ++ "]\nall_goals rfl")
    let sufficientBody := stable ++ s!"refine ⟨{typed}, ({bound}) + 1, ?_⟩\n" ++
      "intro fuel large\ncases fuel with\n| zero => omega\n| succ fuel =>\n" ++ indent enoughBody
    sufficient := sufficient ++ "·\n" ++
      indent (branchInputs c sufficientBody) ++ "\n"
  let splitCases := "rcases member with " ++
    String.intercalate " | " (constructors.map fun _ => "rfl") ++ "\n"
  let membership := s!"simp only [{name}.sourceCases, List.mem_cons, " ++
    "List.not_mem_nil, or_false] at member\n" ++ splitCases
  let text := s!"private def {name}.sourceCases : List Lang.Il.typcase := {cases}\n\n" ++
    "/-- The complete independent grammar of the actual quoted variant. -/\n" ++
    s!"def {name}.{source} (v : Lang.Il.value) : Prop :=\n" ++
    s!"  Representation.Source.Valid {env.lib}.spec {env.domainTerm} " ++
    s!"(Q.varT {sourceId} []) v\n\n" ++
    "/-- Every constructor inherits exactly its positional fields' admission. -/\n" ++
    s!"def {name}.{admitted} : {qualified} → Prop\n" ++ admissions ++ "\n" ++ fieldProofs ++
    s!"private theorem {name}.sourceCasesValid (v : Lang.Il.value) (hv : {name}.{source} v) :\n" ++
    s!"    ∃ c ∈ {name}.sourceCases, Representation.Source.ConstructorDomain " ++
    s!"{env.lib}.spec {env.domainTerm} c " ++
    "(Domain.Mixfix.args c.nottyp.it) v := by\n" ++
    "  obtain ⟨c, member, fields, sub, tree, shape, matching, valid⟩ :=\n" ++
    s!"    hv.variantPayload {id} [] [] {name}.sourceCases v (by rfl)\n" ++
    "  refine ⟨c, member, tree, shape, matching, ?_⟩\n  apply valid.domains\n" ++
    indent membership ++ "\n" ++ payload ++
    s!"\n#audit_axioms {qualified}.sourceCasesValid\n\n" ++
    decoders ++ "/-- The full codec fixes the actual named encoder " ++
    "and decoder dictionaries. -/\n" ++
    s!"theorem {name}.{codec} : " ++ (← codecType env d known).pretty 1000000 ++ " := by\n" ++
    s!"  letI : ToValue {qualified} := ⟨{qualified}.toValue⟩\n" ++
    s!"  letI : OfValue {qualified} := ⟨{qualified}.ofValue⟩\n" ++
    "  refine { encodingValid := ?_, decoder := { sound := ?_, sufficient := ?_ } }\n" ++
    "  · intro x hx\n    cases x with\n" ++ indent encoding ++ "\n" ++
    "  · intro fuel v x hv decoded\n" ++
    s!"    change {qualified}.ofValue fuel v = some x at decoded\n" ++
    "    cases fuel with\n    | zero => cases decoded\n    | succ fuel =>\n" ++
    indent (indent (indent (
      s!"obtain ⟨c, member, tree, shape, matching, valid⟩ := {name}.sourceCasesValid v hv\n" ++
      membership ++ sound))) ++ "\n" ++
    "  · intro v hv\n" ++ indent (indent (
      s!"obtain ⟨c, member, tree, shape, matching, valid⟩ := {name}.sourceCasesValid v hv\n" ++
      membership ++ sufficient)) ++ s!"\n#audit_axioms {qualified}.{codec}\n"
  return Format.text (boundedLines (text.replace "Mixfix." "Domain.Mixfix." |>.replace
    "Domain.Domain.Mixfix." "Domain.Mixfix."))

end P4SpecTec.Codegen.RepresentationMixedVariants
