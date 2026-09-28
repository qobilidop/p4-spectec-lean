import P4SpecTec.Codegen.Certificates.RepresentationField

/-!
Source representation certificates for acyclic monomorphic records. Ordered source
labels and positional field domains come from the actual quoted declaration; field
contracts fix each generated dictionary and preserve source/runtime admission.
-/

namespace P4SpecTec.Codegen.RepresentationRecords

open Std (Format)
open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Codegen.Types
open RepresentationFields

private partial def reaches (env : Env) (target : String) (seen : List String)
    (name : String) : Bool :=
  if name == target then true
  else if seen.contains name then false
  else match env.types[name]? with
    | some { deftyp := some body, .. } =>
      (Env.deftypRefs body).any (reaches env target (name :: seen))
    | _ => false

/-- Validate the complete record shape and every previously proved field codec. -/
def checkSupport (env : Env) (known : String → Option NominalContract) (d : Lang.Al.def) :
    Except String (List (typfield × Contract)) := do
  let .TypD name [] definition _ := d.it
    | throw "source record codec needs a monomorphic type declaration"
  let .StructT fields := definition.it | throw "source record codec needs a record body"
  if fields.isEmpty then throw "source empty record codec is not implemented"
  if (fields.map fun (label, _) => Names.fieldName label.it).eraseDups.length != fields.length then
    throw "source record has duplicate generated field names"
  let mut result := []
  for field@(label, t) in fields do
    let .Keyword _ := label.it
      | throw "source record label needs the generated encoder's keyword shape"
    if (Env.typeRefs t.it).any (reaches env name.it []) then
      throw "source recursive record codec needs SCC composition"
    let contract ← RepresentationFields.resolve env known t
    let _ ← normalizeSubstitution t
    let _ ← identitySubstitution t
    result := result ++ [(field, contract)]
  pure result

/-- Proof-support imports needed by an emitted record certificate. -/
def supportImports : List String :=
  ["P4SpecTec.Refine.Representation.SourceCodec",
   "P4SpecTec.Refine.Representation.SourceRecord",
   "P4SpecTec.Refine.Representation.SourceVariant", "P4SpecTec.Tactic.Audit"]

/-- The exact actual record codec obligation, with named dictionaries and field admission. -/
def codecType (env : Env) (known : String → Option NominalContract) (d : Lang.Al.def) :
    Except String Format := do
  let _ ← checkSupport env known d
  let name := env.q (Names.typeName d.it.id.it)
  pure (Format.text s!"@Refine.Representation.Codec {name} ⟨{name}.toValue⟩ " ++
    Format.text s!"⟨{name}.ofValue⟩ {name}.{env.part "source"} {name}.{env.part "admitted"}")

private def indent (text : String) : String := "  " ++ text.replace "\n" "\n  "

private def listText (terms : List String) : String := "[" ++ ", ".intercalate terms ++ "]"

private def tupleText (terms : List String) : String := "⟨" ++ ", ".intercalate terms ++ "⟩"

private def consProof (terms : List String) : String :=
  terms.foldr (fun term tail => s!".cons ({term}) ({tail})") ".nil"

private def indexNames (namePrefix : String) (count : Nat) : List String :=
  (List.range count).map fun index => namePrefix ++ toString index

private def fieldCodecName (name : String) (index : Nat) : String :=
  s!"{name}.fieldCodec{index}"

private def labelsUnwrap (index count : Nat) (sound : Bool) (body : String) : String :=
  match count with
  | 0 => "cases tail\n" ++ body
  | count + 1 =>
    let labels := if index == 0 then "labels" else "tail"
    let label := (if sound then "label" else "_label") ++ toString index
    s!"cases {labels} with\n| @cons _ f{index} _ _fs {label} tail =>\n" ++
      indent (labelsUnwrap (index + 1) count sound body)

private def valuesUnwrap (index count : Nat) (body : String) : String :=
  match count with
  | 0 => "cases tail\n" ++ body
  | count + 1 =>
    let values := if index == 0 then "valid" else "tail"
    s!"cases {values} with\n| cons _ _ _ _ p{index} tail =>\n" ++
      indent (valuesUnwrap (index + 1) count body)

private def unwrap (name : String) (count : Nat) (sound : Bool) (body : String) : String :=
  let pairs := String.join ((List.range count).map fun index =>
    s!"rcases f{index} with ⟨a{index}, v{index}⟩\n")
  "obtain ⟨fields, shape, labels, valid⟩ := " ++ name ++ ".payload v hv\n" ++
    s!"dsimp only [{name}.sourceFields] at labels\n" ++
    labelsUnwrap 0 count sound (pairs ++
      s!"dsimp only [{name}.sourceTypes, List.map] at valid\n" ++
      valuesUnwrap 0 count body)

private def substitutionUnwrap (index count : Nat) (body : String) : String :=
  match count with
  | 0 => "cases tail\n" ++ body
  | count + 1 =>
    let substitutions := if index == 0 then "subs" else "tail"
    s!"cases {substitutions} with\n| cons sub{index} tail =>\n" ++
      indent (substitutionUnwrap (index + 1) count body)

private def decoderUnwrap (fields : List (typfield × Contract)) (index : Nat)
    (body : String) : String :=
  match fields with
  | [] => body
  | (_, contract) :: fields =>
    let prior := indexNames "d" (index + 1)
    s!"cases d{index} : ({contract.decoder}) fuel v{index} with\n" ++
      "| none => simp [" ++ ", ".intercalate prior ++ "] at decoded\n" ++
      s!"| some x{index} =>\n" ++ indent (decoderUnwrap fields (index + 1) body)

/-- Emit a full source record codec from the quoted ordered fields and checked dependencies. -/
def declarations (env : Env) (known : String → Option NominalContract) (d : Lang.Al.def) :
    Except String Format := do
  let fields ← checkSupport env known d
  let name := Names.typeName d.it.id.it
  let qualified := env.q name
  let source := env.part "source"
  let admitted := env.part "admitted"
  let codec := env.part "codec"
  let encodingSourceIff := env.part "encodingSourceIff"
  let domainTerm := env.domainTerm
  let count := fields.length
  let sourceFields := listText (fields.map fun ((label, t), _) =>
    "(" ++ (Reify.atom label).fmt.pretty ++ ", " ++ (Reify.typ t).fmt.pretty ++ ")")
  let sourceTypes := listText (fields.map fun ((_, t), _) => (Reify.typ t).fmt.pretty)
  let id := "(Q.i " ++ (Reify.str d.it.id.it).fmt.pretty ++ ")"
  let sourceType := "(Q.varT " ++ (Reify.str d.it.id.it).fmt.pretty ++ " [])"
  let xs := indexNames "x" count
  let as := indexNames "admitted" count
  let constructor := tupleText xs
  let admission := " ∧ ".intercalate ((fields.zipIdx.map fun (((label, _), c), _) =>
    "(" ++ c.admitted ++ ") (x." ++ Names.fieldName label.it ++ ")") ++ ["True"])
  let mut fieldProofs := ""
  let mut normalized := []
  let mut identities := []
  let mut encodings := []
  let mut sufficient := ""
  let mut faithful := ""
  let mut related := []
  for (((label, t), contract), index) in fields.zipIdx do
    let fieldCodec := fieldCodecName name index
    let domain := RepresentationFields.source env t
    fieldProofs := fieldProofs ++
      "/-- The field's independent source grammar and exact dictionaries. -/\n" ++
      s!"private theorem {fieldCodecName name index} : {contract.type domain} :=\n" ++
      indent contract.codec ++ s!"\n\n#audit_axioms {fieldCodec}\n\n"
    let sourceType := "(" ++ (Reify.typ t).fmt.pretty ++ ").it"
    let normalizeName := s!"{name}.fieldSubstitution{index}"
    fieldProofs := fieldProofs ++
      "/-- Empty substitution preserves the complete independent field domain. -/\n" ++
      s!"private theorem {normalizeName} : ∀ actual,\n" ++
      s!"    Representation.Source.Substitutes [] {sourceType} actual → ∀ v,\n" ++
      s!"    Representation.Source.Valid {env.lib}.spec " ++
      s!"{domainTerm} actual v →\n" ++
      s!"    ({domain}) v :=\n" ++ indent (← normalizeSubstitution t) ++
      s!"\n\n#audit_axioms {normalizeName}\n\n"
    normalized := normalized ++ [s!"{normalizeName} _ sub{index}"]
    identities := identities ++ [← identitySubstitution t]
    encodings := encodings ++ [s!".cons _ _ _ _ (({contract.encodingProof domain fieldCodec}) " ++
      s!"x{index} admitted{index})"]
    sufficient := sufficient ++ s!"obtain ⟨x{index}, b{index}, h{index}⟩ :=\n" ++
      indent (s!"({contract.sufficientProof domain fieldCodec}) v{index} p{index}") ++ "\n"
    faithful := faithful ++ s!"obtain ⟨admitted{index}, related{index}⟩ :=\n" ++
      indent (s!"({contract.soundProof domain fieldCodec}) fuel v{index} x{index} " ++
        s!"p{index} d{index}") ++ "\n"
    let atom := (Types.atomTerm label.it).fmt.pretty
    faithful := faithful ++
      s!"have labels{index} : Domain.Atom.eq a{index}.it {atom} = true := by\n" ++
      indent (s!"have same : {atom} = a{index}.it := by\n" ++
        indent ("simpa [Domain.Atom.eq, P4SpecTec.Refine.Atom.compare_eq_iff] " ++
          s!"using label{index}") ++ "\n" ++
        "simp [same, Domain.Atom.eq, P4SpecTec.Refine.Atom.compare_eq_iff]") ++ "\n"
    related := related ++ [s!"⟨labels{index}, related{index}⟩"]
  let encodingPayload := encodings.foldr (fun head tail => s!"{head} ({tail})") ".nil"
  let labels := consProof (List.replicate count "rfl")
  let encoding := s!"rcases x with {constructor}\n" ++
    s!"dsimp only [{qualified}.{admitted}] at hx\n" ++
    "obtain " ++ tupleText (as ++ ["_"]) ++ " := hx\n" ++
    s!"apply Representation.Source.RecordDomain.valid {id} [] [] " ++
    s!"{qualified}.sourceFields {qualified}.sourceTypes ({qualified}.toValue {constructor}) " ++
    "(by rfl)\n" ++ indent ("⟨rfl, " ++ consProof identities ++ "⟩") ++ "\n" ++
    s!"exact ⟨_, rfl, {labels}, {encodingPayload}⟩"
  let bound := (indexNames "b" count).foldr (fun head tail => s!"max {head} ({tail})") "0"
  let decodedFields := fields.zipIdx.foldr (fun ((_, c), index) tail =>
    s!"(({c.decoder}) fuel v{index}).bind (fun x{index} => {tail})")
    s!"some ({constructor} : {qualified})"
  let enough := String.join ((List.range count).map fun index =>
    s!"have enough{index} : b{index} ≤ fuel := by omega\n")
  sufficient := sufficient ++ s!"refine ⟨{constructor}, ({bound}) + 1, ?_⟩\n" ++
    "intro fuel enough\ncases fuel with\n| zero => omega\n| succ fuel =>\n" ++
    indent (enough ++ s!"change {qualified}.ofValue (fuel + 1) v = _\n" ++
      s!"simp only [{qualified}.ofValue, shape]\n" ++
      s!"change {decodedFields} = some {constructor}\n" ++
      "rw [" ++ ", ".intercalate ((List.range count).map fun index =>
        s!"h{index} fuel enough{index}") ++ "]\nrfl")
  let finalSound := "simp only [" ++ ", ".intercalate (indexNames "d" count) ++
    "] at decoded\nhave same := Option.some.inj decoded\nsubst x\n" ++
    faithful ++ "refine ⟨" ++ tupleText (as ++ ["trivial"]) ++ ", ?_⟩\n" ++
    s!"change Rel v ({qualified}.toValue {constructor})\n" ++
    "apply Representation.Source.recordRelation shape rfl\nexact " ++ consProof related
  let sound := s!"change {qualified}.ofValue fuel v = some x at decoded\n" ++
    "cases fuel with\n" ++ s!"| zero => simp [{qualified}.ofValue] at decoded\n" ++
    "| succ fuel =>\n" ++ indent (
      s!"simp only [{qualified}.ofValue, shape] at decoded\n" ++
      s!"change {decodedFields} = some x at decoded\n" ++
      decoderUnwrap fields 0 finalSound)
  let encodedDomains := " ∧ ".intercalate ((fields.map fun ((label, t), c) =>
    "(" ++ RepresentationFields.source env t ++ ") ((" ++ c.encoder ++ ") (x." ++
      Names.fieldName label.it ++ "))") ++ ["True"])
  let rawFields := listText (fields.zipIdx.map fun (((label, _), c), index) =>
    "(Q.a (" ++ (Types.atomTerm label.it).fmt.pretty ++ "), (" ++ c.encoder ++ s!") x{index})")
  let sourcePayload := (indexNames "p" count).foldr (fun h tail =>
    s!".cons _ _ _ _ {h} ({tail})") ".nil"
  let sourceEncoding :=
    "/-- Validity of the actual encoded record is exactly validity of its encoded fields. -/\n" ++
    s!"theorem {name}.{encodingSourceIff} (x : {qualified}) :\n" ++
    s!"    {qualified}.{source} ({qualified}.toValue x) ↔ {encodedDomains} := by\n" ++
    s!"  rcases x with {constructor}\n  constructor\n  · intro valid\n" ++
    s!"    obtain ⟨fields, shape, _labels, valid⟩ := {qualified}.payload _ valid\n" ++
    s!"    have same : {rawFields} = fields := Lang.Il.value'.StructV.inj shape\n" ++
    "    cases same\n" ++
    s!"    dsimp only [{qualified}.sourceTypes, List.map] at valid\n" ++
    indent (indent (valuesUnwrap 0 count
      ("exact " ++ tupleText (indexNames "p" count ++ ["trivial"])))) ++ "\n" ++
    "  · intro valid\n    obtain " ++ tupleText (indexNames "p" count ++ ["_"]) ++
    " := valid\n" ++
    s!"    apply Representation.Source.RecordDomain.valid {id} [] [] " ++
    s!"{qualified}.sourceFields {qualified}.sourceTypes ({qualified}.toValue {constructor}) " ++
    "(by rfl)\n      ⟨rfl, " ++ consProof identities ++ "⟩\n" ++
    s!"    exact ⟨_, rfl, {labels}, {sourcePayload}⟩\n\n" ++
    s!"#audit_axioms {qualified}.{encodingSourceIff}"
  let text :=
    "/-- Ordered fields from the actual quoted source record. -/\n" ++
    s!"private def {name}.sourceFields : List Lang.Il.typfield := {sourceFields}\n\n" ++
    "/-- Positional source types before the empty monomorphic substitution. -/\n" ++
    s!"private def {name}.sourceTypes : List Lang.Il.typ := {sourceTypes}\n\n" ++
    "/-- The independent record grammar in the actual compiled source specification. -/\n" ++
    s!"def {name}.{source} (v : Lang.Il.value) : Prop :=\n" ++
    s!"  Representation.Source.Valid {env.lib}.spec " ++
    s!"{domainTerm} {sourceType} v\n\n" ++
    "/-- Each generated field obeys its codec's independent source/runtime admission. -/\n" ++
    s!"def {name}.{admitted} (x : {qualified}) : Prop := {admission}\n\n" ++ fieldProofs ++
    "/-- Source derivations expose the declared labels and exact positional field domains. -/\n" ++
    s!"private theorem {name}.payload (v : Lang.Il.value) (hv : {qualified}.{source} v) :\n" ++
    s!"    Representation.Source.RecordDomain {env.lib}.spec " ++
    s!"{domainTerm}\n" ++
    s!"      {qualified}.sourceFields {qualified}.sourceTypes v := by\n" ++ indent (
      "obtain ⟨types, subs, fields, shape, labels, valid⟩ :=\n" ++ indent (
        s!"Representation.Source.Valid.recordPayload {id} [] [] " ++
        s!"{qualified}.sourceFields v (by rfl) hv") ++ "\n" ++
      "have transfers : List.Forall₂ (fun a b : Lang.Il.typ => ∀ w,\n" ++ indent (
        s!"Representation.Source.Valid {env.lib}.spec " ++
        s!"{domainTerm} a.it w →\n" ++
        s!"Representation.Source.Valid {env.lib}.spec " ++
        s!"{domainTerm} b.it w) " ++
        s!"types {qualified}.sourceTypes := by") ++ "\n" ++ indent (
        "have subs := subs.2\n" ++
        s!"dsimp only [{qualified}.sourceFields, List.map] at subs\n" ++
        substitutionUnwrap 0 count ("exact " ++ consProof normalized)) ++ "\n" ++
      "exact ⟨fields, shape, labels, valid.domains transfers⟩") ++
    s!"\n\n#audit_axioms {qualified}.payload\n\n" ++
    "/-- The actual record encoder and decoder satisfy the complete source grammar. -/\n" ++
    s!"theorem {name}.{codec} : " ++ (← codecType env known d).pretty ++ " := by\n" ++
    s!"  letI : ToValue {qualified} := ⟨{qualified}.toValue⟩\n" ++
    s!"  letI : OfValue {qualified} := ⟨{qualified}.ofValue⟩\n" ++
    "  constructor\n" ++ indent (
      "· intro x hx\n" ++ indent encoding ++ "\n" ++
      "· constructor\n" ++ indent (
        "· intro fuel v x hv decoded\n" ++ indent (unwrap qualified count true sound) ++ "\n" ++
        "· intro v hv\n" ++ indent (unwrap qualified count false sufficient))) ++
    s!"\n\n#audit_axioms {qualified}.{codec}"
  pure (Format.text (boundedLines (text ++ "\n\n" ++ sourceEncoding)))

end P4SpecTec.Codegen.RepresentationRecords
