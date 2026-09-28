import P4SpecTec.Codegen.Certificates.RepresentationRecursiveAdmission
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveEncoding
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveIteration
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveProof

/-!
Complete source codec bundles for actual recursive declaration groups. The bundle
shares only a finite source-derived dispatcher and proof induction; every public
member codec binds its exact generated dictionaries and actual quoted source name.
-/

namespace P4SpecTec.Codegen.RepresentationRecursive

open P4SpecTec.Lang.Il P4SpecTec.Codegen.Types

/-- The independent actual source domain of one monomorphic recursive member. -/
def memberSource (env : Env) (name : String) : String :=
  s!"Representation.Source.Valid {env.lib}.spec {env.domainTerm} " ++
    "(Q.varT " ++ (Reify.str name).fmt.pretty 1000000 ++ " [])"

/-- Exact public codec claim for a recursive member, using its own named dictionaries. -/
def memberCodecType (env : Env) (name : String) (admissionName : String := "") : Std.Format :=
  let qualified := env.q (Names.typeName name)
  let predicate := if admissionName.isEmpty then qualified ++ "." ++ env.part "admitted"
    else admissionName
  Std.Format.text (boundedLines (
    s!"@Representation.Codec {qualified} ⟨{qualified}.toValue⟩ ⟨{qualified}.ofValue⟩\n" ++
    "    (" ++ memberSource env name ++ ") " ++ predicate))

/-- Public admission and codec wrappers, one for every actual source declaration in the group.
The enclosing emitter supplies the library namespace; internal helper names stay local. -/
def memberDeclarations (env : Env) (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut declarations := []
  for (name, index) in plan.roots do
    let some family := plan.families[index]? | throw "recursive member family is absent"
    if family.leaf.isSome then throw "recursive member cannot be an independently supplied leaf"
    let .VarT identifier [] := family.source.it
      | throw "public recursive member codec needs a monomorphic source name"
    if identifier.it != name then throw "recursive member source name differs from its root"
    let localName := Names.typeName name
    let qualified := env.q localName
    let admitted := localName ++ "." ++ env.part "admitted"
    let codec := localName ++ "." ++ env.part "codec"
    let admission := (if env.runtimeProfile then
        "/-- Recursive admission, including the runtime-only raw-extern alternatives. -/\n"
      else "/-- Recursive admission excludes runtime-only constructors. -/\n") ++
      s!"def {admitted} (x : {qualified}) : Prop :=\n" ++
      s!"  {namespaceName}.admitted .f{index} x"
    let proof := (if env.runtimeProfile then
        "/-- Exact recursive codec for the complete runtime-profile grammar. -/\n"
      else "/-- Exact recursive codec for the complete quoted source grammar. -/\n") ++
      s!"theorem {codec} : " ++
      (memberCodecType env name admitted).pretty 1000000 ++ " := by\n" ++
      s!"  letI : ToValue {qualified} := ⟨{qualified}.toValue⟩\n" ++
      s!"  letI : OfValue {qualified} := ⟨{qualified}.ofValue⟩\n" ++
      "  constructor\n  · intro x accepted\n" ++
      s!"    exact {namespaceName}.encodingValid .f{index} x accepted\n" ++
      s!"  · exact {namespaceName}.decoderCorrect .f{index}\n\n" ++
      s!"#audit_axioms {codec}"
    declarations := declarations ++ [admission, proof]
  pure (Std.Format.text (boundedLines ("\n\n".intercalate declarations)))

private def qualifyIdentifier (token : String) : String :=
  let head := (token.splitOn ".").head!
  let qualification := if ["value", "value'", "typ", "typ'", "id", "tparam", "typcase",
      "typfield", "valuefield", "deftyp", "deftyp'"].contains head then
      "P4SpecTec.Lang.Il."
    else if ["Mixfix", "Atom"].contains head then "P4SpecTec.Domain." else ""
  qualification ++ token

-- Only identifier tokens are qualified. Quoted source strings and qualified native names
-- retain their bytes; strings can contain escaped quotes and arbitrary source identifiers.
private partial def qualifyTokens (remaining : List Char) (output : List Char := []) : String :=
  match remaining with
  | [] => String.ofList output.reverse
  | '"' :: rest => stringContents rest ('"' :: output)
  | '«' :: rest => quotedIdentifier rest ('«' :: output)
  | '-' :: '-' :: rest => lineComment rest ('-' :: '-' :: output)
  | '/' :: '-' :: rest => blockComment 1 rest ('-' :: '/' :: output)
  | c :: rest =>
    if c.isAlphanum || c == '_' || c == '.' || c == '\'' then
      let (token, tail) := (c :: rest).span fun ch =>
        ch.isAlphanum || ch == '_' || ch == '.' || ch == '\''
      qualifyTokens tail ((qualifyIdentifier (String.ofList token)).toList.reverse ++ output)
    else qualifyTokens rest (c :: output)
where
  stringContents (remaining output : List Char) : String :=
    match remaining with
    | [] => String.ofList output.reverse
    | '\\' :: c :: rest => stringContents rest (c :: '\\' :: output)
    | '"' :: rest => qualifyTokens rest ('"' :: output)
    | c :: rest => stringContents rest (c :: output)
  quotedIdentifier (remaining output : List Char) : String :=
    match remaining with
    | [] => String.ofList output.reverse
    | '»' :: rest => qualifyTokens rest ('»' :: output)
    | c :: rest => quotedIdentifier rest (c :: output)
  lineComment (remaining output : List Char) : String :=
    match remaining with
    | [] => String.ofList output.reverse
    | '\n' :: rest => qualifyTokens rest ('\n' :: output)
    | c :: rest => lineComment rest (c :: output)
  blockComment (depth : Nat) (remaining output : List Char) : String :=
    match remaining with
    | [] => String.ofList output.reverse
    | '/' :: '-' :: rest => blockComment (depth + 1) rest ('-' :: '/' :: output)
    | '-' :: '/' :: rest =>
      if depth == 1 then qualifyTokens rest ('/' :: '-' :: output)
      else blockComment (depth - 1) rest ('/' :: '-' :: output)
    | c :: rest => blockComment depth rest (c :: output)

#guard qualifyTokens "value NanoP4Spec.value typ Mixfix.t Atom.eq".toList ==
  "P4SpecTec.Lang.Il.value NanoP4Spec.value P4SpecTec.Lang.Il.typ " ++
    "P4SpecTec.Domain.Mixfix.t P4SpecTec.Domain.Atom.eq"
#guard qualifyTokens "\"value\\\"typ\" «value» /- typ /- value -/ -/ value".toList ==
  "\"value\\\"typ\" «value» /- typ /- value -/ -/ P4SpecTec.Lang.Il.value"
#guard qualifyTokens "-- value\nvalue'".toList == "-- value\nP4SpecTec.Lang.Il.value'"

private def qualifyRawTypes (declaration : Std.Format) : Std.Format :=
  Std.Format.text (boundedLines (qualifyTokens (declaration.pretty 1000000).toList))

/-- Assemble a complete checked recursive bundle in source and proof dependency order.
Complete commands preserve the mutual admission block and exact per-member claim boundaries. -/
def declarations (env : Env) (plan : Plan) (namespaceName : String) :
    Except String (List Std.Format) := do
  let beforeAdmission ← [familyDeclarations plan namespaceName,
    fieldMatchingDeclarations plan namespaceName, leafDomainDeclarations plan namespaceName,
    fieldInstantiationDeclarations plan namespaceName,
    constructorDeclarations env plan namespaceName]
      |>.mapM id
  let admission ← admissionDeclarations env plan namespaceName
  let afterAdmission ← [soundConstructorDeclarations env plan namespaceName,
    iterationDeclarations env plan namespaceName,
    aliasCompositionDeclarations env plan namespaceName,
    variantSourceDeclarations env plan namespaceName,
    leafCorrectDeclarations env plan namespaceName, aliasSourceDeclarations env plan namespaceName,
    sourceFidelityDeclarations env plan namespaceName,
    variantSourceDeclarations env plan namespaceName true,
    leafCorrectDeclarations env plan namespaceName true,
    aliasSourceDeclarations env plan namespaceName true,
    sourceFidelityDeclarations env plan namespaceName true,
    variantEncodingDeclarations env plan namespaceName,
    compositionEncodingDeclarations env plan namespaceName,
    encodingDeclarations env plan namespaceName] |>.mapM id
  pure (((beforeAdmission ++ admission ++ afterAdmission ++
    [decoderDeclarations env namespaceName]).map qualifyRawTypes) ++
    [← memberDeclarations env plan namespaceName])

end P4SpecTec.Codegen.RepresentationRecursive
