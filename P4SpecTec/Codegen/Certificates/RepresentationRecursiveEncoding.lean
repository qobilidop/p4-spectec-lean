import P4SpecTec.Codegen.Certificates.RepresentationRecursiveSource

/-! Encoding validity follows admitted generated constructors and actual field substitution. -/

namespace P4SpecTec.Codegen.RepresentationRecursive

open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Codegen.Types

private def quoteType (t : typ) : String := "(" ++ (Reify.typ t).fmt.pretty 1000000 ++ ")"

private def quoteCase (c : typcase) : String :=
  let (origin, arguments) := match c.typorigin.it with | .mk origin arguments => (origin, arguments)
  (Term.call "Q.tc" [Reify.mixfix c.nottyp.it Reify.typ,
    Reify.str origin.it, Reify.lst (arguments.map Reify.typ)]).fmt.pretty 1000000

private def idList (parameters : List tparam) : String :=
  (Reify.lst (parameters.map fun p => Term.call "Q.i" [Reify.str p.it])).fmt.pretty 1000000

private def variantBranch (env : Env) (index selected offset : Nat) (family : Family)
    (name : id) (parameters : List tparam) (arguments : List typ) (cases : List typcase)
    (sourceCase : typcase) (constructorName : String) (children : List Nat) : String := Id.run do
  let positions := List.range children.length
  let values := positions.map (fun i => s!"x{i}")
  let typed := "(" ++ env.q (Names.typeName name.it) ++ "." ++ constructorName ++ " " ++
    " ".intercalate values ++ s!" : Carrier .f{index})"
  let childValues := children.zipIdx.map (fun (child, i) => s!"encode .f{child} x{i}")
  let rendered := (mixfixTerm (Mixfix.to_mixop sourceCase.nottyp.it)
    (childValues.map (fun value => Term.atom ("(" ++ value ++ ")")))).fmt.pretty 1000000
  let fields := "[" ++ ", ".intercalate
    (children.map fun child => s!"Q.t (source .f{child})") ++ "]"
  let binders := children.zipIdx.map fun (child, i) => s!" (x{i} : Carrier .f{child})"
  let hypotheses := children.zipIdx.map fun (child, i) =>
    s!"\n    (h{i} : Representation.Source.Valid {env.lib}.spec " ++
    s!"Representation.Source.externDomain (source .f{child}) (encode .f{child} x{i}))"
  let originalCases := "[" ++ ", ".intercalate (cases.map quoteCase) ++ "]"
  let identity := positions.foldr (fun i tail =>
    s!".cons (instantiateField{index}_{offset + i}) ({tail})") ".nil"
  let payload := positions.foldr (fun i tail => s!".cons _ _ _ _ h{i} ({tail})") ".nil"
  let reduce := "repeat' first\n" ++
    "  | simp only [Mixfix.args]\n" ++
    "  | dsimp only [List.flatMap, List.append, List.map, List.flatten]\n"
  let indent := fun text : String => "  " ++ text.trimAsciiEnd.toString.replace "\n" "\n  "
  let theoremName := s!"encodeBranch{index}_{selected}"
  return "/-- Source-valid children encode to the exact declared source constructor. -/\n" ++
    s!"private theorem {theoremName}" ++ String.join binders ++ String.join hypotheses ++
    s!" :\n    Representation.Source.Valid {env.lib}.spec Representation.Source.externDomain\n" ++
    s!"      (source .f{index}) (encode .f{index} {typed}) := by\n" ++
    "  apply Representation.Source.ConstructorDomain.valid (Q.i " ++
    (Reify.str name.it).fmt.pretty 1000000 ++ ") " ++
    (Reify.lst (arguments.map Reify.typ)).fmt.pretty 1000000 ++ " " ++ idList parameters ++ " " ++
    originalCases ++ " (" ++ quoteCase sourceCase ++ ") " ++ fields ++ " _\n" ++
    "    (by rfl) (by simp)\n    (by\n      refine ⟨rfl, ?_⟩\n" ++
    "      dsimp [Q.tc, Q.nt, Q.t, Lang.Il.typcase.nottyp, Util.Source.mkPhrase]\n" ++
    indent (indent (indent (reduce ++ "exact " ++ identity))) ++ ")\n" ++
    s!"  refine ⟨{rendered}, ?_, rfl, ?_⟩\n" ++
    "  · dsimp only [encode]\n    rw [" ++ ", ".intercalate family.encoderUnfolding ++
    "] <;> rfl\n  · " ++ (reduce ++ "exact " ++ payload).replace "\n" "\n    " ++
    s!"\n\n#audit_axioms {theoremName}"

/-- Emit each actual source variant's encoding rule, conditional only on its children. -/
def variantEncodingDeclarations (env : Env) (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut declarations := []
  for (family, index) in plan.families.toList.zipIdx do
    if family.leaf.isSome then continue
    let some declaration := family.declaration | continue
    let .TypD name parameters definition _ := declaration.it
      | throw "recursive encoding requires an actual source type definition"
    let .VariantT cases := definition.it | continue
    let .VarT _ arguments := family.source.it | throw "recursive variant source is not nominal"
    let some (.VariantT actualCases) := family.body
      | throw "recursive instantiated variant changes source declaration shape"
    if cases.length != actualCases.length then throw "recursive variant changes constructor count"
    let mut offset := 0
    for ((sourceCase, constructor), selected) in (cases.zip (ctorNames actualCases)).zipIdx do
      let count := (Mixfix.args sourceCase.nottyp.it).length
      let children := family.children.drop offset |>.take count
      declarations := declarations ++ [variantBranch env index selected offset family name
        parameters arguments cases sourceCase constructor children]
      offset := offset + count
    if offset != family.children.length then throw "recursive encoding source field arity mismatch"
  pure (Std.Format.text (boundedLines (
    s!"namespace {namespaceName}\n\n" ++ "\n\n".intercalate declarations ++
    s!"\n\nend {namespaceName}")))

private def validity (env : Env) (index : Nat) (value : String) : String :=
  s!"Representation.Source.Valid {env.lib}.spec Representation.Source.externDomain " ++
    s!"(source .f{index}) (encode .f{index} ({value}))"

private def iterationEncoding (env : Env) (index child : Nat) (kind : iter) : String :=
  let valid := validity env index
  let childValid := validity env child "x"
  match kind with
  | .List =>
    s!"private theorem encodeList{index} (xs : Carrier .f{index})\n" ++
    s!"    (children : ∀ x ∈ xs, {childValid}) : {valid "xs"} := by\n" ++
    s!"  apply Representation.Source.Valid.list (Q.t (source .f{child})) _ " ++
    s!"(xs.map (encode .f{child})) (listEncoding{index} xs)\n" ++
    "  apply Representation.Source.Values.replicate\n  intro v member\n" ++
    "  obtain ⟨x, belongs, rfl⟩ := List.mem_map.mp member\n" ++
    "  exact children x belongs\n\n" ++ s!"#audit_axioms encodeList{index}"
  | .Opt =>
    s!"private theorem encodeNone{index} : {valid "none"} :=\n" ++
    s!"  .none (Q.t (source .f{child})) _ noneEncoding{index}\n\n" ++
    s!"#audit_axioms encodeNone{index}\n\n" ++
    s!"private theorem encodeSome{index} (x : Carrier .f{child})\n" ++
    s!"    (child : {childValid}) : {valid "some x"} :=\n" ++
    s!"  .some (Q.t (source .f{child})) _ (encode .f{child} x) (someEncoding{index} x) child\n\n" ++
    s!"#audit_axioms encodeSome{index}"

private def aliasEncoding (env : Env) (index child : Nat) (family : Family)
    (name : id) (parameters : List tparam) (arguments : List typ) (definition : typ) : String :=
  s!"private theorem encodeAlias{index} (x : Carrier .f{index})\n" ++
  s!"    (child : {validity env child "x"}) : {validity env index "x"} := by\n" ++
  "  apply Representation.Source.Valid.alias (Q.i " ++ (Reify.str name.it).fmt.pretty 1000000 ++
  ") " ++ (Reify.lst (arguments.map Reify.typ)).fmt.pretty 1000000 ++ " " ++ idList parameters ++
  " " ++ quoteType definition ++ s!" (Q.t (source .f{child})) _ (by rfl)\n" ++
  s!"    ⟨rfl, .cons instantiateField{index}_0 .nil⟩\n" ++
  s!"  have encoding : encode .f{index} x = encode .f{child} x := by\n" ++
  "    dsimp only [encode]\n    rw [" ++ ", ".intercalate family.encoderUnfolding ++
  "] <;> rfl\n  rw [encoding]\n  exact child\n\n" ++
  s!"#audit_axioms encodeAlias{index}"

/-- Emit exact leaf codecs and source encoding rules for recursive aliases and containers. -/
def compositionEncodingDeclarations (env : Env) (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut declarations := []
  for (family, index) in plan.families.toList.zipIdx do
    if let some contract := family.leaf then
      let domain := RepresentationFields.source env family.source
      declarations := declarations ++ [
        s!"private theorem encodeLeaf{index} (x : Carrier .f{index})\n" ++
        s!"    (accepted : admitted .f{index} x) : {validity env index "x"} := by\n" ++
        s!"  exact ({contract.encodingProof domain contract.codec}) x accepted\n\n" ++
        s!"#audit_axioms encodeLeaf{index}"]
    else
      match family.source.it, family.body with
      | .IterT _ kind, _ =>
        let [child] := family.children | throw "iteration encoding needs exactly one child"
        declarations := declarations ++ [iterationEncoding env index child kind]
      | .VarT _ arguments, some (.PlainT _) =>
        let [child] := family.children | throw "alias encoding needs exactly one child"
        let some d := family.declaration | throw "alias encoding source declaration absent"
        let .TypD name parameters definition _ := d.it | throw "alias source is not defined"
        let .PlainT field := definition.it | throw "alias source changes its declared shape"
        declarations := declarations ++ [aliasEncoding env index child family name parameters
          arguments field]
      | _, _ => pure ()
  pure (Std.Format.text (boundedLines (
    s!"namespace {namespaceName}\n\n" ++ "\n\n".intercalate declarations ++
    s!"\n\nend {namespaceName}")))

private def consEncoding (env : Env) (index child : Nat) : String :=
  s!"private theorem encodeCons{index} (x : Carrier .f{child}) (xs : Carrier .f{index})\n" ++
  s!"    (head : {validity env child "x"}) (tail : {validity env index "xs"}) :\n" ++
  s!"    {validity env index "x :: xs"} := by\n" ++
  s!"  apply encodeList{index}\n  intro y member\n" ++
  "  rcases List.mem_cons.mp member with rfl | member\n  · exact head\n" ++
  "  · obtain ⟨raws, shape, valid⟩ :=\n" ++
  s!"      (Representation.Source.listIff (Q.t (source .f{child})) _).mp tail\n" ++
  s!"    rw [listEncoding{index}] at shape\n" ++
  "    cases value'.ListV.inj shape\n" ++
  "    exact valid _ (List.mem_map.mpr ⟨y, member, rfl⟩)\n\n" ++
  s!"#audit_axioms encodeCons{index}"

private def admissionHandler (plan : Plan) (children : List Nat) (values : List String)
    (conclusion : List String → String) : Except String String := do
  let mut hypotheses := []
  let mut inductions := []
  let mut proofs := []
  for ((child, value), position) in (children.zip values).zipIdx do
    let some family := plan.families[child]? | throw "encoding handler child is absent"
    if family.leaf.isSome then
      hypotheses := hypotheses ++ [s!"h{position}"]
      proofs := proofs ++ [s!"(encodeLeaf{child} {value} h{position})"]
    else
      hypotheses := hypotheses ++ [s!"_h{position}"]
      inductions := inductions ++ [s!"ih{position}"]
      proofs := proofs ++ [s!"ih{position}"]
  let binders := values ++ hypotheses ++ inductions
  pure (if binders.isEmpty then conclusion proofs else
    "(fun " ++ " ".intercalate binders ++ " => " ++ conclusion proofs ++ ")")

/-- Assemble checked admitted-carrier induction from actual constructor and leaf encoding rules.
Every nonrecursive leaf is discharged by its exact codec, never by an admission assumption. -/
def encodingDeclarations (env : Env) (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut minors := []
  let mut extras := []
  let recursive := plan.families.toList.zipIdx.filter fun (family, _) => family.leaf.isNone
  for (family, index) in recursive do
    match family.source.it, family.body with
    | .IterT _ .List, _ =>
      let [child] := family.children | throw "list encoding induction needs one element family"
      extras := extras ++ [consEncoding env index child]
      minors := minors ++ [s!"(encodeList{index} [] (by simp))",
        ← admissionHandler plan [child, index] ["x", "xs"] fun proofs =>
          s!"encodeCons{index} x xs " ++ " ".intercalate proofs]
    | .IterT _ .Opt, _ =>
      let [child] := family.children | throw "option encoding induction needs one element family"
      minors := minors ++ [s!"encodeNone{index}",
        ← admissionHandler plan [child] ["x"] fun proofs =>
          s!"encodeSome{index} x " ++ " ".intercalate proofs]
    | .VarT .., some (.PlainT _) =>
      let [child] := family.children | throw "alias encoding induction needs one child family"
      minors := minors ++ [← admissionHandler plan [child] ["x"] fun proofs =>
        s!"encodeAlias{index} x " ++ " ".intercalate proofs]
    | .VarT .., some (.VariantT cases) =>
      let mut offset := 0
      for (sourceCase, selected) in cases.zipIdx do
        let count := (Mixfix.args sourceCase.nottyp.it).length
        let children := family.children.drop offset |>.take count
        let values := (List.range count).map fun position => s!"x{position}"
        minors := minors ++ [← admissionHandler plan children values fun proofs =>
          s!"encodeBranch{index}_{selected} " ++ " ".intercalate (values ++ proofs)]
        offset := offset + count
      if offset != family.children.length then throw "encoding induction constructor arity differs"
    | _, _ => throw "recursive encoding induction does not support this local source shape"
  let motives := recursive.zipIdx.map fun ((_, family), position) =>
    let name := if recursive.length == 1 then "motive" else s!"motive_{position + 1}"
    s!"({name} := fun x _ => {validity env family "x"})"
  let mut branches := []
  for (family, index) in plan.families.toList.zipIdx do
    if family.leaf.isSome then
      branches := branches ++ [s!"  | f{index} => exact encodeLeaf{index} x accepted"]
    else
      branches := branches ++ [s!"  | f{index} =>\n    exact AdmittedF{index}.rec\n      " ++
        "\n      ".intercalate (motives ++ minors ++ ["accepted"])]
  let text := "\n\n".intercalate extras ++ "\n\n" ++
    "/-- Every structurally admitted generated value belongs to its full source grammar. -/\n" ++
    "theorem encodingValid (family : Family) (x : Carrier family)\n" ++
    "    (accepted : admitted family x) :\n" ++
    s!"    Representation.Source.Valid {env.lib}.spec Representation.Source.externDomain\n" ++
    "      (source family) (encode family x) := by\n  cases family with\n" ++
    "\n".intercalate branches ++ "\n\n#audit_axioms encodingValid"
  pure (Std.Format.text (boundedLines (
    s!"namespace {namespaceName}\n\n" ++ text ++ s!"\n\nend {namespaceName}")))

end P4SpecTec.Codegen.RepresentationRecursive
