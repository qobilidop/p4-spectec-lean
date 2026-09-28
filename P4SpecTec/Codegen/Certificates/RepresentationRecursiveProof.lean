import P4SpecTec.Codegen.Certificates.RepresentationRecursiveConstructor
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveSource

/-!
Source-derivation induction templates for finite recursive representation families.
Constructor selection and field membership come from the actual quoted declarations;
child obligations are supplied by the mutual source derivation, never by decoder success.
-/

namespace P4SpecTec.Codegen.RepresentationRecursive

open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Codegen.Types

private def quote (t : typ) : String := "(" ++ (Reify.typ t).fmt.pretty 1000000 ++ ")"

private def sourceBody (parameters : List tparam) (definition : deftyp) : String :=
  "some (" ++ (Reify.lst (parameters.map fun p =>
    Term.call "Q.i" [Reify.str p.it])).fmt.pretty 1000000 ++
  ", " ++ "(" ++ (Reify.deftyp definition).fmt.pretty 1000000 ++ ").it)"

private def matchArguments (arguments : List typ) : List String :=
  (List.range arguments.length).map (fun i => s!"arg{i}")

private def matchingCase (index : Nat) (arguments : List typ) : String :=
  s!"  | f{index} name " ++ " ".intercalate (matchArguments arguments) ++ " nameEq " ++
    " ".intercalate ((List.range arguments.length).map (fun i => s!"harg{i}")) ++ " =>\n"

private def matchingValue (index : Nat) (arguments : List typ) : String :=
  s!"(.f{index} name " ++ " ".intercalate (matchArguments arguments) ++ " nameEq " ++
    " ".intercalate ((List.range arguments.length).map (fun i => s!"harg{i}")) ++ ")"

private def selectedVariant (env : Env) (index selected offset : Nat) (arguments : List typ)
    (sourceCase : typcase) (children : List Nat) (sufficient : Bool)
    (sourceName constructorName : String) : String := Id.run do
  let pattern := sourceCase.nottyp.it
  let fields := Mixfix.args pattern
  let typed := (Reify.mixfix pattern Reify.typ).fmt.pretty 1000000
  let unit := (mixopTerm (Mixfix.to_mixop pattern)).fmt.pretty 1000000
  let args := (Reify.lst (fields.map Reify.typ)).fmt.pretty 1000000
  let rules := argumentRules pattern
  let mut text := s!"have originalArgs : Mixfix.args (({typed}) : Mixfix.t typ) = {args} := by\n" ++
    s!"  simp only [{rules}] <;> rfl\n" ++
    "obtain ⟨_arity, substitutions⟩ := fields\n" ++
    "dsimp only [Q.tc, typcase.nottyp, Q.nt, Util.Source.mkPhrase] at substitutions\n" ++
    "rw [originalArgs] at substitutions\n"
  let mut indent := ""
  let mut tail := "substitutions"
  for position in List.range fields.length do
    text := text ++ indent ++ s!"cases {tail} with\n" ++ indent ++
      s!"| cons sub{position} rest{position} =>\n"
    indent := indent ++ "  "
    tail := s!"rest{position}"
  text := text ++ indent ++ s!"cases {tail}\n" ++ indent ++
    "generalize argsShape : Mixfix.args tree = raws at ih\n"
  tail := "ih"
  for position in List.range fields.length do
    text := text ++ indent ++ s!"cases {tail} with\n" ++ indent ++
      s!"| @cons t{position} a{position} ts{position} raws{position} ih{position} " ++
      s!"tail{position} =>\n"
    indent := indent ++ "  "
    tail := s!"tail{position}"
  text := text ++ indent ++ s!"cases {tail}\n" ++ indent ++
    s!"have matching : Mixfix.eq_mixop tree (({unit}) : Mixfix.mixop) = true :=\n" ++
    indent ++ "  Representation.Source.mixopTrans tree _ _ mixopMatches (by rfl)\n" ++
    indent
  if !sufficient then
    text := text ++ s!"exact soundBranch{index}_{selected} v tree " ++
      " ".intercalate ((List.range fields.length).map (fun i => s!"a{i}")) ++
      " shape matching argsShape"
  for (child, position) in children.zipIdx do
    let matched := s!"(matchField{index}_{offset + position} " ++
      " ".intercalate (matchArguments arguments) ++ " " ++
      " ".intercalate ((List.range arguments.length).map (fun i => s!"harg{i}")) ++
      s!" _ sub{position})"
    if sufficient then
      text := text ++ s!"obtain ⟨x{position}, d{position}⟩ := ih{position} .f{child} {matched}\n" ++
        indent
    else text := text ++ s!" (ih{position} .f{child} {matched})"
  if sufficient then
    let value := "(" ++ env.q (Names.typeName sourceName) ++ "." ++ constructorName ++ " " ++
      " ".intercalate ((List.range fields.length).map (fun i => s!"x{i}")) ++ ")"
    text := text ++ s!"exact ⟨({value} : Carrier .f{index}), " ++
      s!"decodeBranch{index}_{selected} v tree " ++
      " ".intercalate ((List.range fields.length).map (fun i => s!"a{i}")) ++ " " ++
      " ".intercalate ((List.range fields.length).map (fun i => s!"x{i}")) ++
      " shape matching argsShape " ++
      " ".intercalate ((List.range fields.length).map (fun i => s!"d{i}")) ++ "⟩"
  return text ++ "\n"

/-- Emit variant source induction, parameterized only by checked nonrecursive leaf correctness.
The leaf premise is explicit staging machinery and must be discharged by exact leaf codecs. -/
def variantSourceDeclarations (env : Env) (plan : Plan) (namespaceName : String)
    (sufficient : Bool := false) : Except String Std.Format := do
  let goal := if sufficient then "Witness" else "Faithful"
  let leafName := if sufficient then "leafWitness" else "leafCorrect"
  let theoremName := if sufficient then "variantSourceWitness" else "variantSourceFaithful"
  let leafCases := plan.families.toList.zipIdx.map fun (family, index) =>
    s!"  | .f{index} => {if family.leaf.isSome then "true" else "false"}"
  let spec := env.lib ++ ".spec"
  let domain := "Representation.Source.externDomain"
  let faithful := "/-- Actual decoder fidelity with independently structural admission. -/\n" ++
    s!"def {goal} (input : typ') (v : value) : Prop :=\n" ++
    "  ∀ family, Matches input family → " ++
    (if sufficient then "∃ x, Representation.Decodes (decode family) v x" else
      "∀ fuel x, decode family fuel v = some x →\n" ++
      "    admitted family x ∧ Rel v (encode family x)")
  let leaf := "/-- Independently checked leaf contracts in this finite closure. -/\n" ++
    "def isLeaf : Family → Bool\n" ++ "\n".intercalate leafCases
  let mut proof := "  intro family matching\n  cases matching with\n"
  for (family, index) in plan.families.toList.zipIdx do
    let .VarT sourceName arguments := family.source.it | continue
    proof := proof ++ matchingCase index arguments
    if family.leaf.isSome then
      proof := proof ++ s!"    exact {leafName} _ v .f{index} rfl " ++
        matchingValue index arguments ++ " whole\n"
      continue
    let some declaration := family.declaration | throw "local recursive nominal lacks declaration"
    let .TypD _ parameters definition _ := declaration.it
      | throw "recursive variant induction requires a defined type"
    proof := proof ++ s!"    have actual : Representation.Source.body {spec} name.it =\n" ++
      "        " ++ sourceBody parameters definition ++ " := by\n      rw [nameEq]; rfl\n"
    match definition.it with
    | .VariantT cases =>
      proof := proof ++ "    cases Option.some.inj (declared.symm.trans actual)\n" ++
        "    change constructor ∈ " ++ (Reify.lst (cases.map fun c =>
          let (origin, targs) := match c.typorigin.it with | .mk o args => (o, args)
          Term.call "Q.tc" [Reify.mixfix c.nottyp.it Reify.typ, Reify.str origin.it,
            Reify.lst (targs.map Reify.typ)])).fmt.pretty 1000000 ++ " at member\n" ++
        "    simp only [List.mem_cons, List.not_mem_nil, or_false] at member\n" ++
        "    rcases member with " ++ " | ".intercalate (List.replicate cases.length "rfl") ++ "\n"
      let mut offset := 0
      for (sourceCase, selected) in cases.zipIdx do
        let count := (Mixfix.args sourceCase.nottyp.it).length
        let body := selectedVariant env index selected offset arguments sourceCase
          (family.children.drop offset |>.take count) sufficient sourceName.it
          ((ctorNames cases)[selected]!)
        proof := proof ++ "    · " ++ (body.trimAscii.toString.replace "\n" "\n      ")
        proof := proof ++ "\n"
        offset := offset + count
      if offset != family.children.length then throw "recursive variant child arity mismatch"
    | _ => proof := proof ++
        "    simp only [actual, Option.some.injEq, Prod.mk.injEq] at declared\n" ++
        "    obtain ⟨_, impossible⟩ := declared\n    cases impossible\n"
  let proofDeclaration := "/-- Source constructors supply recursive child codec facts. -/\n" ++
    s!"private theorem {theoremName}\n" ++
    s!"    ({leafName} : ∀ input v family, isLeaf family = true → Matches input family →\n" ++
    s!"      Representation.Source.Valid {spec} {domain} input v →\n" ++
    (if sufficient then "      ∃ x, Representation.Decodes (decode family) v x)\n" else
      "      ∀ fuel x, decode family fuel v = some x →\n" ++
      "        admitted family x ∧ Rel v (encode family x))\n") ++
    "    (name : id) (arguments : List typ) (parameters : List tparam)\n" ++
    "    (cases : List typcase) (constructor : typcase) (instantiated : List typ)\n" ++
    "    (v : value) (tree : Mixfix.t value)\n" ++
    s!"    (declared : Representation.Source.body {spec} name.it =\n" ++
    "      some (parameters, .VariantT cases)) (member : constructor ∈ cases)\n" ++
    "    (shape : v.it = .CaseV tree)\n" ++
    "    (mixopMatches : Mixfix.eq_mixop tree constructor.nottyp.it = true)\n" ++
    "    (fields : Representation.Source.instantiatedFields parameters arguments\n" ++
    "      (Mixfix.args constructor.nottyp.it) instantiated)\n" ++
    s!"    (ih : List.Forall₂ (fun type v => {goal} type.it v)\n" ++
    "      instantiated (Mixfix.args tree))\n" ++
    s!"    (whole : Representation.Source.Valid {spec} {domain} (.VarT name arguments) v) :\n" ++
    s!"    {goal} (.VarT name arguments) v := by\n" ++ proof ++
    s!"\n#audit_axioms {theoremName}"
  pure (Std.Format.text (boundedLines (s!"namespace {namespaceName}\n\n" ++ faithful ++
    (if sufficient then "" else "\n\n" ++ leaf) ++ "\n\n" ++
    proofDeclaration ++ s!"\n\nend {namespaceName}")))

/-- Discharge finite leaf fidelity from the actual explicitly bound child codecs. -/
def leafCorrectDeclarations (env : Env) (plan : Plan) (namespaceName : String)
    (sufficient : Bool := false) : Except String Std.Format := do
  let theoremName := if sufficient then "leafWitness" else "leafCorrect"
  let mut branches := []
  for (family, index) in plan.families.toList.zipIdx do
    let branch ← match family.leaf with
      | none => pure "    cases leaf"
      | some contract =>
        if sufficient then pure (
          "    obtain ⟨x, stable⟩ := (" ++ contract.sufficientProof
            (RepresentationFields.source env family.source) contract.codec ++
          s!") v (leafDomain{index} matching valid)\n    exact ⟨x, stable⟩")
        else pure (
          "    exact (" ++ contract.soundProof
            (RepresentationFields.source env family.source) contract.codec ++
          s!") fuel v x (leafDomain{index} matching valid) decoded")
    branches := branches ++ [s!"  | f{index} =>\n" ++ branch]
  let text := "/-- Checked source leaf codecs supply actual decoder facts. -/\n" ++
    s!"private theorem {theoremName} (input : typ') (v : value) (family : Family)\n" ++
    "    (leaf : isLeaf family = true) (matching : Matches input family)\n" ++
    s!"    (valid : Representation.Source.Valid {env.lib}.spec\n" ++
    "      Representation.Source.externDomain input v)" ++
    (if sufficient then " : ∃ x, Representation.Decodes (decode family) v x := by\n" else
      "\n    (fuel : Nat) (x : Carrier family) (decoded : decode family fuel v = some x) :\n" ++
      "    admitted family x ∧ Rel v (encode family x) := by\n") ++
    "  cases family with\n" ++ "\n".intercalate branches ++ s!"\n\n#audit_axioms {theoremName}"
  pure (Std.Format.text (boundedLines (s!"namespace {namespaceName}\n\n" ++ text ++
    s!"\n\nend {namespaceName}")))

/-- Emit plain source alias induction through the actual substitution derivation. -/
def aliasSourceDeclarations (env : Env) (plan : Plan) (namespaceName : String)
    (sufficient : Bool := false) : Except String Std.Format := do
  let goal := if sufficient then "Witness" else "Faithful"
  let leafName := if sufficient then "leafWitness" else "leafCorrect"
  let theoremName := if sufficient then "aliasSourceWitness" else "aliasSourceFaithful"
  let spec := env.lib ++ ".spec"
  let mut proof := "  intro family matching\n  cases matching with\n"
  for (family, index) in plan.families.toList.zipIdx do
    let .VarT _ arguments := family.source.it | continue
    proof := proof ++ matchingCase index arguments
    if family.leaf.isSome then
      proof := proof ++ s!"    exact {leafName} _ v .f{index} rfl " ++
        matchingValue index arguments ++ " whole\n"
      continue
    let some declaration := family.declaration | throw "recursive alias has no source declaration"
    let .TypD _ parameters definition _ := declaration.it
      | throw "recursive alias source must be defined"
    proof := proof ++ s!"    have actual : Representation.Source.body {spec} name.it =\n" ++
      "        " ++ sourceBody parameters definition ++ " := by\n      rw [nameEq]; rfl\n"
    match definition.it with
    | .PlainT _ =>
      let [child] := family.children | throw "recursive alias has more than one child"
      proof := proof ++ "    cases Option.some.inj (declared.symm.trans actual)\n" ++
        "    obtain ⟨_arity, substitutions⟩ := fields\n" ++
        "    cases substitutions with\n    | cons substitution tail =>\n      cases tail\n" ++
        (if sufficient then
          s!"      obtain ⟨x, stable⟩ := ih .f{child} (matchField{index}_0 " else
          s!"      exact soundAlias{index} v (ih .f{child} (matchField{index}_0 ") ++
        " ".intercalate (matchArguments arguments) ++ " " ++
        " ".intercalate ((List.range arguments.length).map (fun i => s!"harg{i}")) ++
        (if sufficient then s!" _ substitution)\n      exact ⟨x, decodeAlias{index} v x stable⟩\n"
          else " _ substitution))\n")
    | _ => proof := proof ++
        "    simp only [actual, Option.some.injEq, Prod.mk.injEq] at declared\n" ++
        "    obtain ⟨_, impossible⟩ := declared\n    cases impossible\n"
  let text := "/-- Plain source aliases preserve fidelity at arbitrary recursive depth. -/\n" ++
    s!"private theorem {theoremName}\n" ++
    "    (name : id) (arguments : List typ) (parameters : List tparam)\n" ++
    "    (definition instantiated : typ) (v : value)\n" ++
    s!"    (declared : Representation.Source.body {spec} name.it =\n" ++
    "      some (parameters, .PlainT definition))\n" ++
    "    (fields : Representation.Source.instantiatedFields parameters arguments\n" ++
    s!"      [definition] [instantiated]) (ih : {goal} instantiated.it v)\n" ++
    s!"    (whole : Representation.Source.Valid {spec} Representation.Source.externDomain\n" ++
    s!"      (.VarT name arguments) v) : {goal} (.VarT name arguments) v := by\n" ++
    proof ++ s!"\n#audit_axioms {theoremName}"
  pure (Std.Format.text (boundedLines (s!"namespace {namespaceName}\n\n" ++ text ++
    s!"\n\nend {namespaceName}")))

private def primitiveMinor (plan : Plan) (input : typ') (binders valid : String)
    (sufficient : Bool) : String :=
  let leafName := if sufficient then "leafWitness" else "leafCorrect"
  let branches := plan.families.toList.zipIdx.filterMap fun (family, index) =>
    if Types.typEq family.source.it input then
      some (s!"    | f{index} => exact {leafName} _ v .f{index} rfl .f{index} ({valid})")
    else none
  "  · intro " ++ binders ++ " family matching\n    cases matching" ++
    (if branches.isEmpty then "\n" else " with\n" ++ "\n".intercalate branches ++ "\n")

private def iterationMinor (plan : Plan) (kind : iter) (constructor : String)
    (sufficient : Bool) : Except String String := do
  let leafName := if sufficient then "leafWitness" else "leafCorrect"
  let binders := match constructor with
    | "list" => "element v raws shape payload ih"
    | "none" => "element v shape"
    | _ => "element v raw shape payload ih"
  let valid := match constructor with
    | "list" => "Representation.Source.Valid.list element v raws shape payload"
    | "none" => "Representation.Source.Valid.none element v shape"
    | _ => "Representation.Source.Valid.some element v raw shape payload"
  let mut branches := []
  for (family, index) in plan.families.toList.zipIdx do
    let .IterT _ actualKind := family.source.it | continue
    if actualKind != kind then continue
    let body ← if family.leaf.isSome then
      pure (s!"      exact {leafName} _ v .f{index} rfl (.f{index} element matching) ({valid})")
    else do
      let [child] := family.children | throw "recursive iteration source needs one child"
      pure (if sufficient then match constructor with
        | "list" => "      obtain ⟨xs, children⟩ := " ++
            s!"witnessesList .f{child} raws (fun raw member =>\n" ++
            s!"        listChildrenWitness element raws ih raw member .f{child} matching)\n" ++
            s!"      exact ⟨xs, decodeList{index} v raws xs shape children⟩"
        | "none" => s!"      exact ⟨none, decodeNone{index} v shape⟩"
        | _ => s!"      obtain ⟨x, stable⟩ := ih .f{child} matching\n" ++
            s!"      exact ⟨some x, decodeSome{index} v raw x shape stable⟩"
      else match constructor with
        | "list" => s!"      exact soundList{index} v raws shape (fun raw member =>\n" ++
            s!"        listChildren element raws ih raw member .f{child} matching)"
        | "none" => s!"      exact soundNone{index} v shape"
        | _ => s!"      exact soundSome{index} v raw shape (ih .f{child} matching)")
    branches := branches ++ [s!"    | f{index} element matching =>\n" ++ body]
  pure ("  · intro " ++ binders ++ " family matching\n    cases matching" ++
    (if branches.isEmpty then "\n" else " with\n" ++ "\n".intercalate branches ++ "\n"))

private def impossibleNominal (env : Env) (family : Family) : Except String String := do
  let some declaration := family.declaration | throw "source family has no actual declaration"
  let .TypD _ parameters definition _ := declaration.it
    | throw "source family is not a defined declaration"
  pure (s!"      have actual : Representation.Source.body {env.lib}.spec name.it =\n" ++
    "          " ++ sourceBody parameters definition ++ " := by\n        rw [nameEq]; rfl\n")

/-- Emit the full mutual source-derivation fidelity proof for a finite recursive family.
Every leaf is discharged by its actual codec; local cases use only source grammar induction. -/
def sourceFidelityDeclarations (env : Env) (plan : Plan) (namespaceName : String)
    (sufficient : Bool := false) : Except String Std.Format := do
  let goal := if sufficient then "Witness" else "Faithful"
  let leafName := if sufficient then "leafWitness" else "leafCorrect"
  let suffix := if sufficient then "Witness" else "Faithful"
  let listChildrenName := if sufficient then "listChildrenWitness" else "listChildren"
  let spec := env.lib ++ ".spec"
  let domain := "Representation.Source.externDomain"
  let listChildren := "/-- Homogeneous source induction supplies every child fidelity fact. -/\n" ++
    s!"private theorem {listChildrenName} (element : typ) (raws : List value)\n" ++
    s!"    (ih : List.Forall₂ (fun type raw => {goal} type.it raw)\n" ++
    "      (List.replicate raws.length element) raws) :\n" ++
    s!"    ∀ raw ∈ raws, {goal} element.it raw := by\n" ++
    "  induction raws with\n  | nil => intro raw member; cases member\n" ++
    "  | cons raw raws rec =>\n" ++
    "    simp only [List.length_cons, List.replicate_succ] at ih\n" ++
    "    cases ih with\n    | cons head tail =>\n" ++
    "      intro rawValue member\n      rcases List.mem_cons.mp member with rfl | member\n" ++
    "      · exact head\n      · exact rec tail rawValue member\n" ++
    s!"\n#audit_axioms {listChildrenName}"
  let mut recordCases := []
  let mut externCases := []
  for (family, index) in plan.families.toList.zipIdx do
    let .VarT _ arguments := family.source.it | continue
    let recordHeader := "    " ++ (matchingCase index arguments).trimAscii.toString ++ "\n"
    let externalHeader := s!"    | f{index} name nameEq =>\n"
    if family.leaf.isSome then
      recordCases := recordCases ++ [recordHeader ++
        s!"      exact {leafName} _ v .f{index} rfl " ++
        matchingValue index arguments ++ " whole\n"]
      if arguments.isEmpty then
        externCases := externCases ++ [externalHeader ++
          s!"      exact {leafName} _ v .f{index} rfl (.f{index} name nameEq)\n" ++
          "        (Representation.Source.Valid.external name v declared payload)\n"]
      continue
    if let some (.StructT _) := family.body then
      throw "recursive record source fidelity composition is not yet implemented"
    let actual ← impossibleNominal env family
    recordCases := recordCases ++ [recordHeader ++ actual ++
      "      simp only [actual, Option.some.injEq, Prod.mk.injEq] at declared\n" ++
      "      obtain ⟨_, impossible⟩ := declared\n      cases impossible\n"]
    if arguments.isEmpty then
      externCases := externCases ++ [externalHeader ++ actual ++
        "      have impossible := Representation.Source.externalFalseOfBody actual\n" ++
        "      rw [impossible] at declared\n      cases declared\n"]
  let record := "/-- Records retain their source declaration family. -/\n" ++
    s!"private theorem recordSource{suffix} (name : id) (arguments : List typ)\n" ++
    "    (parameters : List tparam) (sourceFields : List typfield)\n" ++
    s!"    (v : value) (declared : Representation.Source.body {spec} name.it =\n" ++
    "      some (parameters, .StructT sourceFields))\n" ++
    s!"    (whole : Representation.Source.Valid {spec} {domain} (.VarT name arguments) v) :\n" ++
    s!"    {goal} (.VarT name arguments) v := by\n" ++
    "  intro family matching\n  cases matching with\n" ++
    String.join recordCases ++ s!"\n#audit_axioms recordSource{suffix}"
  let extern := "/-- Source external declarations use independent checked leaf codecs. -/\n" ++
    s!"private theorem externalSource{suffix} (name : id) (v : value)\n" ++
    s!"    (declared : Representation.Source.external {spec} name.it = true)\n" ++
    s!"    (payload : {domain}.external name.it v) : {goal} (.VarT name []) v := by\n" ++
    "  intro family matching\n  cases matching with\n" ++
    String.join externCases ++ s!"\n#audit_axioms externalSource{suffix}"
  let proof := primitiveMinor plan .BoolT "v b shape"
      "Representation.Source.Valid.bool v b shape" sufficient ++
    primitiveMinor plan (.NumT .NatT) "v n shape"
      "Representation.Source.Valid.nat v n shape" sufficient ++
    primitiveMinor plan (.NumT .IntT) "v n shape"
      "Representation.Source.Valid.int v n shape" sufficient ++
    primitiveMinor plan .TextT "v text shape"
      "Representation.Source.Valid.text v text shape" sufficient ++
    (← iterationMinor plan .List "list" sufficient) ++
    (← iterationMinor plan .Opt "none" sufficient) ++
    (← iterationMinor plan .Opt "some" sufficient) ++
    "  · intro types v raws shape payload ih family matching; cases matching\n" ++
    "  · intro name arguments parameters definition instantiated v declared fields payload ih\n" ++
    s!"    exact aliasSource{suffix} name arguments parameters definition instantiated v\n" ++
    "      declared fields ih (.alias name arguments parameters definition instantiated v\n" ++
    "        declared fields payload)\n" ++
    "  · intro name arguments parameters sourceFields instantiated v valueFields declared\n" ++
    "      shape labels fields payload ih\n" ++
    s!"    exact recordSource{suffix} name arguments parameters sourceFields v declared\n" ++
    "      (.record name arguments parameters sourceFields instantiated v valueFields\n" ++
    "        declared shape labels fields payload)\n" ++
    "  · intro name arguments parameters cases constructor instantiated v tree declared member\n" ++
    "      shape mixop fields payload ih\n" ++
    s!"    exact variantSource{suffix} {leafName} name arguments parameters cases constructor\n" ++
    "      instantiated v tree declared member shape mixop fields ih\n" ++
    "      (.variant name arguments parameters cases constructor instantiated v tree\n" ++
    "        declared member shape mixop fields payload)\n" ++
    s!"  · exact externalSource{suffix}\n" ++
    "  · intro name arguments v payload\n" ++
    "    exact absurd payload (Representation.Source.externDomainNoRuntime _ v)\n" ++
    "  · exact .nil\n" ++
    "  · intro type v types values head tail ihHead ihTail; exact .cons ihHead ihTail\n"
  let main := "/-- Complete actual decoder facts by independent source derivation. -/\n" ++
    s!"private theorem source{suffix}" ++ " {input : typ'} {v : value}\n" ++
    s!"    (valid : Representation.Source.Valid {spec} {domain} input v) :\n" ++
    s!"    {goal} input v := by\n" ++
    s!"  apply Representation.Source.Valid.rec (motive_1 := fun type v _ => {goal} type v)\n" ++
    "    (motive_2 := fun types raws _ =>\n" ++
    s!"      List.Forall₂ (fun type raw => {goal} type.it raw) types raws) (t := valid)\n" ++
    proof ++ s!"\n#audit_axioms source{suffix}"
  let choose := if !sufficient then "" else
    "/-- Finite child witnesses preserve every list position without a depth cutoff. -/\n" ++
    "private theorem witnessesList (child : Family) (raws : List value)\n" ++
    "    (children : ∀ raw ∈ raws, ∃ x, Representation.Decodes (decode child) raw x) :\n" ++
    "    ∃ xs, List.Forall₂ (Representation.Decodes (decode child)) raws xs := by\n" ++
    "  induction raws with\n  | nil => exact ⟨[], .nil⟩\n" ++
    "  | cons raw raws ih =>\n" ++
    "    obtain ⟨x, head⟩ := children raw (by simp)\n" ++
    "    obtain ⟨xs, tail⟩ := ih (fun raw member => children raw (by simp [member]))\n" ++
    "    exact ⟨x :: xs, .cons head tail⟩\n\n#audit_axioms witnessesList\n\n"
  pure (Std.Format.text (boundedLines (s!"namespace {namespaceName}\n\n" ++
    choose ++ listChildren ++
    "\n\n" ++ record ++ "\n\n" ++ extern ++ "\n\n" ++ main ++
    s!"\n\nend {namespaceName}")))

private def aliasComposition (env : Env) (index child : Nat) (name : String)
    (family : Family) : String := Id.run do
  let adjustment := if family.guarded then "(fuel + 1)" else "fuel"
  let unfoldDecoder := if family.guarded then " " ++ env.q (ofValueName name) else ""
  let encoded := "/-- The actual source alias retains its child's exact encoding. -/\n" ++
    s!"private theorem aliasEncoding{index} (x : Carrier .f{child}) :\n" ++
    s!"    encode .f{index} x = encode .f{child} x := by\n" ++
    "  dsimp only [encode]\n" ++
    "  unfold " ++ " ".intercalate family.encoderUnfolding ++ "\n  rfl\n" ++
    s!"\n#audit_axioms aliasEncoding{index}"
  let decoded := "/-- Exact alias decoder fuel policy in recursive field context. -/\n" ++
    s!"private theorem aliasDecoding{index} (fuel : Nat) (v : value) :\n" ++
    s!"    decode .f{index} {adjustment} v = decode .f{child} fuel v := by\n" ++
    "  unfold decode" ++ unfoldDecoder ++ "\n  rfl\n" ++
    s!"\n#audit_axioms aliasDecoding{index}"
  let sound := "/-- Faithful admitted child decoding is preserved by the actual alias. -/\n" ++
    s!"private theorem soundAlias{index} (v : value)\n" ++
    s!"    (child : ∀ fuel x, decode .f{child} fuel v = some x →\n" ++
    s!"      admitted .f{child} x ∧ Rel v (encode .f{child} x))\n" ++
    s!"    (fuel : Nat) (x : Carrier .f{index})\n" ++
    s!"    (decoded : decode .f{index} fuel v = some x) :\n" ++
    s!"    admitted .f{index} x ∧ Rel v (encode .f{index} x) := by\n"
  let indent := if family.guarded then "    " else "  "
  let split := if family.guarded then
    "  cases fuel with\n  | zero => cases decoded\n  | succ fuel =>\n" else ""
  let sound := sound ++ split ++ indent ++ s!"rw [aliasDecoding{index}] at decoded\n" ++
    indent ++ "obtain ⟨accepted, related⟩ := child fuel x decoded\n" ++
    indent ++ "constructor\n" ++ indent ++ "· exact .alias x accepted\n" ++
    indent ++ s!"· rw [aliasEncoding{index}]; exact related\n" ++
    s!"\n#audit_axioms soundAlias{index}"
  let stable := "/-- Stable child decoding is preserved by the actual alias fuel frame. -/\n" ++
    s!"private theorem decodeAlias{index} (v : value) (x : Carrier .f{child})\n" ++
    s!"    (child : Representation.Decodes (decode .f{child}) v x) :\n" ++
    s!"    Representation.Decodes (decode .f{index}) v x := by\n" ++
    "  obtain ⟨bound, stable⟩ := child\n" ++
    s!"  refine ⟨bound{if family.guarded then " + 1" else ""}, ?_⟩\n" ++
    "  intro fuel large\n" ++
    (if family.guarded then
      "  cases fuel with\n  | zero => omega\n  | succ fuel =>\n" else "") ++
    indent ++ s!"rw [aliasDecoding{index}]\n" ++
    indent ++ "exact stable fuel (by omega)\n" ++ s!"\n#audit_axioms decodeAlias{index}"
  return encoded ++ "\n\n" ++ decoded ++ "\n\n" ++ sound ++ "\n\n" ++ stable

/-- Emit actual alias encoder, decoder and conditional faithful composition equations. -/
def aliasCompositionDeclarations (env : Env) (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut declarations := []
  for (family, index) in plan.families.toList.zipIdx do
    let some (.PlainT _) := family.body | continue
    let .VarT name _ := family.source.it | throw "recursive source alias is not nominal"
    let [child] := family.children | throw "recursive source alias needs exactly one child"
    declarations := declarations ++ [aliasComposition env index child name.it family]
  pure (Std.Format.text (boundedLines (s!"namespace {namespaceName}\n\n" ++
    "\n\n".intercalate declarations ++ s!"\n\nend {namespaceName}")))

/-- Bundle source soundness and stable sufficiency with the actual finite-family dictionaries. -/
def decoderDeclarations (env : Env) (namespaceName : String) : Std.Format :=
  Std.Format.text (boundedLines (s!"namespace {namespaceName}\n\n" ++
    "/-- Actual recursive decoders cover the independently quoted source grammar. -/\n" ++
    "private theorem decoderCorrect (family : Family) :\n" ++
    "    @Representation.DecoderCorrect (Carrier family) ⟨encode family⟩\n" ++
    s!"      (Representation.Source.Valid {env.lib}.spec Representation.Source.externDomain\n" ++
    "        (source family)) (admitted family) (decode family) := by\n" ++
    "  letI : ToValue (Carrier family) := ⟨encode family⟩\n" ++
    "  constructor\n" ++
    "  · intro fuel v x valid decoded\n" ++
    "    exact sourceFaithful valid family (sourceMatches family) fuel x decoded\n" ++
    "  · intro v valid\n" ++
    "    exact sourceWitness valid family (sourceMatches family)\n" ++
    "\n#audit_axioms decoderCorrect\n\n" ++ s!"end {namespaceName}"))

end P4SpecTec.Codegen.RepresentationRecursive
