import P4SpecTec.Codegen.Certificates.RepresentationRecursive

/-!
Source-field classification for recursive codec emission. The emitted theorems
classify actual source substitution derivations using declared parameter bindings;
they do not inspect an encoder image or require a successful decoder.
-/

namespace P4SpecTec.Codegen.RepresentationRecursive

open P4SpecTec.Lang.Il P4SpecTec.Codegen.Types

private def syntaxIndex (plan : Plan) (t : typ) : Except String Nat := do
  let some index := plan.families.findIdx? (fun family => Types.typEq family.source.it t.it)
    | throw "recursive field syntax is absent from its family closure"
  pure index

private def quotedType (t : typ) : String := "(" ++ (Reify.typ t).fmt.pretty ++ ")"

private partial def classification (plan : Plan) (parameters : List String)
    (arguments : List typ) (original : typ) (target : Nat) (substitution fresh : String) :
    Except String String := do
  let some family := plan.families[target]? | throw "recursive field index is invalid"
  match original.it with
  | .BoolT => pure s!"rw [{substitution}.boolResult]; exact .f{target}"
  | .NumT _ => pure s!"rw [{substitution}.numResult]; exact .f{target}"
  | .TextT => pure s!"rw [{substitution}.textResult]; exact .f{target}"
  | .VarT name sourceArgs =>
    if let some index := parameters.findIdx? (· == name.it) then
      if !sourceArgs.isEmpty then throw "source parameters cannot be applied as constructors"
      let some argument := arguments[index]? | throw "recursive source parameter arity mismatch"
      if !Types.typEq argument.it family.source.it then
        throw "recursive parameter source shape differs from the requested child family"
      pure (s!"rw [{substitution}.boundResult (Q.i {(Reify.str name.it).fmt.pretty}) " ++
        s!"(by rfl)]\nexact _harg{index}")
    else
      let .VarT _ targetArgs := family.source.it
        | throw "recursive nominal field has a nonnominal instantiated family"
      if sourceArgs.length != targetArgs.length then
        throw "recursive nominal field changes its source arity"
      let id := "(Q.i " ++ (Reify.str name.it).fmt.pretty ++ ")"
      let sourceArgsText := (Reify.lst (sourceArgs.map Reify.typ)).arg.pretty
      let mut proof := s!"obtain ⟨{fresh}args, {fresh}shape, {fresh}subs⟩ := " ++
        s!"{substitution}.namedArguments {id} {sourceArgsText} (by rfl)\n" ++
        s!"rw [{fresh}shape]\n"
      let mut indent := ""
      let mut tail := fresh ++ "subs"
      for position in List.range sourceArgs.length do
        proof := proof ++ indent ++ s!"cases {tail} with\n" ++ indent ++
          s!"| cons {fresh}sub{position} {fresh}rest{position} =>\n"
        indent := indent ++ "  "
        tail := s!"{fresh}rest{position}"
      proof := proof ++ indent ++ s!"cases {tail}\n" ++ indent ++
        s!"refine .f{target} {id} " ++
        " ".intercalate (List.replicate sourceArgs.length "_") ++ " rfl" ++
        String.join (List.replicate sourceArgs.length " ?_")
      for ((source, actual), position) in (sourceArgs.zip targetArgs).zipIdx do
        let child ← syntaxIndex plan actual
        let body ← classification plan parameters arguments source child
          s!"{fresh}sub{position}" s!"{fresh}{position}_"
        proof := proof ++ "\n" ++ indent ++ "· " ++ body.replace "\n" ("\n" ++ indent ++ "  ")
      pure proof
  | .IterT sourceElement kind =>
    let .IterT targetElement _ := family.source.it
      | throw "recursive iterated field has a noniterated instantiated family"
    let child ← syntaxIndex plan targetElement
    let kind := if kind == .List then ".List" else ".Opt"
    let body ← classification plan parameters arguments sourceElement child
      (fresh ++ "sub") (fresh ++ "inner_")
    pure (s!"obtain ⟨{fresh}element, {fresh}shape, {fresh}sub⟩ := " ++
      s!"{substitution}.iterResult {quotedType sourceElement} {kind}\n" ++
      s!"rw [{fresh}shape]\nrefine .f{target} {fresh}element ?_\n" ++ body)
  | _ => throw "recursive field classification does not support this source form"

private def sourceFields : deftyp' → List typ
  | .PlainT target => [target]
  | .StructT fields => fields.map (·.2)
  | .VariantT cases => cases.flatMap fun c => Domain.Mixfix.args c.nottyp.it

/-- Emit source substitution classification for every locally expanded nominal field.
The finite-family dispatcher must be emitted first in the same namespace. -/
def fieldMatchingDeclarations (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut declarations := []
  for (family, index) in plan.families.toList.zipIdx do
    let some declaration := family.declaration | continue
    let .TypD _ parameters definition _ := declaration.it
      | throw "recursive source classification needs a defined type"
    let .VarT _ arguments := family.source.it
      | throw "recursive nominal source family has a nonnominal root"
    let fields := sourceFields definition.it
    if fields.length != family.children.length then
      throw "recursive source classification field arity differs from its descriptor"
    let parameterNames := parameters.map (·.it)
    let argumentNames := (List.range arguments.length).map (fun i => s!"arg{i}")
    let bindings := "[" ++ ", ".intercalate (parameterNames.zipIdx.map fun (name, position) =>
      s!"({(Reify.str name).fmt.pretty}, arg{position}.it)") ++ "].reverse"
    let binders := if argumentNames.isEmpty then "" else
      " (" ++ " ".intercalate argumentNames ++ " : typ)"
    let hypotheses ← (arguments.zipIdx).mapM fun (argument, position) => do
      let child ← syntaxIndex plan argument
      pure s!"\n    (_harg{position} : Matches arg{position}.it .f{child})"
    for ((field, child), position) in (fields.zip family.children).zipIdx do
      let body ← classification plan parameterNames arguments field child "substitution" "s_"
      let name := s!"matchField{index}_{position}"
      declarations := declarations ++ [
        "/-- Actual field substitution retains its finite source-family membership. -/\n" ++
        s!"private theorem {name}{binders}" ++ String.join hypotheses ++
        "\n    (result : typ')\n    (substitution : Representation.Source.Substitutes " ++
        bindings ++ " " ++ quotedType field ++ ".it result) :\n" ++
        s!"    Matches result .f{child} := by\n  " ++ body.replace "\n" "\n  " ++
        s!"\n\n#audit_axioms {name}"]
  pure (Std.Format.text (boundedLines (
    s!"namespace {namespaceName}\n\n" ++ "\n\n".intercalate declarations ++
    s!"\n\nend {namespaceName}")))

private partial def leafDomainOrder (plan : Plan) (index : Nat) (done : List Nat) :
    Except String (List Nat) := do
  if done.contains index then return done
  let some family := plan.families[index]? | throw "recursive leaf domain index is invalid"
  if family.leaf.isNone then throw "recursive leaf domain depends on a locally expanded family"
  let done ← match family.source.it with
    | .IterT element _ => leafDomainOrder plan (← syntaxIndex plan element) done
    | .VarT _ (_ :: _) => throw "parameterized recursive leaf domain transport is not implemented"
    | _ => pure done
  pure (done ++ [index])

private def leafDomain (plan : Plan) (index : Nat) : Except String String := do
  let some family := plan.families[index]? | throw "recursive leaf domain index is invalid"
  let branch ← match family.source.it with
    | .BoolT | .NumT _ | .TextT => pure s!"  | f{index} => exact valid"
    | .VarT _ [] => pure (s!"  | f{index} name nameEq =>\n" ++
        "    exact valid.nominalName nameEq")
    | .IterT element _ => do
      let child ← syntaxIndex plan element
      pure (s!"  | f{index} element matching =>\n" ++
        s!"    exact Representation.Source.Valid.iterDomain\n" ++
        s!"      (fun _ valid => leafDomain{child} matching valid) valid")
    | _ => throw "recursive leaf source-domain transport is not implemented"
  pure ("/-- Syntax membership transports a leaf to its independent source domain. -/\n" ++
    s!"private theorem leafDomain{index} " ++ "{spec externalDomain input}\n" ++
    s!"    (matching : Matches input .f{index}) " ++ "{v}\n" ++
    "    (valid : Representation.Source.Valid spec externalDomain input v) :\n" ++
    s!"    Representation.Source.Valid spec externalDomain (source .f{index}) v := by\n" ++
    "  cases matching with\n" ++ branch ++ s!"\n\n#audit_axioms leafDomain{index}")

/-- Emit metadata-independent source-domain transport for each checked nonrecursive leaf.
The proof is generic in the specification and its independent external source domain. -/
def leafDomainDeclarations (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut order := []
  for (family, index) in plan.families.toList.zipIdx do
    if family.leaf.isSome then order ← leafDomainOrder plan index order
  let declarations ← order.mapM (leafDomain plan)
  pure (Std.Format.text (boundedLines (
    s!"namespace {namespaceName}\n\n" ++ "\n\n".intercalate declarations ++
    s!"\n\nend {namespaceName}")))

private partial def fieldIdentity (parameters : List String) (arguments : List typ)
    (original actual : typ) : Except String String := do
  match original.it, actual.it with
  | .BoolT, .BoolT => pure "Representation.Source.Substitutes.bool"
  | .NumT kind, .NumT _ =>
    let kind := if kind == .NatT then ".NatT" else ".IntT"
    pure s!"Representation.Source.Substitutes.num {kind}"
  | .TextT, .TextT => pure "Representation.Source.Substitutes.text"
  | .VarT name [], _ =>
    if let some index := parameters.findIdx? (· == name.it) then
      let some argument := arguments[index]? | throw "recursive identity parameter arity mismatch"
      if !Types.typEq argument.it actual.it then
        throw "recursive field identity changes its declared parameter type"
      pure ("Representation.Source.Substitutes.bound (Q.i " ++
        (Reify.str name.it).fmt.pretty ++ ") " ++ quotedType actual ++ ".it (by rfl)")
    else
      let .VarT _ [] := actual.it
        | throw "recursive unbound field identity changes its source shape"
      pure ("Representation.Source.Substitutes.named (Q.i " ++
        (Reify.str name.it).fmt.pretty ++ ") [] [] (by rfl) .nil")
  | .VarT name sourceArgs, .VarT _ targetArgs =>
    if parameters.contains name.it then throw "source parameters cannot be constructor applications"
    if sourceArgs.length != targetArgs.length then throw "recursive identity changes source arity"
    let children ← (sourceArgs.zip targetArgs).mapM fun (a, b) =>
      fieldIdentity parameters arguments a b
    let payload := children.foldr (fun child rest => ".cons (" ++ child ++ ") (" ++ rest ++ ")")
      ".nil"
    pure ("Representation.Source.Substitutes.named (Q.i " ++
      (Reify.str name.it).fmt.pretty ++ ") " ++
      (Reify.lst (sourceArgs.map Reify.typ)).arg.pretty ++ " " ++
      (Reify.lst (targetArgs.map Reify.typ)).arg.pretty ++ " (by rfl) (" ++ payload ++ ")")
  | .IterT source kind, .IterT target _ =>
    let child ← fieldIdentity parameters arguments source target
    let kind := if kind == .List then ".List" else ".Opt"
    pure ("Representation.Source.Substitutes.iter " ++ quotedType source ++ " " ++
      quotedType target ++ s!" {kind} ({child})")
  | _, _ => throw "recursive field identity is not implemented for this source shape"

/-- Emit actual closed source-field instantiation derivations for encoder validity.
The source declaration, parameter bindings and every child type are taken from the plan. -/
def fieldInstantiationDeclarations (plan : Plan) (namespaceName : String) :
    Except String Std.Format := do
  let mut declarations := []
  for (family, index) in plan.families.toList.zipIdx do
    let some declaration := family.declaration | continue
    let .TypD _ parameters definition _ := declaration.it
      | throw "recursive source instantiation needs a defined type"
    let .VarT _ arguments := family.source.it
      | throw "recursive nominal instantiation needs a nominal source root"
    let fields := sourceFields definition.it
    let parameterNames := parameters.map (·.it)
    let bindings := "[" ++ ", ".intercalate ((parameterNames.zip arguments).map fun (name, t) =>
      "(" ++ (Reify.str name).fmt.pretty ++ ", " ++ quotedType t ++ ".it)") ++ "].reverse"
    for ((field, child), position) in (fields.zip family.children).zipIdx do
      let some target := plan.families[child]? | throw "recursive instantiation child is absent"
      let proof ← fieldIdentity parameterNames arguments field target.source
      let name := s!"instantiateField{index}_{position}"
      declarations := declarations ++ [
        "/-- The actual closed parameter binding instantiates this declared source field. -/\n" ++
        s!"private theorem {name} : Representation.Source.Substitutes {bindings}\n" ++
        "    " ++ quotedType field ++ s!".it (source .f{child}) :=\n  {proof}\n\n" ++
        s!"#audit_axioms {name}"]
  pure (Std.Format.text (boundedLines (
    s!"namespace {namespaceName}\n\n" ++ "\n\n".intercalate declarations ++
    s!"\n\nend {namespaceName}")))

end P4SpecTec.Codegen.RepresentationRecursive
