import P4SpecTec.Codegen.Certificates.RepresentationRecursive

/-!
Structural generated-carrier admission for recursive source codecs. These predicates
follow the actual source constructors and independently admitted children. Explicit
runtime-only carrier alternatives have no admission constructor in the source profile;
the runtime profile admits them.
-/

namespace P4SpecTec.Codegen.RepresentationRecursive

open P4SpecTec.Lang.Il P4SpecTec.Codegen.Types

private def childAdmission (plan : Plan) (index : Nat) (value : String) :
    Except String String := do
  let some family := plan.families[index]? | throw "recursive admission child index is invalid"
  match family.leaf with
  | some contract => pure ("(" ++ contract.admitted ++ ") " ++ value)
  | none => pure s!"AdmittedF{index} {value}"

private def constructor (plan : Plan) (index : Nat) (name value : String)
    (children : List Nat) : Except String String := do
  let values := children.zipIdx.map fun (child, position) =>
    s!" (x{position} : Carrier .f{child})"
  let hypotheses ← children.zipIdx.mapM fun (child, position) => do
    pure (s!" (h{position} : " ++ (← childAdmission plan child s!"x{position}") ++ ")")
  pure ("  | " ++ name ++ String.join values ++ String.join hypotheses ++
    s!" : AdmittedF{index} ({value})")

private def admission (env : Env) (plan : Plan) (index : Nat) (family : Family) :
    Except String Std.Format := do
  let header := "/-- Structural source admission for the actual generated carrier. -/\n" ++
    s!"inductive AdmittedF{index} : Carrier .f{index} → Prop where\n"
  let body ← match family.source.it, family.body with
    | .IterT _ .List, _ =>
      let [child] := family.children | throw "recursive list admission needs one child family"
      let predicate ← childAdmission plan child "x"
      pure (s!"  | nil : AdmittedF{index} []\n" ++
        s!"  | cons (x : Carrier .f{child}) (xs : Carrier .f{index})\n" ++
        s!"      (head : {predicate}) (tail : AdmittedF{index} xs) : AdmittedF{index} (x :: xs)")
    | .IterT _ .Opt, _ =>
      let [child] := family.children | throw "recursive option admission needs one child family"
      let predicate ← childAdmission plan child "x"
      pure (s!"  | none : AdmittedF{index} none\n" ++
        s!"  | some (x : Carrier .f{child}) (payload : {predicate}) : AdmittedF{index} (some x)")
    | .VarT _ _, some (.PlainT _) =>
      let [child] := family.children | throw "recursive alias admission needs one child family"
      let predicate ← childAdmission plan child "x"
      pure s!"  | alias (x : Carrier .f{child}) (payload : {predicate}) : AdmittedF{index} x"
    | .VarT _ _, some (.StructT _) =>
      let values := (List.range family.children.length).map (fun position => s!"x{position}")
      constructor plan index "mk" ("⟨" ++ ", ".intercalate values ++ "⟩") family.children
    | .VarT name _, some (.VariantT cases) => do
      let mut constructors := []
      let mut cursor := 0
      for (sourceCase, name_) in cases.zip (ctorNames cases) do
        let count := Domain.Mixfix.args sourceCase.nottyp.it |>.length
        let children := family.children.drop cursor |>.take count
        let values := (List.range count).map (fun position => s!"x{position}")
        let value := env.q (Names.typeName name.it) ++ "." ++ name_ ++ " " ++
          " ".intercalate values
        constructors := constructors ++ [← constructor plan index name_ value children]
        cursor := cursor + count
      if cursor != family.children.length then throw "recursive variant admission field mismatch"
      -- The runtime profile admits the carrier's explicit raw-extern alternative.
      if env.runtimeProfile && family.runtimeExtended then
        constructors := constructors ++ [s!"  | {Representation.rawExternCtor} " ++
          "(x0 : P4SpecTec.Prelude.ExternValue) : " ++
          s!"AdmittedF{index} ({runtimeExternValue env name.it} x0)"]
      pure ("\n".intercalate constructors)
    | _, _ => throw "recursive admission needs a supported actual source body"
  pure (Std.Format.text (boundedLines (header ++ body)))

/-- Emit mutual structural carrier predicates and their finite-family dispatcher.
The result consists of complete commands, preserving the mutual declaration block. -/
def admissionDeclarations (env : Env) (plan : Plan) (namespaceName : String) :
    Except String (List Std.Format) := do
  let mut predicates := []
  let mut branches := []
  for (family, index) in plan.families.toList.zipIdx do
    if family.leaf.isNone then
      predicates := predicates ++ [← admission env plan index family]
    let predicate ← childAdmission plan index "x"
    branches := branches ++ [s!"  | .f{index}, x => {predicate}"]
  pure [Std.Format.text s!"namespace {namespaceName}", mutualBlock predicates,
    Std.Format.text (boundedLines (
      (if env.runtimeProfile then
        "/-- Structural admission, including the runtime-only raw-extern alternatives. -/\n"
      else "/-- Structural admission excludes runtime-only constructors recursively. -/\n") ++
      "def admitted : (family : Family) → Carrier family → Prop\n" ++
      "\n".intercalate branches)), Std.Format.text s!"end {namespaceName}"]

end P4SpecTec.Codegen.RepresentationRecursive
