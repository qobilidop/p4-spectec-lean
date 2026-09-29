import P4SpecTec.Codegen.Certificates.SourceBuiltin

/-!
Source-domain contracts for structurally checked polymorphic membership and pair projections.
Parameter codecs remain explicit, and source-domain preservation adds no equality law to the
independent execution correspondence certificates.
-/

namespace P4SpecTec.Codegen.SourcePolymorphic
open P4SpecTec.Lang.Il P4SpecTec.Codegen.SourceBuiltinCertificates

/-- A supported defined operation, with a constructor projection or a Boolean result. -/
structure Plan where
  /-- Declared parameter names, in source order. -/
  parameters : List String
  /-- Actual source input contracts. -/
  inputs : List Field
  /-- Actual source result contract. -/
  output : Field
  /-- The projected pair component; absent for the Boolean-producing membership fragment. -/
  projection : Option Nat

/-- Recognize the actual defined operation using checked nominal codecs. -/
def planWithKnown (env : Env) (known : String → Option RepresentationFields.NominalContract)
    (d : Lang.Al.def) : Except String Plan := do
  unless env.mode == .pure do throw "source polymorphic contracts require pure execution"
  let .FuncDecD _ parameters inputs result _ none _ := d.it
    | throw "source polymorphic contract needs a defined function"
  let parameters := parameters.map (·.it)
  let projection ← if Validate.polymorphicMembership env d then pure none
    else if Validate.polymorphicPairProjection env d then do
      unless parameters.length == 2 && inputs.length == 1 do
        throw "source projection needs one two-parameter map"
      let [.mk (.ExpP input) _ _] := inputs | throw "source projection input is not first-order"
      unless BuiltinCertificates.shape parameters input.it == "map($0,$1)" do
        throw "source projection input is not the declared map"
      match BuiltinCertificates.shape parameters result.it with
      | "set($0)" => pure (some 0)
      | "set($1)" => pure (some 1)
      | _ => throw "source projection result is not a parameter set"
    else throw "unsupported polymorphic source operation"
  let inputs ← inputs.mapM fun p => match p.it with
    | .ExpP type => fieldWithKnown env known parameters type
    | _ => throw "source polymorphic callback is unsupported"
  let output ← fieldWithKnown env known parameters result
  return { parameters, inputs, output, projection }

/-- Recognize a standalone defined operation, resolving named codecs recursively. -/
def plan (env : Env) (d : Lang.Al.def) : Except String Plan := do
  planWithKnown env (namedKnown env) d

/-- Exact source coverage and successful-output contract for the selected defined operation. -/
def theoremType (env : Env) (d : Lang.Al.def) : Except String String := do
  let p ← plan env d
  return domainType env d p.parameters p.inputs p.output

/-- Complete source codecs required by the selected signature. -/
def dependencies (env : Env) (d : Lang.Al.def) : Except String (List String) := do
  let p ← plan env d
  return ((p.inputs ++ [p.output]).flatMap (·.dependencies)).eraseDups

/-- Reusable proof dependencies, independent of generated source codec sidecars. -/
def supportImports : List String := SourceBuiltinCertificates.supportImports

/-- Emit actual coverage witnesses and a proof about successful outputs from a resolved plan. -/
private def declarationsOfPlan (env : Env) (d : Lang.Al.def) (p : Plan) :
    Except String String := do
  let introLine := "intro " ++ " ".intercalate
    (p.inputs.zipIdx.flatMap fun (_, i) => [s!"p{i}", s!"hp{i}"]) ++ " result run\n"
  let encoding := "apply " ++ p.output.toContract.encodingProof
    (p.output.source env) p.output.codec ++ " result\n"
  let body ← match p.projection with
    | none => pure "trivial"
    | some selected =>
      let projection := if selected == 0 then ".1" else ".2"
      pure ("rcases p0 with ⟨xs⟩\n" ++
        "simp only [" ++ env.q (Names.funcName d.it.id.it) ++
        ", List.mapM_pure] at run\n" ++
        "cases Except.ok.inj (Option.some.inj run)\n" ++
        "intro value member\n" ++
        "obtain ⟨entry, originalMember, rfl⟩ := List.mem_map.mp member\n" ++
        "obtain ⟨entry, pairMember, rfl⟩ := List.mem_map.mp originalMember\n" ++
        "cases entry with | colon k v => exact (hp0 _ pairMember)" ++ projection)
  return domainDeclaration env d p.parameters p.inputs p.output (introLine ++ encoding ++ body)

/-- Emit actual coverage witnesses and successful-output proof for a standalone operation. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String String := do
  declarationsOfPlan env d (← plan env d)

/-- Render proof, exact statement and dependencies from one catalog-backed operation plan. -/
def complete (env : Env) (known : String → Option RepresentationFields.NominalContract)
    (d : Lang.Al.def) : Except String (String × String × List String) := do
  let p ← planWithKnown env known d
  return (← declarationsOfPlan env d p,
    domainType env d p.parameters p.inputs p.output,
    ((p.inputs ++ [p.output]).flatMap (·.dependencies)).eraseDups)

end P4SpecTec.Codegen.SourcePolymorphic
