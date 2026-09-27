import P4SpecTec.Codegen.Reify
import P4SpecTec.Codegen.QuoteCheck
import P4SpecTec.Refine.SourceProfile

/-!
Typed source metavariables are retained in a separate source-order quotation.
The executable spec continues to omit them because AL initialization does not bind values.
Structural export comparison and kernel no-op evidence account for that omission; codecs
for each declared type remain independent certificate dependencies.
-/

namespace P4SpecTec.Codegen.SourceProfiles

open P4SpecTec.Lang.Il Std

/-- A source variable's actual name and declared type, independent of codec availability. -/
structure Variable where
  /-- Actual source variable identifier. -/
  name : String
  /-- Actual declared source type, including its argument order. -/
  type : typ

/-- Extract typed omitted declarations in their actual source order. -/
def variableDeclarations (spec : Lang.Al.spec) : Lang.Al.spec :=
  Refine.SourceProfile.variables spec

/-- Expose variable type obligations without assuming a codec or a runtime initial value. -/
def metadata (spec : Lang.Al.spec) : List Variable :=
  (variableDeclarations spec).filterMap fun d => match d.it with
    | .VarD name type _ => some ⟨name.it, type⟩
    | _ => none

/-- Compare the omitted quotation against the decoded source, preserving names/types/order.
The same region and hint erasure policy as ordinary quoted definitions applies. -/
def compareVariables (source quoted : Lang.Al.spec) : Except String Nat := do
  let expected := variableDeclarations source
  unless expected.length == quoted.length do
    throw s!"variable quotation length: expected {expected.length}, got {quoted.length}"
  for (a, b) in expected.zip quoted do
    unless QuoteCheck.sameDef a b do
      throw s!"variable quotation differs at {a.it.id.it}; got {b.it.id.it}"
  pure expected.length

/-- Exact compiled no-op claim type for the emitted, source-ordered variable quotation. -/
def variablesIgnoredType (lib : String) : String :=
  "∀ (g : Interp_al.Ctx.global), Interp_al.Ctx.load_defs g " ++
    lib ++ ".SourceProfile.variableDeclarations = .ok g"

/-- Minimal proof imports for the standalone omitted-declaration sidecar. -/
def supportImports : List String :=
  ["P4SpecTec.Refine.Quote", "P4SpecTec.Refine.Representation.SourceExtern",
   "P4SpecTec.Refine.Representation.SourcePrimitive", "P4SpecTec.Refine.SourceProfile",
   "P4SpecTec.Tactic.Audit"]

/-- Emit exact typed metadata and an audited no-op theorem for arbitrary initial globals. -/
def declarations (spec : Lang.Al.spec) : Format :=
  let variables := (Reify.lst ((variableDeclarations spec).map Reify.def')).fmt.pretty 1000000
  let facts := if (variableDeclarations spec).isEmpty then "variableDeclarations"
    else "variableDeclarations, Refine.SourceProfile.isVariable"
  Format.text <| boundedLines <| String.join [
    "namespace SourceProfile\n\n",
    "/-- Source-order typed metavariables, intentionally absent from the executable spec. -/\n",
    "def variableDeclarations : Lang.Al.spec := ", variables, "\n\n",
    "/-- Schematic declarations do not change any initial AL global table. -/\n",
    "theorem variablesIgnored (g : Interp_al.Ctx.global) :\n",
    "    Interp_al.Ctx.load_defs g variableDeclarations = .ok g :=\n",
    "  Refine.SourceProfile.loadVariables g variableDeclarations (by\n",
    s!"    simp [{facts}])\n\n",
    "#audit_axioms variablesIgnored\n\nend SourceProfile"]

/-- Exact compiled primitive profile type, with independent source grammar and legal children. -/
def primitiveType (lib : String) : String :=
  "Representation.Source.PrimitiveProfile " ++ lib ++ ".spec " ++
    "Representation.Source.externDomain"

/-- Emit the actual-spec binding of existing codecs, keeping producer/call obligations separate. -/
def primitiveDeclarations (lib : String) : Format :=
  Format.text <| boundedLines <| String.join [
    "namespace SourceProfile\n\n",
    "/-- Checked primitive codecs and contextual containers for the actual source grammar. -/\n",
    "theorem primitiveRepresentations : ", primitiveType lib, " :=\n",
    "  Representation.Source.primitiveProfile\n\n",
    "#audit_axioms primitiveRepresentations\n\nend SourceProfile"]

end P4SpecTec.Codegen.SourceProfiles
