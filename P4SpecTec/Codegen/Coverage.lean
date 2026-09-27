import Lean.Data.Json.FromToJson
import Lean.Data.Json.Printer

/-!
Deterministic metadata for the certificates emitted with a generated library.
This is an inventory, not proof evidence: `Coverage.Check` separately checks
the claims against compiled declarations and a freshly regenerated report.
Callable definitions and source type representations have separate inventories,
so equal names in separate source namespaces cannot collide. Source profiles
account for cross-cutting claims. Recursion groups share refinement exclusions.
-/

namespace P4SpecTec.Codegen.Coverage

open Lean

/-- An emitted per-definition theorem; helper group theorems are not counted. -/
structure Claim where
  /-- Fully qualified Lean name, in Lean source syntax. -/
  name : String
  /-- The checked contract family, including invocation, source entry and representation. -/
  kind : String
  /-- The checked direction or dispatch equality; not an unqualified equivalence claim. -/
  direction : String
  /-- Closed expected type, elaborated in the generated library's namespace. -/
  expectedType : String
  deriving BEq, FromJson, ToJson, Inhabited

/-- A reason a theorem is not emitted, possibly inherited from an SCC peer. -/
structure Exclusion where
  /-- The theorem kind whose generation is blocked. -/
  kind : String := "refinement"
  /-- The group member at which the obstruction occurs. -/
  definition : String
  /-- The planner's explanation; not a claim of semantic impossibility. -/
  reason : String
  /-- The direct callee whose missing theorem causes the obstruction, if any. -/
  dependency : Option String := none
  deriving BEq, FromJson, ToJson, Inhabited

/-- One declaration and its emitted certificates, stored in its source namespace. -/
structure Entry where
  /-- Original AL identifier, without Lean escaping or the function `$` prefix. -/
  id : String
  /-- Callable kind, or `type`/`externType` in the representation inventory. -/
  kind : String
  /-- Source spec file recorded in the AL export. -/
  source : String
  /-- Strongly connected component, including this definition. -/
  group : List String
  /-- Whether the component requires recursive generation. -/
  recursive : Bool
  /-- Direct dependencies within this declaration namespace. -/
  dependencies : List String
  /-- Emitted claims, not a cached assertion that Lean has checked them. -/
  claims : List Claim
  /-- Missing theorem reasons, including shared recursion-group obstructions. -/
  exclusions : List Exclusion
  deriving BEq, FromJson, ToJson, Inhabited

/-- Versioned report for one generated library and AL export. -/
structure Report where
  /-- Bump when changing the report contract. -/
  schemaVersion : Nat := 3
  /-- Generated Lean library namespace. -/
  library : String
  /-- Export path passed to the generator; provenance, not a content digest. -/
  input : String
  /-- Callable definitions in deterministic planner order. -/
  definitions : List Entry
  /-- Source type declarations and their checked codec claims, in a separate namespace. -/
  representations : List Entry := []
  /-- Cross-cutting source-profile claims, separately checked against compiled theorem types. -/
  profiles : List Claim := []
  deriving BEq, FromJson, ToJson, Inhabited

/-- Stable JSON text used by the ordinary generator freshness check. -/
def Report.render (report : Report) : String := (toJson report).pretty ++ "\n"

/-- Whether a per-definition forward AL theorem is emitted. -/
def Entry.hasForwardRefinement (entry : Entry) : Bool :=
  entry.claims.any fun claim =>
    claim.kind == "refinement" && claim.direction == "referenceToGenerated"

/-- Whether a per-definition eventual reverse AL theorem is emitted. -/
def Entry.hasReverseRefinement (entry : Entry) : Bool :=
  entry.claims.any fun claim =>
    claim.kind == "refinement" && claim.direction == "generatedToReference"

/-- Whether an operation-specific equality of actual dispatch and wrapper outcomes is emitted. -/
def Entry.hasBuiltinContract (entry : Entry) : Bool :=
  entry.claims.any fun claim =>
    claim.kind == "builtinContract" && claim.direction == "twoWayDispatch"

/-- Bodied definitions used as the refinement denominator, excluding externs/builtins. -/
def Entry.isBodied (entry : Entry) : Bool :=
  ["function", "relation", "table"].contains entry.kind

private def reasonLines (reason : String) : List String := Id.run do
  let commentPrefix := "    --   "
  let mut result := []
  let mut current := commentPrefix
  for word in reason.splitOn " " do
    if current.length > commentPrefix.length && current.length + word.length + 1 > 100 then
      result := result ++ [current]
      current := commentPrefix ++ word
    else
      current := current ++ (if current == commentPrefix then "" else " ") ++ word
  return result ++ [current]

/-- Human-readable refinement index, derived from the same entries as the JSON. -/
def summary (entries : List Entry) : String := Id.run do
  let bodied := entries.filter Entry.isBodied
  let covered := bodied.filter Entry.hasForwardRefinement
  let reverse := bodied.filter Entry.hasReverseRefinement
  let builtins := entries.filter (·.kind == "builtin")
  let contracts := builtins.filter Entry.hasBuiltinContract
  let mut lines := [
    s!"-- forward refinement theorems: {covered.length} of {bodied.length} definitions",
    s!"-- reverse realization theorems: {reverse.length} of {bodied.length} definitions",
    s!"-- builtin dispatch contracts: {contracts.length} of {builtins.length} definitions"]
  for entry in bodied do
    if entry.hasForwardRefinement then continue
    let reasons := entry.exclusions.filter (·.kind == "refinement")
    lines := lines ++ ["", s!"-- no refinement theorem: {entry.id}"]
    for reason in reasons do
      let origin := if reason.definition == entry.id then ""
        else s!"group member {reason.definition}: "
      lines := lines ++ reasonLines (origin ++ reason.reason)
  for entry in bodied do
    if !entry.hasForwardRefinement || entry.hasReverseRefinement then continue
    lines := lines ++ ["", s!"-- no reverse theorem: {entry.id}"]
    for reason in entry.exclusions.filter (·.kind == "realization") do
      lines := lines ++ reasonLines reason.reason
  for entry in builtins do
    if entry.hasBuiltinContract then continue
    lines := lines ++ ["", s!"-- no builtin dispatch contract: {entry.id}"]
    for reason in entry.exclusions do
      lines := lines ++ reasonLines reason.reason
  "\n".intercalate lines

/-- Reachable callable dependencies and SCC peers; cycles are visited once.
Unknown identifiers fail rather than silently appearing covered. -/
def closure (report : Report) (entryPoint : String) : Except String (List Entry) := do
  let mut pending := [entryPoint]
  let mut seen : List String := []
  let mut entries : List Entry := []
  -- Each visit enqueues at most all stored edges and component members once.
  let bound := 1 + (report.definitions.map fun e =>
    e.dependencies.length + e.group.length).sum
  for _ in List.range (bound + 1) do
    match pending with
    | [] => return entries
    | name :: rest =>
      pending := rest
      if seen.contains name then continue
      let some entry := report.definitions.find? (·.id == name)
        | throw s!"unknown coverage definition: {name}"
      seen := seen ++ [name]
      entries := entries ++ [entry]
      pending := pending ++ entry.dependencies ++ entry.group
  throw "coverage dependency traversal exceeded its edge bound"

/-- Explain the selected entry and its dependency closure without asserting a proof. -/
def explain (report : Report) (entryPoint : String) : Except String String := do
  let entries ← closure report entryPoint
  let lines := entries.map fun entry =>
    let forward := if entry.hasForwardRefinement then "forward AL theorem emitted"
      else "no forward AL theorem"
    let reverse := if entry.hasReverseRefinement then "reverse AL theorem emitted"
      else "no reverse AL theorem"
    let status := forward ++ "; " ++ reverse
    let reasons := (entry.exclusions.filter (·.kind == "refinement")).map fun r =>
      s!"    {r.definition}: {r.reason}"
    "\n".intercalate (s!"  {entry.id}: {status}" :: reasons)
  pure (s!"{entryPoint}: {entries.length} reachable callable definitions/SCC members\n" ++
    "\n".intercalate lines)

end P4SpecTec.Codegen.Coverage
