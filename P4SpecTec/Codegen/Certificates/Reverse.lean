import P4SpecTec.Codegen.Certificates.Forward

/-!
Reverse certificates construct eventual executions of the actual quoted interpreter.
Recursive definitions use the generated partial fixed point's outcome induction;
neither forward refinement nor determinism supplies the reverse witness.
-/

namespace P4SpecTec.Codegen.Reverse

open Std (Format)
open P4SpecTec.Codegen.Types P4SpecTec.Codegen.Exp P4SpecTec.Codegen.Props
open P4SpecTec.Codegen.Funcs

/-- The actual reference invocation, abstracted over its fuel. -/
def reference (m : Member) : Format :=
  Format.paren (Format.text "fun fuel => " ++ Validate.invocation m)

/-- The reverse contract includes every defined generated outcome, including failures. -/
def conclusion (m : Member) : Format :=
  Format.group (Format.nest 2 (Format.text "Realizes " ++ Validate.resultRel m ++
    Format.line ++ reference m ++ Format.line ++ Validate.generated m))

/-- The exact closed type shared by emission and compiled certificate checking. -/
def realizationType (lib : String) (m : Member) : Format :=
  Format.group (Format.nest 4 (Format.text "∀ " ++ Validate.binders lib m ++ "," ++
    Format.line ++ conclusion m))

/-- A reverse motive quantifies environments and raw related inputs after the outcome. -/
def motive (lib : String) (m : Member) : Format := Id.run do
  let values := (List.range m.params.length).map fun i => s!"v{i}"
  let raw := if values.isEmpty then Format.nil else
    Format.line ++ Format.text ("∀ (" ++ " ".intercalate values ++ " : Lang.Il.value),")
  let relations := Format.join ((List.range m.params.length).map fun i =>
    Format.line ++ Format.text s!"Rel v{i} p{i} →")
  return Format.group (Format.nest 2 (
    Format.text "∀ (cfg : Interp_al.Interp.Config) (ctx : Interp_al.Ctx.t) (internal : Bool)," ++
    Format.line ++ "cfg.guard = false → " ++
    (if m.printHints then Format.text "cfg.printHints = [] → " else Format.nil) ++
    "ctx.local.fenv = [] →" ++
    Format.line ++ Format.text s!"HoldsSpec {lib}.spec ctx.global →" ++
    Format.join (m.typeFreshness.map fun name =>
      Format.line ++ Format.text s!"ctx.global.tdtbl.get? {name.quote} = none →") ++
    raw ++ relations ++
    Format.line ++ "∃ r, EventuallyRuns " ++ reference m ++ " r ∧" ++
    Format.line ++ "ResRel " ++ Validate.resultRel m ++ " r q"))

/-- Space-separated words that break across lines within the column limit. -/
private def words (head : String) (items : List String) : Format :=
  let parts := (if head.isEmpty then [] else [head]) ++ items
  Format.fill (Format.nest 4 (Format.joinSep (parts.map Format.text) Format.line))

/-- Emit a singleton recursive certificate using its actual outcome induction principle. -/
def recursiveTheorems (lib : String) (m : Member) : List Format := Id.run do
  let owner := m.localName.replace ".run" ""
  let qualified := m.defName.replace ".run" ""
  let motiveName := owner ++ ".realizesMotive"
  let ps := paramNames m.params.length
  let vs := (List.range m.params.length).map fun i => s!"v{i}"
  let hs := (List.range m.params.length).map fun i => s!"h{i}"
  let fresh := (List.range m.typeFreshness.length).map fun i => s!"ht{i}"
  let args := Validate.configArguments m ++ fresh ++ vs ++ hs
  let motiveDef := Format.group (Format.nest 4 (
    Format.text ("private def " ++ motiveName) ++ paramBinders m.params ++
    Format.line ++ "(q : Except Fail " ++ m.ret.arg ++ ") : Prop :=")) ++
    Format.nest 2 (Format.line ++ motive lib m)
  let header := Format.group (Format.nest 4 (Format.text ("theorem " ++ owner ++ ".realizes") ++
    Format.line ++ Validate.binders lib m ++ " :" ++ Format.line ++ conclusion m ++ " := by"))
  let introArgs := ["rec", "ih"] ++ ps ++ ["q", "hq"] ++ args
  let finalArgs := ps ++ ["q", "hq"] ++ args
  let step := if m.requiresColumns then "realize_step (columns) hq)"
    else if m.isRel || m.requiresTypeRules || m.requiresStructureRules then
      "realize_step (relations) hq)"
    else "realize_step hq)"
  let proof := Format.nest 2 (Format.line ++ "intro q hq" ++ Format.line ++
    Format.text ("exact " ++ m.defName ++ ".partial_correctness") ++
    Format.nest 2 (Format.line ++ Format.text ("(motive := " ++ motiveName ++ ") (by") ++
      Format.nest 2 (Format.line ++ words "intro" introArgs ++
        Format.line ++ Format.text step) ++
      Format.line ++ words "" finalArgs))
  return [motiveDef, header ++ proof, Validate.audit (qualified ++ ".realizes")]

/-- A member's outcome-indexed statement for joint fixed-point induction. -/
def groupStatement (lib : String) (m : Member) : Format :=
  let ps := paramNames m.params.length
  Format.group (Format.nest 2 (Format.text "∀" ++ paramBinders m.params ++
    Format.line ++ "(q : Except Fail " ++ m.ret.arg ++ ")," ++
    Format.line ++ (Term.call m.defName (ps.map Term.atom)).fmt ++ " = some q →" ++
    Format.line ++ motive lib m))

/-- Joint reverse induction, followed by exact per-member realization corollaries. -/
def mutualTheorems (lib : String) (members : List Member) : List Format := Id.run do
  let first := members.head!
  let owner := first.localName.replace ".run" ""
  let qualified := first.defName.replace ".run" ""
  let groupName := qualified ++ ".realizes_group"
  let statement := Format.joinSep (members.map fun m => Format.paren (groupStatement lib m))
    (Format.text " ∧" ++ Format.line)
  let declaration := Format.text ("theorem " ++ owner ++ ".realizes_group :") ++
    Format.nest 2 (Format.line ++ statement) ++ " := by" ++
    Format.nest 2 (Format.line ++ Format.text
      ("realize_group " ++ first.defName ++ ".mutual_partial_correctness"))
  let mut result := [declaration, Validate.audit groupName]
  for (m, i) in members.zipIdx do
    let name := m.localName.replace ".run" "" ++ ".realizes"
    let projection := groupName ++ String.join ((List.range i).map fun _ => ".2") ++
      (if i == members.length - 1 then "" else ".1")
    let ps := paramNames m.params.length
    let vs := (List.range m.params.length).map fun i => s!"v{i}"
    let hs := (List.range m.params.length).map fun i => s!"h{i}"
    let fresh := (List.range m.typeFreshness.length).map fun i => s!"ht{i}"
    let args := ps ++ ["q", "hq"] ++ Validate.configArguments m ++ fresh ++ vs ++ hs
    result := result ++ [
      Format.group (Format.nest 4 (Format.text ("theorem " ++ name) ++
        Format.line ++ Validate.binders lib m ++ " :" ++ Format.line ++ conclusion m ++
        " := by")) ++ Format.nest 2 (Format.line ++ "intro q hq" ++
          Format.line ++ Format.group (Format.nest 2 (Format.text ("exact " ++ projection) ++
            Format.line ++ Format.joinSep (args.map Format.text) Format.line))),
      Validate.audit (m.defName.replace ".run" "" ++ ".realizes")]
  return result

/-- Select the source-derived observation relation for a nonrecursive traversal. -/
def bodyTactic (m : Member) : Format :=
  if m.requiresColumns then "realize_al (columns)" else
  match m.iterationRelation with
  | none => if m.requiresTypeRules || m.requiresStructureRules then "realize_al (subtypes)"
    else "realize_al"
  | some relation => Format.group (Format.nest 2 (
      Format.text "realize_al (iteration :=" ++ Format.line ++ relation ++ ")"))

/-- Emit reverse contracts for supported definitions, using joint induction for mutual groups. -/
def groupTheorems (lib : String) (recursive : Bool) (members : List Member)
    (reasons : List (String × String)) : List Format := Id.run do
  if !reasons.isEmpty then
    return reasons.map fun (id, reason) =>
      Format.text s!"-- no reverse theorem: {id}\n--   {reason}"
  if members.length > 1 then return mutualTheorems lib members
  if recursive then return members.flatMap (recursiveTheorems lib)
  return members.flatMap fun m =>
    let name := m.localName.replace ".run" "" ++ ".realizes"
    [Format.group (Format.nest 4 (Format.text ("theorem " ++ name) ++
        Format.line ++ Validate.binders lib m ++ " :" ++ Format.line ++ conclusion m ++
        " := by")) ++ Format.nest 2 (Format.line ++ bodyTactic m),
      Validate.audit (m.defName.replace ".run" "" ++ ".realizes")]

end P4SpecTec.Codegen.Reverse
