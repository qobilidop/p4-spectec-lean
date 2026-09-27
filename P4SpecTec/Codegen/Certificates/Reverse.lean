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
    Format.line ++ "cfg.guard = false → ctx.local.fenv = [] →" ++
    Format.line ++ Format.text s!"HoldsSpec {lib}.spec ctx.global →" ++ raw ++ relations ++
    Format.line ++ "∃ r, EventuallyRuns " ++ reference m ++ " r ∧" ++
    Format.line ++ "ResRel " ++ Validate.resultRel m ++ " r q"))

/-- Emit a singleton recursive certificate using its actual outcome induction principle. -/
def recursiveTheorems (lib : String) (m : Member) : List Format := Id.run do
  let owner := m.localName.replace ".run" ""
  let qualified := m.defName.replace ".run" ""
  let motiveName := owner ++ ".realizesMotive"
  let ps := paramNames m.params.length
  let vs := (List.range m.params.length).map fun i => s!"v{i}"
  let hs := (List.range m.params.length).map fun i => s!"h{i}"
  let config := ["cfg", "ctx", "internal", "hguard", "hfenv", "hspec"]
  let args := config ++ vs ++ hs
  let motiveDef := Format.group (Format.nest 4 (
    Format.text ("private def " ++ motiveName) ++ paramBinders m.params ++
    Format.line ++ "(q : Except Fail " ++ m.ret.arg ++ ") : Prop :=")) ++
    Format.nest 2 (Format.line ++ motive lib m)
  let header := Format.group (Format.nest 4 (Format.text ("theorem " ++ owner ++ ".realizes") ++
    Format.line ++ Validate.binders lib m ++ " :" ++ Format.line ++ conclusion m ++ " := by"))
  let introArgs := ["rec", "ih"] ++ ps ++ ["q", "hq"] ++ args
  let finalArgs := ps ++ ["q", "hq"] ++ args
  let proof := Format.nest 2 (Format.line ++ "intro q hq" ++ Format.line ++
    Format.text ("exact " ++ m.defName ++ ".partial_correctness") ++
    Format.nest 2 (Format.line ++ Format.text ("(motive := " ++ motiveName ++ ") (by") ++
      Format.nest 2 (Format.line ++ Format.text ("intro " ++ " ".intercalate introArgs) ++
        Format.line ++ "realize_step hq)") ++
      Format.line ++ Format.text (" ".intercalate finalArgs)))
  return [motiveDef, header ++ proof, Validate.audit (qualified ++ ".realizes")]

/-- Emit reverse contracts for checked singleton groups; unsupported groups remain explicit. -/
def groupTheorems (lib : String) (recursive : Bool) (members : List Member)
    (reasons : List (String × String)) : List Format := Id.run do
  if !reasons.isEmpty then
    return reasons.map fun (id, reason) =>
      Format.text s!"-- no reverse theorem: {id}\n--   {reason}"
  if members.length > 1 then
    return members.map fun m =>
      Format.text s!"-- no reverse theorem: {m.id}\n--   " ++
        "mutual reverse induction is not implemented"
  if recursive then return members.flatMap (recursiveTheorems lib)
  return members.flatMap fun m =>
    let name := m.localName.replace ".run" "" ++ ".realizes"
    [Format.group (Format.nest 4 (Format.text ("theorem " ++ name) ++
        Format.line ++ Validate.binders lib m ++ " :" ++ Format.line ++ conclusion m ++
        " := by")) ++ Format.nest 2 (Format.line ++ "realize_al"),
      Validate.audit (m.defName.replace ".run" "" ++ ".realizes")]

end P4SpecTec.Codegen.Reverse
