import P4SpecTec.Codegen.Names
import P4SpecTec.Lang.Al.Ast

/-!
Certificates for the initialized reference environment of a quoted specification.
These discharge global lookup and empty-local-table assumptions without importing
a downstream example. Source-domain and semantic program initialization are
separate obligations.
-/

namespace P4SpecTec.Codegen.Initialization

/-- Declarations for a concrete, checked environment of the generated quotation. -/
def declarations (lib : String) (spec : Lang.Al.spec := []) : Std.Format :=
  let typeNames := spec.filterMap fun d => match d.it with
    | .TypD id .. | .ExternTypD id .. => some id.it
    | _ => none
  let parameterNames := (spec.flatMap fun d => match d.it with
    | .FuncDecD _ ps .. | .BuiltinDecD _ ps .. | .ExternDecD _ ps .. => ps.map (·.it)
    | _ => []).eraseDups.filter fun name => !typeNames.contains name
  let freshness := String.join <| parameterNames.map fun name =>
    let theoremName := "typeParameterFresh_" ++ Names.typeName name
    String.join [
      "/-- The initialized type table leaves this callable parameter name fresh. -/\n",
      s!"theorem {theoremName} : global.tdtbl.get? {name.quote} = none :=\n",
      s!"  Refine.Init.globalTypeAbsent {lib}.spec {name.quote} (by decide)\n\n",
      s!"#audit_axioms {theoremName}\n\n"]
  Std.Format.text <| String.join [
    "namespace Environment\n\n",
    s!"private theorem namesUnique : Refine.Init.NamesUnique {lib}.spec := by decide\n\n",
    "#audit_axioms namesUnique\n\n",
    "/-- The concrete global tables of the complete generated quotation. -/\n",
    s!"def global : Interp_al.Ctx.global := Refine.Init.global {lib}.spec\n\n",
    "/-- Checked AL table initialization succeeds for the quoted specification. -/\n",
    s!"theorem initEqOk : Interp_al.Ctx.init {lib}.spec = .ok global :=\n",
    "  Refine.Init.initEqOk _ namesUnique\n\n",
    "#audit_axioms initEqOk\n\n",
    "/-- The initialized global tables contain every quoted definition. -/\n",
    s!"theorem holdsSpec : Refine.HoldsSpec {lib}.spec global :=\n",
    "  Refine.holdsSpec_of_init initEqOk\n\n",
    "#audit_axioms holdsSpec\n\n",
    "/-- An initial context with no local bindings or function overrides. -/\n",
    "def ctx : Interp_al.Ctx.t := Interp_al.Ctx.empty global\n\n",
    "/-- The initialized context satisfies the no-local-override hypothesis. -/\n",
    "theorem localFenvEmpty : ctx.local.fenv = [] := rfl\n\n",
    "#audit_axioms localFenvEmpty\n\n",
    freshness, "end Environment"]

end P4SpecTec.Codegen.Initialization
