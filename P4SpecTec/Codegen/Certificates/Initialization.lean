import Lean.Data.Format

/-!
Certificates for the initialized reference environment of a quoted specification.
These discharge global lookup and empty-local-table assumptions without importing
a downstream example. Source-domain and semantic program initialization are
separate obligations.
-/

namespace P4SpecTec.Codegen.Initialization

/-- Declarations for a concrete, checked environment of the generated quotation. -/
def declarations (lib : String) : Std.Format :=
  Std.Format.text <| String.join [
    "namespace Environment\n\n",
    s!"private theorem namesUnique : Refine.Init.NamesUnique {lib}.spec := by decide\n\n",
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
    "end Environment"]

end P4SpecTec.Codegen.Initialization
