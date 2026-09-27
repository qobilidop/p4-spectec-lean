import P4SpecTec.Codegen.Types

/-!
Equality certificates for generated type dictionaries. Generated `BEq` compares
encoded observations, so no injectivity or equality law for a type parameter is
needed. These instances belong in a proof sidecar, keeping proof support out of
the executable specification modules.
-/

namespace P4SpecTec.Codegen.EqualityCertificates

open Std (Format)
open P4SpecTec.Codegen.Types

/-- Certify each actual generated dictionary, including aliases and recursive types. -/
def declarations (env : Env) (spec : Lang.Al.spec) : Format :=
  joinDecls <| spec.filterMap fun d => match d.it with
    | .TypD id params _ _ =>
      let ps := params.map (·.it)
      let name := Names.typeName id.it ++ ".valueBEq"
      some <| Format.group (Format.nest 4 (
        Format.text s!"instance {name}" ++ tparamImplicits ps ++ tparamInstances ps ++
        " :" ++ Format.line ++ "Refine.Representation.ValueBEq " ++
        (selfType env id.it ps).arg ++ " :=" ++ Format.line ++
        "Refine.Representation.ValueBEq.ofValueEq")) ++
        Term.hardLine ++ Term.hardLine ++ Format.text s!"#audit_axioms {name}"
    | _ => none

end P4SpecTec.Codegen.EqualityCertificates
