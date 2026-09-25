import P4SpecTec.Lang.Al.Ast

/-!
Relations as the AL interpreter stores them. Mirrors
`p4spec/lib/runtime/dynamic-al/rel.ml`.
-/

namespace P4SpecTec.Runtime.Dynamic_al.Rel

open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al

/-- Mirrors `Rel.t`. -/
inductive t where
  /-- An extern relation: its notation and input positions. -/
  | Extern (nottyp : nottyp) (inputs : Hints.Input.t)
  /-- A defined relation: its notation, input positions and rules. -/
  | Defined (nottyp : nottyp) (inputs : Hints.Input.t) (rulegroups : List Lang.Al.rulegroup)
      (elsegroup : Option Lang.Al.elsegroup)

/-- Mirrors `to_string`. -/
def to_string : t → String
  | .Extern .. => "extern relation"
  | .Defined .. => "defined relation"

/-- Mirrors `get_signature`. -/
def get_signature : t → nottyp × Hints.Input.t
  | .Extern nottyp inputs => (nottyp, inputs)
  | .Defined nottyp inputs _ _ => (nottyp, inputs)

end P4SpecTec.Runtime.Dynamic_al.Rel
