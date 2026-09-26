import P4SpecTec.Lang.Al.Ast

/-! Complete ordered relation attempts shared by executable and proof generation. -/

namespace P4SpecTec.Codegen.Attempt

open P4SpecTec.Lang.Il P4SpecTec.Lang.Al

/-- One complete path, including its repeated group match and shared premises. -/
structure RelAttempt where
  /-- The source group identifier. -/
  groupId : id
  /-- The source path identifier. -/
  pathId : id
  /-- Input matching and shared premises, rerun for this attempt. -/
  match_ : rulematch
  /-- Path-specific premises. -/
  prems : List prem
  /-- Output expressions in order. -/
  outs : List exp

/-- Flatten in upstream sequential order, with the else path last. -/
def ofRelation (groups : List Lang.Al.rulegroup) (elsegroup : Option Lang.Al.elsegroup) :
    List RelAttempt :=
  let ofPath (groupId : id) (match_ : rulematch) (p : rulepath) : RelAttempt :=
    let (pathId, prems, outs) := p
    { groupId, pathId, match_, prems, outs }
  groups.flatMap (fun g =>
    let (i, m, ps) := g.it
    ps.map (ofPath i m)) ++
  match elsegroup with
  | none => []
  | some g => let (i, m, p) := g.it; [ofPath i m p]

end P4SpecTec.Codegen.Attempt
