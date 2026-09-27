import P4SpecTec.Runtime.Type.SubstDepth

/-! Checked substitution crosses the old cutoff and retains explicit error behavior. -/

namespace P4SpecTecTest.Runtime.Type.SubstDepth

open P4SpecTec P4SpecTec.Lang.Il P4SpecTec.Util.Source P4SpecTec.Runtime.Type

private def nested : Nat → typ → typ
  | 0, t => t
  | n + 1, t => mkPhrase (.IterT (nested n t) .List)

private def boolLeaf : typ → Bool
  | ⟨.BoolT, _, _⟩ => true
  | ⟨.IterT t .List, _, _⟩ => boolLeaf t
  | _ => false

private def sourceVar : typ := mkPhrase (.VarT (mkPhrase "X") [])
private def theta : Subst.theta := [("X", mkPhrase .BoolT)]
private def deep := nested 1100 sourceVar

#guard (Subst.subst_typ_checked Subst.fuel theta deep).run.isNone
#guard match (Subst.substType theta deep).run with
  | some (.ok t) => boolLeaf t && Subst.syntaxDepth t == 1101
  | _ => false
#guard match (Subst.substTypes theta [sourceVar, deep]).run with
  | some (.ok ts) => ts.length == 2 && ts.all boolLeaf
  | _ => false

-- Substitution is simultaneous: a replacement containing X is returned as is.
#guard match (Subst.substType [("X", deep)] sourceVar).run with
  | some (.ok t) => !boolLeaf t && Subst.syntaxDepth t == 1101
  | _ => false

#guard match (Subst.substType theta (mkPhrase (.VarT (mkPhrase "X") [deep]))).run with
  | some (.error msg) => msg == "higher-order substitution is disallowed"
  | _ => false
#guard match (Subst.substType theta (mkPhrase (.FuncT [] [] sourceVar))).run with
  | some (.error msg) => msg == "function-type substitution requires type-fresh state"
  | _ => false

end P4SpecTecTest.Runtime.Type.SubstDepth
