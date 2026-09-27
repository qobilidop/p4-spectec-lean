import P4SpecTec.Interp.InterpAl.Interp
import Lean.Elab.GuardMsgs

/-! Exact checked mixfix-subtype execution, independent of recursive membership or type lookup. -/

namespace P4SpecTec.Refine

open P4SpecTec.Lang.Il P4SpecTec.Prelude P4SpecTec.Interp_al P4SpecTec.Runtime.Value

/-- A positive-fuel mixfix check inspects only the outer constructor notation.
It neither looks up types nor recursively validates constructor arguments. -/
theorem checkedMixop (types : Match.FindTypdef) (functions : Match.FindFuncChecked)
    (fuel : Nat) (mixops : List Lang.Il.mixop) (v : value) :
    Interp.checked_type (Match.check_checked types functions (fuel + 1) (.MixopSC mixops) v) =
      (pure (match v.it with
        | .CaseV c => mixops.any fun op => Domain.Mixfix.eq_mixop op c
        | _ => false) : Eval Bool) := by
  cases v with
  | mk payload note region => cases payload <;> rfl

/-- info: 'P4SpecTec.Refine.checkedMixop' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkedMixop

/-- Successful checked type computation preserves its value when lifted to evaluation. -/
theorem checkedTypePure {α : Type} (v : α) :
    Interp.checked_type (pure v) = (pure v : Eval α) := rfl

/-- info: 'P4SpecTec.Refine.checkedTypePure' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms checkedTypePure

/-- Running a successful checked computation returns its exact value. -/
theorem checkedPureRun {α : Type} (v : α) :
    ExceptT.run (pure v : Runtime.Type.Subst.Checked α) = some (.ok v) := rfl

/-- info: 'P4SpecTec.Refine.checkedPureRun' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms checkedPureRun

/-- A positive-fuel recursive natural check preserves the reference numeric-tag rule.
Integer-tag values are accepted exactly when nonnegative; metadata is unrestricted. -/
theorem checkedRecurseNat (types : Match.FindTypdef) (functions : Match.FindFuncChecked)
    (fuel : Nat) (type : typ) (natural : type.it = .NumT .NatT) (v : value) :
    Interp.checked_type (Match.check_checked types functions (fuel + 1)
      (.RecurseSC type) v) =
      (pure (match v.it with
        | .NumV (.Nat _) => true
        | .NumV (.Int i) => decide (i ≥ 0)
        | _ => false) : Eval Bool) := by
  cases type with
  | mk payload note region =>
    cases natural
    rw [Match.check_checked.eq_def]
    simp only [Match.sub_checked.eq_def, Match.fuel]
    exact checkedTypePure _

/-- info: 'P4SpecTec.Refine.checkedRecurseNat' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms checkedRecurseNat

end P4SpecTec.Refine
