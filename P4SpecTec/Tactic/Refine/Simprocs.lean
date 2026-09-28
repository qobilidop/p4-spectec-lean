import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.LitValues
import P4SpecTec.Interp.InterpAl.Interp

/-!
Guarded unfolding of interpreter equations for the refinement drivers. An unconditional
successor-fuel equation also fires on patterns bound inside a traversal of unknown values;
there it only multiplies the goal, once per available fuel level, without progress.
-/

namespace P4SpecTec.Tactic

open Lean Meta Simp
open P4SpecTec.Interp_al

/-- The predecessor of a successor fuel: `n + k` for a positive literal `k` (normalization
merges successive successors), `Nat.succ n` or a positive literal. -/
def fuelPredecessor? (fuel : Expr) : MetaM (Option Expr) := do
  let fuel := fuel.consumeMData
  if fuel.isAppOfArity ``HAdd.hAdd 6 then
    match ← getNatValue? (fuel.getArg! 5).consumeMData with
    | some 1 => return some (fuel.getArg! 4)
    | some (k + 1) => return some (← mkAdd (fuel.getArg! 4) (mkNatLit k))
    | _ => pure ()
  if fuel.isAppOfArity ``Nat.succ 1 then return some (fuel.getArg! 0)
  if let some (k + 1) ← getNatValue? fuel then return some (mkNatLit k)
  return none

/-- Unfold `f (n + 1) ctx x value` by its successor equation `equation` only when `x` is a
concrete quoted phrase, whose payload the equation's `match` then inspects. The functions
guarded this way share the argument layout `{m} [Effects m] fuel ctx phrase value`. -/
def guardedUnfold (equation : Name) (e : Expr) : SimpM Step := do
  let args := e.getAppArgs
  unless args.size == 6 do return .continue
  let some n ← fuelPredecessor? args[2]! | return .continue
  let phrase ← whnfR args[4]!
  unless phrase.isAppOf ``P4SpecTec.Util.Source.info.mk do return .continue
  let unfolded ← mkAppOptM equation #[args[0]!, args[1]!, args[3]!, args[4]!, args[5]!, n]
  let some (_, _, rhs) := (← inferType unfolded).eq? | return .continue
  let proof ← mkExpectedTypeHint unfolded (← mkEq e rhs)
  return .visit { expr := rhs, proof? := some proof }

/-- Assignment to a concrete quoted pattern. -/
simproc_decl assignExpConcrete (Interp.assign_exp _ _ _ _) :=
  guardedUnfold ``Interp.assign_exp.eq_2

/-- A downcast to a concrete quoted type. -/
simproc_decl downcastConcrete (Interp.downcast _ _ _ _) :=
  guardedUnfold ``Interp.downcast.eq_2

/-- An upcast to a concrete quoted type. -/
simproc_decl upcastConcrete (Interp.upcast _ _ _ _) :=
  guardedUnfold ``Interp.upcast.eq_2

end P4SpecTec.Tactic
