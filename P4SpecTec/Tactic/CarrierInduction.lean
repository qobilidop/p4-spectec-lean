import Lean.Elab.Tactic.ElabTerm
import Lean.Meta.Tactic.Apply

/-!
Checked application of an actual native recursor with explicit carrier predicates.
Lean's nested-recursion motive order is read from the recursor declaration, rather
than reconstructed from a source grammar. All resulting minor premises remain
ordinary kernel-checked proof goals. This is our own proof support.
-/

namespace P4SpecTec.Tactic

open Lean Meta Elab Tactic

/-- Apply a parameter-free native recursor, matching its motives to explicit predicates.
Every motive must have a supplied predicate of its exact carrier type. Multiple matches
are accepted only when their predicates are definitionally equal; ambiguity fails closed. -/
elab "carrier_induction " recursor:ident " [" predicates:term,* "]" : tactic =>
    withoutRecover <| withMainContext do
  let name ← realizeGlobalConstNoOverloadWithInfo recursor
  let .recInfo info ← getConstInfo name | throwError "{name} is not a native recursor"
  unless info.numParams == 0 do
    throwError "carrier_induction requires a parameter-free native recursor"
  let candidates ← predicates.getElems.mapM fun predicate => elabTerm predicate none
  let candidateTypes ← candidates.mapM (fun candidate => inferType candidate)
  let eliminator := mkConst name (info.levelParams.map fun _ => Level.zero)
  let chosen ← forallBoundedTelescope (← inferType eliminator) (some info.numMotives)
      fun motives _ => do
    motives.mapM fun motive => do
      let expected ← inferType motive
      let mut selected := none
      for candidate in candidates, candidateType in candidateTypes do
        if ← isDefEq candidateType expected then
          match selected with
          | none => selected := some candidate
          | some prior =>
            unless ← isDefEq prior candidate do
              throwError "ambiguous carrier predicate for recursor motive {expected}"
      let some predicate := selected
        | throwError "no explicit carrier predicate for recursor motive {expected}"
      pure predicate
  let goals ← (← getMainGoal).apply (mkAppN eliminator chosen)
  replaceMainGoal goals

end P4SpecTec.Tactic
