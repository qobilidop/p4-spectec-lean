import NanoP4Spec.Refinement.Spec
import P4SpecTec.Tactic.Realize

/-!
Regression for canonical equality decisions during reverse symbolic execution.
The fact must preserve the `Realizes` goal rather than introducing its outcome
quantifier as though that were a canonical-inequality side condition.
-/

open Lean Elab Tactic P4SpecTec P4SpecTec.Refine P4SpecTec.Prelude P4SpecTec.Tactic

-- The normalization rules select the generated library from the theorem namespace.
namespace NanoP4Spec

theorem reverseGuard.realizes :
    Realizes Rel (fun _ => pure (toValue true))
      (if Runtime.Value.eq (toValue direction.IN) (toValue direction._EMPTY) = false
       then pure true else throw Fail.unmatch) := by
  run_tac withoutRecover do
    let s ← prepareSimpSet (← simpSet)
    let _ ← normalize s
    let (_, _, generated) ← Realize.goalParts
    unless ← Realize.alignTests s generated generated do
      throwError "canonical inequality was not aligned"
  apply Realizes.pure
  rfl

/-- info: 'NanoP4Spec.reverseGuard.realizes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms reverseGuard.realizes

end NanoP4Spec

namespace P4SpecTecTest.Refine.Reverse

-- Raw extern payloads retain canonical facts after their enclosing value is exposed.
theorem rawPayloadFact (v : Lang.Il.value) (payload : Lean.Json)
    (h : canon' v.it = .ExternV payload) : (canon v).it = .ExternV payload := by
  run_tac withoutRecover do
    let s ← prepareSimpSet { lemmas := #[``canon_it], procs := #[] }
    let _ ← normalize s
    unless (← getGoals).isEmpty do throwError "canonical payload fact was ignored"

/-- info: 'P4SpecTecTest.Refine.Reverse.rawPayloadFact' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rawPayloadFact

end P4SpecTecTest.Refine.Reverse
