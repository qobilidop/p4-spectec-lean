import P4SpecTec.Interface.Builtin.Maps
import P4SpecTec.Tactic.Audit

/-! Actual ordered map operations preserve independently supplied key/value domains. -/

namespace P4SpecTec.Refine.ProducerMap
open P4SpecTec.Prelude

/-- Replacing the first matching pair or appending retains every pair's domain.
No equality law is needed: either branch preserves exactly the established predicate. -/
theorem update {K V : Type} [ToValue K] (domain : K × V → Prop)
    (pairs : List (K × V)) (key : K) (value : V)
    (prior : ∀ pair ∈ pairs, domain pair) (replacement : domain (key, value)) :
    ∀ pair ∈ Builtin.Maps.update key value pairs, domain pair := by
  induction pairs with
  | nil => simpa only [Builtin.Maps.update, List.mem_singleton] using
      (fun pair (same : pair = (key, value)) => same ▸ replacement)
  | cons head tail ih =>
    rcases head with ⟨oldKey, oldValue⟩
    simp only [Builtin.Maps.update]
    split
    · intro pair member
      rcases List.mem_cons.mp member with rfl | member
      · exact replacement
      · exact prior pair (List.mem_cons_of_mem _ member)
    · intro pair member
      rcases List.mem_cons.mp member with rfl | member
      · exact prior _ (List.mem_cons_self)
      · exact ih (fun pair member => prior pair (List.mem_cons_of_mem _ member)) pair member

/-- info: 'P4SpecTec.Refine.ProducerMap.update' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms update
#audit_axioms update

end P4SpecTec.Refine.ProducerMap
