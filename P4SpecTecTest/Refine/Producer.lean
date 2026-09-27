import P4SpecTec.Refine.Producer

/-! Producer domains constrain successes without erasing ordered failure behavior. -/

namespace P4SpecTecTest.Refine.Producer
open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

-- A hard error stops before an invalid successful fallback, so the whole computation
-- still satisfies any success-only invariant. A mismatch reaches that fallback.
example : Produces (fun n : Nat => n = 0)
    (Eval.orElse (throw .err) (pure 1)) := Produces.error _ _

example : ¬Produces (fun n : Nat => n = 0)
    (Eval.orElse (throw .unmatch) (pure 1)) := by
  intro valid
  have invalid := valid 1 rfl
  contradiction

-- Standard list encoding preserves an independently chosen source domain elementwise.
example {α : Type} [ToValue α] (spec : Lang.Al.spec)
    (externalDomain : String → Lang.Il.value → Prop) (element : Lang.Il.typ) (xs : List α)
    (valid : ∀ x ∈ xs,
      Representation.Source.Valid spec externalDomain element.it (toValue x)) :
    Representation.Source.Valid spec externalDomain (.IterT element .List) (toValue xs) :=
  (Representation.Source.encodedListIff element xs).mpr valid

end P4SpecTecTest.Refine.Producer
