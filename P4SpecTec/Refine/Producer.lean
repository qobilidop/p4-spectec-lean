import P4SpecTec.Prelude.Eval
import P4SpecTec.Refine.Representation.SourceObservation

/-!
Successful producer results preserve independent source domains. These contracts do not
assert termination or suppress failure outcomes; invocation correspondence remains separate.
-/

namespace P4SpecTec.Refine
open P4SpecTec.Prelude

/-- Every successful finite result belongs to an independently supplied output domain.
Divergence and failures impose no successful-value obligation. -/
def Produces {α : Type} (domain : α → Prop) (computation : Eval α) : Prop :=
  ∀ value, computation.run = some (.ok value) → domain value

/-- A pure producer preserves its established output-domain fact. -/
theorem Produces.pure {α : Type} {domain : α → Prop} {value : α}
    (valid : domain value) : Produces domain (pure value) := by
  intro output run
  have same : value = output := Except.ok.inj (Option.some.inj run)
  exact same ▸ valid

/-- info: 'P4SpecTec.Refine.Produces.pure' does not depend on any axioms -/
#guard_msgs in #print axioms Produces.pure
#audit_axioms Produces.pure

/-- An actual failure has no successful value to admit. -/
theorem Produces.error {α : Type} (domain : α → Prop) (error : Fail) :
    Produces domain (throw error) := by
  intro output run
  cases Option.some.inj run

/-- info: 'P4SpecTec.Refine.Produces.error' does not depend on any axioms -/
#guard_msgs in #print axioms Produces.error
#audit_axioms Produces.error

/-- Bind retains the actual intermediate admission required by its continuation. -/
theorem Produces.bind {α β : Type} {input : α → Prop} {output : β → Prop}
    {m : Eval α} {k : α → Eval β} (first : Produces input m)
    (next : ∀ value, input value → Produces output (k value)) :
    Produces output (m >>= k) := by
  intro value run
  obtain ⟨intermediate, found, result⟩ := Eval.run_bind_ok.mp run
  exact next intermediate (first intermediate found) value result

/-- info: 'P4SpecTec.Refine.Produces.bind' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Produces.bind
#audit_axioms Produces.bind

/-- A continuation may preserve its output domain for every successful intermediate value.
This establishes output preservation only, not source validity at the intermediate call. -/
theorem Produces.bindAny {α β : Type} {output : β → Prop} {m : Eval α} {k : α → Eval β}
    (next : ∀ value, Produces output (k value)) : Produces output (m >>= k) :=
  Produces.bind (input := fun _ => True) (fun _ _ => trivial) (fun value _ => next value)

/-- info: 'P4SpecTec.Refine.Produces.bindAny' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Produces.bindAny
#audit_axioms Produces.bindAny

/-- Ordered choice retains the domain of both successful branches.
The actual mismatch-only retry condition comes from the evaluation rule. -/
theorem Produces.orElse {α : Type} {domain : α → Prop} {a b : Eval α}
    (left : Produces domain a) (right : Produces domain b) :
    Produces domain (Eval.orElse a b) := by
  intro value run
  rcases Eval.run_orElse_ok.mp run with success | ⟨_, success⟩
  · exact left value success
  · exact right value success

/-- info: 'P4SpecTec.Refine.Produces.orElse' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Produces.orElse
#audit_axioms Produces.orElse

/-- An ordered traversal preserves the output domain for every produced element. -/
theorem Produces.mapM {α β : Type} {domain : β → Prop} (f : α → Eval β) (xs : List α)
    (steps : ∀ x ∈ xs, Produces domain (f x)) :
    Produces (fun ys => ∀ y ∈ ys, domain y) (xs.mapM f) := by
  intro ys run
  induction xs generalizing ys with
  | nil =>
    simp only [List.mapM_nil, Eval.run_pure_ok] at run
    subst ys
    simp
  | cons x xs ih =>
    simp only [List.mapM_cons, Eval.run_bind_ok, Eval.run_pure_ok] at run
    obtain ⟨y, hy, rest, hrest, rfl⟩ := run
    intro value member
    rcases List.mem_cons.mp member with rfl | member
    · exact steps x (by simp) _ hy
    · exact ih (by intro z hz; exact steps z (by simp [hz])) rest hrest value member

/-- info: 'P4SpecTec.Refine.Produces.mapM' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Produces.mapM
#audit_axioms Produces.mapM

end P4SpecTec.Refine
