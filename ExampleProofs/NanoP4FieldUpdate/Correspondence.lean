import ExampleProofs.NanoP4FieldUpdate.Representation
import ExampleProofs.NanoP4FieldUpdate.Semantics
import NanoP4Spec.Refinement.Environment
import NanoP4Spec.Refinement.update_fieldValue

/-!
# Finite-fuel correspondence for field updates

The generated forward and reverse certificates connect the actual quoted helper to
its total first-match update meaning. Related raw inputs may carry arbitrary notes
and source regions. The consumer discharges the concrete initialized environment
and composes the helper for two writes; surrounding lvalue evaluation and arbitrary
expression effects remain outside this certificate.
-/

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Interp_al
open P4SpecTec.Lang.Il P4SpecTec.Domain
namespace ExampleProofs.NanoP4FieldUpdate

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- Every related field-list input has a successful finite-fuel execution of the actual
quoted AL function, and its result represents the total generated first-match update.
No termination hypothesis is required; raw notes and source regions are unrestricted. -/
theorem alRealizesUpdate
    (cfg : Interp.Config) (ctx : Ctx.t) (internal : Bool)
    (hguard : cfg.guard = false) (hfenv : ctx.local.fenv = [])
    (hspec : HoldsSpec NanoP4Spec.spec ctx.global)
    (rawFields rawName rawValue : Lang.Il.value)
    (fields : List NanoP4Spec.fieldValue) (name : NanoP4Spec.nameIR)
    (replacement : NanoP4Spec.value)
    (hfields : Rel rawFields fields) (hname : Rel rawName name)
    (hvalue : Rel rawValue replacement) :
    ∃ fuel output,
      Interp.invoke_func fuel cfg internal ctx (Q.i "update_fieldValue") []
        [rawFields, rawName, rawValue] = some (.ok output) ∧
      Rel output (update fields name replacement) := by
  have reverse := NanoP4Spec.«$update_fieldValue».realizes
    cfg ctx internal hguard hfenv hspec rawFields rawName rawValue fields name replacement
    hfields hname hvalue
  obtain ⟨result, ⟨bound, run⟩, related⟩ :=
    reverse (.ok (update fields name replacement)) (generatedEqUpdate fields name replacement)
  cases result with
  | ok output => exact ⟨bound, output, run bound (Nat.le_refl bound), related⟩
  | error failure => cases related

/-- info: 'ExampleProofs.NanoP4FieldUpdate.alRealizesUpdate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms alRealizesUpdate
#audit_axioms alRealizesUpdate

/-- Actual AL helper execution in the initialized, guard-disabled Nano environment. -/
def referenceUpdate (fuel : Nat) (fields name replacement : Lang.Il.value) :
    Eval Lang.Il.value :=
  Interp_al.Interp.invoke_func fuel { guard := false } false NanoP4Spec.Environment.ctx
    (Refine.Q.i "update_fieldValue") [] [fields, name, replacement]

/-- Sequential reference calls, each with its own finite evaluation budget.
The actual first output is passed directly into the second call. -/
def referenceWrites (firstFuel secondFuel : Nat) (fields : Lang.Il.value)
    (left right : ByteText) (leftValue rightValue : Scalar) : Eval Lang.Il.value := do
  let first ← referenceUpdate firstFuel fields (toValue left) (toValue leftValue.generated)
  referenceUpdate secondFuel first (toValue right) (toValue rightValue.generated)

/-- The observable outcomes of two reference calls, existentially hiding only fuel
and irrelevant source annotations. This does not equate finite-fuel exhaustion with failure. -/
def ReferenceObserves (fields : Lang.Il.value) (left right : ByteText)
    (leftValue rightValue : Scalar) (observation : Lang.Il.value) : Prop :=
  ∃ firstFuel secondFuel output,
    (referenceWrites firstFuel secondFuel fields left right leftValue rightValue).run =
      some (.ok output) ∧ Refine.canon output = observation

/-- Every terminating reference outcome is the corresponding successful field update.
The environment witness and all callee obligations are discharged, not assumptions. -/
theorem referenceSound (fuel : Nat) (fields : List NanoP4Spec.fieldValue)
    (name : ByteText) (replacement : NanoP4Spec.value)
    (rawFields rawName rawReplacement : Lang.Il.value)
    (hfields : Refine.Rel rawFields fields) (hname : Refine.Rel rawName name)
    (hvalue : Refine.Rel rawReplacement replacement)
    (result : Except Fail Lang.Il.value)
    (hresult : (referenceUpdate fuel rawFields rawName rawReplacement).run = some result) :
    ∃ output, result = .ok output ∧ Refine.Rel output (update fields name replacement) := by
  set_option maxRecDepth 8192 in
  have forward := NanoP4Spec.«$update_fieldValue».refines fuel
    { guard := false } NanoP4Spec.Environment.ctx false rfl NanoP4Spec.Environment.localFenvEmpty
    NanoP4Spec.Environment.holdsSpec rawFields rawName rawReplacement fields name replacement
    hfields hname hvalue
  obtain ⟨generated, hg, hrel⟩ := forward result hresult
  change NanoP4Spec.«$update_fieldValue» fields name replacement = some generated at hg
  rw [generatedEqUpdate] at hg
  cases Option.some.inj hg
  cases result with
  | ok output => exact ⟨output, rfl, hrel⟩
  | error e => exact False.elim hrel

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceSound' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceSound

/-- Two terminating reference calls produce the two corresponding generated updates. -/
theorem referenceWritesSound (firstFuel secondFuel : Nat) (fields : List Field)
    (rawFields : Lang.Il.value) (hfields : Refine.Rel rawFields (generatedFields fields))
    (left right : ByteText) (leftValue rightValue : Scalar)
    (result : Except Fail Lang.Il.value)
    (hresult : (referenceWrites firstFuel secondFuel rawFields
      left right leftValue rightValue).run = some result) :
    ∃ output, result = .ok output ∧ Refine.Rel output
      (update (update (generatedFields fields) left leftValue.generated)
        right rightValue.generated) := by
  unfold referenceWrites at hresult
  rw [Refine.run_bind] at hresult
  cases hfirst : (referenceUpdate firstFuel rawFields
      (toValue left) (toValue leftValue.generated)).run with
  | none => simp [hfirst] at hresult
  | some first =>
    obtain ⟨middle, hm, hmiddle⟩ := referenceSound firstFuel _ left leftValue.generated
      rawFields (toValue left) (toValue leftValue.generated) hfields rfl rfl first hfirst
    subst first
    simp only [hfirst, Option.bind_some] at hresult
    exact referenceSound secondFuel _ right rightValue.generated middle
      (toValue right) (toValue rightValue.generated) hmiddle rfl rfl result hresult

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceWritesSound' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceWritesSound

/-- Every observed reference result agrees with the generated sequential result. -/
theorem referenceObservationSound (fields : List Field) (rawFields : Lang.Il.value)
    (hfields : Refine.Rel rawFields (generatedFields fields))
    (left right : ByteText) (leftValue rightValue : Scalar) (observation : Lang.Il.value)
    (h : ReferenceObserves rawFields left right leftValue rightValue observation) :
    observation = Refine.canon (toValue
      (update (update (generatedFields fields) left leftValue.generated)
        right rightValue.generated)) := by
  obtain ⟨firstFuel, secondFuel, output, hrun, hobs⟩ := h
  obtain ⟨out, hout, hrel⟩ := referenceWritesSound firstFuel secondFuel fields rawFields
    hfields left right leftValue rightValue (.ok output) hrun
  cases Except.ok.inj hout
  exact hobs.symm.trans hrel

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceObservationSound' depends on axioms:
    [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceObservationSound


/-- Finite-fuel realization with the concrete initialized environment discharged. -/
theorem referenceRealizes (fields : List NanoP4Spec.fieldValue) (name : ByteText)
    (replacement : NanoP4Spec.value) (rawFields rawName rawReplacement : Lang.Il.value)
    (hfields : Rel rawFields fields) (hname : Rel rawName name)
    (hvalue : Rel rawReplacement replacement) :
    ∃ fuel output, (referenceUpdate fuel rawFields rawName rawReplacement).run =
      some (.ok output) ∧ Rel output (update fields name replacement) := by
  exact alRealizesUpdate { guard := false } NanoP4Spec.Environment.ctx false rfl
    NanoP4Spec.Environment.localFenvEmpty NanoP4Spec.Environment.holdsSpec
    rawFields rawName rawReplacement
    fields name replacement hfields hname hvalue

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceRealizes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceRealizes

/-- Both actual reference calls finish at some finite budgets; the first raw output
is reused, without re-encoding, as the input to the second call. -/
theorem referenceWritesRealize (fields : List Field) (rawFields : Lang.Il.value)
    (hfields : Rel rawFields (generatedFields fields))
    (left right : ByteText) (leftValue rightValue : Scalar) :
    ∃ firstFuel secondFuel output,
      (referenceWrites firstFuel secondFuel rawFields left right leftValue rightValue).run =
        some (.ok output) ∧ Rel output
          (update (update (generatedFields fields) left leftValue.generated)
            right rightValue.generated) := by
  obtain ⟨firstFuel, middle, hfirst, hmiddle⟩ := referenceRealizes (generatedFields fields)
    left leftValue.generated rawFields (toValue left) (toValue leftValue.generated)
    hfields rfl rfl
  obtain ⟨secondFuel, output, hsecond, houtput⟩ := referenceRealizes
    (update (generatedFields fields) left leftValue.generated) right rightValue.generated
    middle (toValue right) (toValue rightValue.generated) hmiddle rfl rfl
  refine ⟨firstFuel, secondFuel, output, ?_, houtput⟩
  unfold referenceWrites
  rw [Refine.run_bind, hfirst]
  exact hsecond

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceWritesRealize' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceWritesRealize

/-- Exact two-way characterization of the reference consumer's observations.
The reverse implication supplies successful executions, not a termination premise. -/
theorem referenceObservesIff (fields : List Field) (rawFields : Lang.Il.value)
    (hfields : Rel rawFields (generatedFields fields))
    (left right : ByteText) (leftValue rightValue : Scalar) (observation : Lang.Il.value) :
    ReferenceObserves rawFields left right leftValue rightValue observation ↔
      observation = canon (toValue
        (update (update (generatedFields fields) left leftValue.generated)
          right rightValue.generated)) := by
  constructor
  · exact referenceObservationSound fields rawFields hfields left right leftValue rightValue
      observation
  · intro h
    obtain ⟨firstFuel, secondFuel, output, hrun, hrel⟩ :=
      referenceWritesRealize fields rawFields hfields left right leftValue rightValue
    exact ⟨firstFuel, secondFuel, output, hrun, hrel.trans h.symm⟩

/-- info: 'ExampleProofs.NanoP4FieldUpdate.referenceObservesIff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms referenceObservesIff

end ExampleProofs.NanoP4FieldUpdate
