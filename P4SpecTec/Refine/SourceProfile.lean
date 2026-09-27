import P4SpecTec.Interp.InterpAl.Ctx
import P4SpecTec.Tactic.Audit

/-!
Accounting for source metavariable declarations omitted from executable quotations.
AL table initialization deliberately ignores VarD; no runtime values are invented.
Declared-type source codecs and semantic program initialization are separate obligations.
-/

namespace P4SpecTec.Refine.SourceProfile

open P4SpecTec.Lang.Il P4SpecTec.Interp_al

/-- Identify schematic AL variable declarations, which carry no initializer. -/
def isVariable (d : Lang.Al.def) : Bool :=
  match d.it with | .VarD .. => true | _ => false

/-- Retain actual typed variable declarations in source order. -/
def variables (spec : Lang.Al.spec) : Lang.Al.spec := spec.filter isVariable

/-- Retain exactly the definitions loaded by the executable quotation. -/
def withoutVariables (spec : Lang.Al.spec) : Lang.Al.spec :=
  spec.filter fun d => !isVariable d

/-- A schematic variable declaration leaves every initialized global table unchanged. -/
theorem loadVariable (g : Ctx.global) (d : Lang.Al.def) (declared : isVariable d = true) :
    Ctx.load_def g d = .ok g := by
  rcases d with ⟨definition, note, region⟩
  cases definition <;> simp only [isVariable, Bool.false_eq_true] at declared
  rfl

/-- info: 'P4SpecTec.Refine.SourceProfile.loadVariable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loadVariable
#audit_axioms loadVariable

/-- An entire list of schematic declarations leaves every initial global unchanged. -/
theorem loadVariables (g : Ctx.global) (ds : Lang.Al.spec)
    (onlyVariables : ∀ d ∈ ds, isVariable d = true) : Ctx.load_defs g ds = .ok g := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [Ctx.load_defs, loadVariable g d (onlyVariables d (List.mem_cons_self ..))]
    simp only [bind, Except.bind]
    exact ih (fun d member => onlyVariables d (List.mem_cons_of_mem _ member))

/-- info: 'P4SpecTec.Refine.SourceProfile.loadVariables' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loadVariables
#audit_axioms loadVariables

/-- Removing source metavariables preserves checked AL table initialization, including errors. -/
theorem loadWithoutVariables (g : Ctx.global) (ds : Lang.Al.spec) :
    Ctx.load_defs g (withoutVariables ds) = Ctx.load_defs g ds := by
  induction ds generalizing g with
  | nil => rfl
  | cons d ds ih =>
    cases h : isVariable d with
    | false =>
      simp only [withoutVariables, List.filter_cons, h, Bool.not_false, ↓reduceIte]
      rw [Ctx.load_defs, Ctx.load_defs]
      cases Ctx.load_def g d with
      | error e => rfl
      | ok global => exact ih global
    | true =>
      simp only [withoutVariables, List.filter_cons, h, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte]
      rw [Ctx.load_defs, loadVariable g d h]
      exact ih g

/-- info: 'P4SpecTec.Refine.SourceProfile.loadWithoutVariables' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms loadWithoutVariables
#audit_axioms loadWithoutVariables

/-- Metavariable omission changes neither successful nor failing specification initialization. -/
theorem initWithoutVariables (ds : Lang.Al.spec) :
    Ctx.init (withoutVariables ds) = Ctx.init ds := loadWithoutVariables {} ds

/-- info: 'P4SpecTec.Refine.SourceProfile.initWithoutVariables' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms initWithoutVariables
#audit_axioms initWithoutVariables

end P4SpecTec.Refine.SourceProfile
