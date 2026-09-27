import P4SpecTec.Runtime.Type.Subst
import P4SpecTec.Tactic.Audit

/-!
Syntax-derived bounds for checked substitution, not a mirror. The traversal only
visits the input syntax: replacement types are returned without recursively
substituting them. Function-type substitution keeps its explicit unsupported
error. These bounds remove a fixed-depth cutoff without changing checked results
at sufficient fuel; they do not bound recursive alias expansion.
-/

namespace P4SpecTec.Runtime.Type.Subst

open P4SpecTec.Lang.Il

mutual

/-- Maximum checked-substitution traversal depth of one input type. -/
def syntaxDepth (t : typ) : Nat :=
  match t with
  | ⟨.VarT _ ts, _, _⟩ | ⟨.TupleT ts, _, _⟩ => syntaxDepths ts + 1
  | ⟨.IterT t _, _, _⟩ => syntaxDepth t + 1
  | _ => 1
termination_by sizeOf t

/-- Maximum traversal depth across a list of input types. -/
def syntaxDepths : List typ → Nat
  | [] => 0
  | t :: ts => max (syntaxDepth t) (syntaxDepths ts)
termination_by ts => sizeOf ts

end

private theorem sufficient (theta : theta) (fuel : Nat) :
    (∀ t, syntaxDepth t ≤ fuel → ∃ r, (subst_typ_inner_checked theta fuel t).run = some r) ∧
    (∀ ts, syntaxDepths ts ≤ fuel →
      ∃ r, (subst_typs_inner_checked theta fuel ts).run = some r) := by
 induction fuel with
 | zero =>
   constructor
   · intro t h
     cases t with | mk t note location =>
       cases t <;> simp [syntaxDepth] at h
   · intro ts h
     cases ts with
     | nil => exact ⟨.ok [], by simp [subst_typs_inner_checked, pure, ExceptT.pure]⟩
     | cons t ts =>
       simp only [syntaxDepths] at h
       have ht : syntaxDepth t = 0 := Nat.le_zero.mp (Nat.le_trans (Nat.le_max_left _ _) h)
       cases t with | mk t note location => cases t <;> simp [syntaxDepth] at ht
 | succ fuel ih =>
   have one : ∀ t, syntaxDepth t ≤ fuel + 1 →
       ∃ r, (subst_typ_inner_checked theta (fuel + 1) t).run = some r := by
     intro t h
     cases t with | mk t note location =>
       cases t with
       | BoolT | NumT _ | TextT =>
         simp [subst_typ_inner_checked, pure, ExceptT.pure]
       | FuncT _ _ _ =>
         simp only [subst_typ_inner_checked]
         exact ⟨.error _, rfl⟩
       | VarT id args =>
         simp only [subst_typ_inner_checked]
         split
         · split <;> exact ⟨_, rfl⟩
         · obtain ⟨r, hr⟩ := ih.2 args (by simpa [syntaxDepth] using h)
           simp only [ExceptT.run] at hr
           cases r <;> simp [bind, ExceptT.bind, ExceptT.bindCont, ExceptT.mk,
             ExceptT.run, hr, pure, ExceptT.pure]
       | TupleT args =>
         obtain ⟨r, hr⟩ := ih.2 args (by simpa [syntaxDepth] using h)
         simp only [ExceptT.run] at hr
         cases r <;> simp [subst_typ_inner_checked, bind, ExceptT.bind, ExceptT.bindCont,
           ExceptT.mk, ExceptT.run, hr, pure, ExceptT.pure]
       | IterT t iter =>
         obtain ⟨r, hr⟩ := ih.1 t (by simpa [syntaxDepth] using h)
         simp only [ExceptT.run] at hr
         cases r <;> simp [subst_typ_inner_checked, bind, ExceptT.bind, ExceptT.bindCont,
           ExceptT.mk, ExceptT.run, hr, pure, ExceptT.pure]
   refine ⟨one, ?_⟩
   intro ts h
   induction ts with
   | nil => exact ⟨.ok [], by simp [subst_typs_inner_checked, pure, ExceptT.pure]⟩
   | cons t ts tail =>
     simp only [syntaxDepths] at h
     obtain ⟨r, hr⟩ := one t (Nat.le_trans (Nat.le_max_left _ _) h)
     obtain ⟨s, hs⟩ := tail (Nat.le_trans (Nat.le_max_right _ _) h)
     simp only [ExceptT.run] at hr hs
     cases r <;> cases s <;>
       simp [subst_typs_inner_checked, bind, ExceptT.bind, ExceptT.bindCont,
         ExceptT.mk, ExceptT.run, hr, hs, pure, ExceptT.pure]

private theorem stable (theta : theta) (fuel : Nat) :
    (∀ t, syntaxDepth t ≤ fuel → ∀ extra,
      subst_typ_inner_checked theta (fuel + extra) t = subst_typ_inner_checked theta fuel t) ∧
    (∀ ts, syntaxDepths ts ≤ fuel → ∀ extra,
      subst_typs_inner_checked theta (fuel + extra) ts =
        subst_typs_inner_checked theta fuel ts) := by
 induction fuel with
 | zero =>
   constructor
   · intro t h
     cases t with | mk t note location => cases t <;> simp [syntaxDepth] at h
   · intro ts h extra
     cases ts with
     | nil => simp [subst_typs_inner_checked]
     | cons t ts =>
       simp only [syntaxDepths] at h
       have ht : syntaxDepth t = 0 := Nat.le_zero.mp (Nat.le_trans (Nat.le_max_left _ _) h)
       cases t with | mk t note location => cases t <;> simp [syntaxDepth] at ht
 | succ fuel ih =>
   have one : ∀ t, syntaxDepth t ≤ fuel + 1 → ∀ extra,
       subst_typ_inner_checked theta (fuel + 1 + extra) t =
         subst_typ_inner_checked theta (fuel + 1) t := by
     intro t h extra
     rw [show fuel + 1 + extra = fuel + extra + 1 by omega]
     cases t with | mk t note location =>
       cases t with
       | BoolT | NumT _ | TextT | FuncT _ _ _ => simp [subst_typ_inner_checked]
       | VarT id args =>
         simp only [subst_typ_inner_checked]
         cases hl : theta.lookup id.it with
         | some r => rfl
         | none => rw [ih.2 args (by simpa [syntaxDepth] using h) extra]
       | TupleT args =>
         simp only [subst_typ_inner_checked]
         rw [ih.2 args (by simpa [syntaxDepth] using h) extra]
       | IterT t iter =>
         simp only [subst_typ_inner_checked]
         rw [ih.1 t (by simpa [syntaxDepth] using h) extra]
   refine ⟨one, ?_⟩
   intro ts h extra
   induction ts with
   | nil => simp [subst_typs_inner_checked]
   | cons t ts tail =>
     simp only [syntaxDepths] at h
     simp only [subst_typs_inner_checked]
     rw [one t (Nat.le_trans (Nat.le_max_left _ _) h) extra,
       tail (Nat.le_trans (Nat.le_max_right _ _) h)]
/-- Checked substitution with sufficient fuel computed from its input syntax. -/
def substType (theta : theta) (t : typ) : Checked typ :=
  if theta.isEmpty then pure t else subst_typ_inner_checked theta (syntaxDepth t) t

/-- Checked substitution of a type list with a common sufficient syntax bound. -/
def substTypes (theta : theta) (ts : List typ) : Checked (List typ) :=
  if theta.isEmpty then pure ts else subst_typs_inner_checked theta (syntaxDepths ts) ts

/-- Checked notation substitution with enough fuel for every argument type. -/
def substNotation (theta : theta) (n : nottyp) : Checked nottyp :=
  if theta.isEmpty then pure n
  else subst_nottyp_checked (syntaxDepths (Domain.Mixfix.args n.it)) theta n

/-- Syntax-bounded substitution always returns a value or an explicit error. -/
theorem substTypeDefined (theta : theta) (t : typ) :
    ∃ result, (substType theta t).run = some result := by
  unfold substType
  split
  · exact ⟨.ok t, rfl⟩
  · exact (sufficient theta (syntaxDepth t)).1 t (Nat.le_refl _)

/-- info: 'P4SpecTec.Runtime.Type.Subst.substTypeDefined' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms substTypeDefined
#audit_axioms substTypeDefined

/-- The list wrapper cannot silently exhaust substitution fuel. -/
theorem substTypesDefined (theta : theta) (ts : List typ) :
    ∃ result, (substTypes theta ts).run = some result := by
  unfold substTypes
  split
  · exact ⟨.ok ts, rfl⟩
  · exact (sufficient theta (syntaxDepths ts)).2 ts (Nat.le_refl _)

/-- info: 'P4SpecTec.Runtime.Type.Subst.substTypesDefined' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms substTypesDefined
#audit_axioms substTypesDefined

/-- Every larger substitution budget has exactly the syntax-bounded result. -/
theorem substTypeStable (theta : theta) (t : typ) (fuel : Nat)
    (enough : syntaxDepth t ≤ fuel) :
    subst_typ_checked fuel theta t = substType theta t := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  simp only [substType, subst_typ_checked]
  split
  · rfl
  · exact (stable theta (syntaxDepth t)).1 t (Nat.le_refl _) extra

/-- info: 'P4SpecTec.Runtime.Type.Subst.substTypeStable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms substTypeStable
#audit_axioms substTypeStable

/-- A common syntax bound gives the same list result at every larger budget. -/
theorem substTypesStable (theta : theta) (ts : List typ) (fuel : Nat)
    (enough : syntaxDepths ts ≤ fuel) :
    subst_typs_checked fuel theta ts = substTypes theta ts := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  simp only [substTypes, subst_typs_checked]
  split
  · rfl
  · exact (stable theta (syntaxDepths ts)).2 ts (Nat.le_refl _) extra

/-- info: 'P4SpecTec.Runtime.Type.Subst.substTypesStable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms substTypesStable
#audit_axioms substTypesStable

/-- Notation substitution also yields a value or an explicit error, never exhaustion. -/
theorem substNotationDefined (theta : theta) (n : nottyp) :
    ∃ result, (substNotation theta n).run = some result := by
  unfold substNotation
  split
  · exact ⟨.ok n, rfl⟩
  · rename_i nonempty
    simp only [subst_nottyp_checked, nonempty]
    obtain ⟨r, hr⟩ := (sufficient theta (syntaxDepths (Domain.Mixfix.args n.it))).2
      (Domain.Mixfix.args n.it) (Nat.le_refl _)
    simp only [ExceptT.run] at hr
    cases r with
    | error e =>
      exact ⟨.error e, by simp [bind, ExceptT.bind, ExceptT.bindCont, hr,
        ExceptT.run, ExceptT.mk, pure]⟩
    | ok ts =>
      simp only [bind, ExceptT.bind, hr, ExceptT.bindCont, Option.bind_some]
      cases Domain.Mixfix.fill (Domain.Mixfix.to_mixop n.it) ts <;> exact ⟨_, rfl⟩

/-- info: 'P4SpecTec.Runtime.Type.Subst.substNotationDefined' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms substNotationDefined
#audit_axioms substNotationDefined

end P4SpecTec.Runtime.Type.Subst
