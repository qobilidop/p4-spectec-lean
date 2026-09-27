import P4SpecTec.Interp.InterpAl.Ctx
import P4SpecTec.Refine.Iteration

/-! Canonical local-variable observations at actual AL call and iteration boundaries. -/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude P4SpecTec.Lang.Il P4SpecTec.Interp_al

/-- A local lookup returns a value with the observation of an explicit encoding.
This relation keeps the actual reference context instead of replacing it by a typed context. -/
def LookupRel {α : Type} (key : Runtime.Dynamic.Var.t) (encode : α → value)
    (ctx : Ctx.t) (x : α) : Prop :=
  ∃ v, Ctx.find_value_opt ctx key = some v ∧ canon v = canon (encode x)

/-- Pointwise local lookup observations transport a complete ordered traversal.
All lookups are checked; no absent variable is interpreted as a successful value. -/
theorem lookupMapM {α : Type} (key : Runtime.Dynamic.Var.t) (encode : α → value)
    {ctxs : List Ctx.t} {xs : List α} (h : List.Forall₂ (LookupRel key encode) ctxs xs) :
    ∃ vs, ctxs.mapM (fun ctx => Ctx.find_value ctx key) = (pure vs : Eval (List value)) ∧
      canons vs = canons (xs.map encode) := by
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons ctx x ctxs xs hx _ ih =>
    obtain ⟨v, hv, hc⟩ := hx
    obtain ⟨vs, hvs, hcanons⟩ := ih
    refine ⟨v :: vs, ?_, ?_⟩
    · rw [List.mapM_cons, hvs]
      simp only [Ctx.find_value, hv, pure_bind]
    · simp only [canons, List.map_cons, hc, hcanons]

/-- info: 'P4SpecTec.Refine.lookupMapM' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lookupMapM
#audit_axioms lookupMapM

/-- Two named observations of an actual iteration context. The encoders can
project different components of a generated pair without assuming product encoding. -/
def PairLookupRel {α : Type} (left right : Runtime.Dynamic.Var.t)
    (encodeLeft encodeRight : α → value) (ctx : Ctx.t) (x : α) : Prop :=
  LookupRel left encodeLeft ctx x ∧ LookupRel right encodeRight ctx x

/-- Select the first observation from a pointwise paired-context relation. -/
theorem pairLookupLeft {α : Type} {left right : Runtime.Dynamic.Var.t}
    {encodeLeft encodeRight : α → value} {ctxs : List Ctx.t} {xs : List α}
    (h : List.Forall₂ (PairLookupRel left right encodeLeft encodeRight) ctxs xs) :
    List.Forall₂ (LookupRel left encodeLeft) ctxs xs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.1 ih

/-- info: 'P4SpecTec.Refine.pairLookupLeft' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairLookupLeft
#audit_axioms pairLookupLeft

/-- Select the second observation from a pointwise paired-context relation. -/
theorem pairLookupRight {α : Type} {left right : Runtime.Dynamic.Var.t}
    {encodeLeft encodeRight : α → value} {ctxs : List Ctx.t} {xs : List α}
    (h : List.Forall₂ (PairLookupRel left right encodeLeft encodeRight) ctxs xs) :
    List.Forall₂ (LookupRel right encodeRight) ctxs xs := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.2 ih

/-- info: 'P4SpecTec.Refine.pairLookupRight' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms pairLookupRight
#audit_axioms pairLookupRight

private theorem transposeColumnsOne (xs : List value) :
    ((List.range xs.length).map fun j => [xs].filterMap fun row => row[j]?) =
      xs.map (fun x => [x]) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, List.filterMap_cons, List.filterMap_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ]
    exact congrArg (List.cons [x]) ih
private theorem transposeColumnsTwo (xs ys : List value) (h : xs.length = ys.length) :
    ((List.range xs.length).map fun j => [xs, ys].filterMap fun row => row[j]?) =
      (xs.zip ys).map (fun p => [p.1, p.2]) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        Function.comp_def, List.filterMap_cons, List.filterMap_nil, List.getElem?_cons_zero,
        List.getElem?_cons_succ, List.zip_cons_cons]
      exact congrArg (List.cons [x,y]) (ih ys h)
/-- A single batch transposes into ordered singleton columns, including the empty batch. -/
theorem transposeOne (xs : List value) : Ctx.transpose [xs] = pure (xs.map (fun x => [x])) := by
  simp only [Ctx.transpose, List.all_cons, List.all_nil, BEq.rfl, Bool.and_true,
    ite_true]
  rw [transposeColumnsOne]
/-- Two equal-width batches transpose into ordered paired columns. The width premise
retains the actual interpreter boundary rather than truncating a mismatched matrix. -/
theorem transposeTwo (xs ys : List value) (h : xs.length = ys.length) :
    Ctx.transpose [xs,ys] = pure ((xs.zip ys).map (fun p => [p.1,p.2])) := by
  simp only [Ctx.transpose, List.all_cons, List.all_nil, h, BEq.rfl, Bool.and_true,
    ite_true]
  rw [← h, transposeColumnsTwo xs ys h]

/-- info: 'P4SpecTec.Refine.transposeOne' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transposeOne
#audit_axioms transposeOne

/-- info: 'P4SpecTec.Refine.transposeTwo' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transposeTwo
#audit_axioms transposeTwo

/-- Successfully collected empty batches have no transposed columns.
The premise concerns actual collected outputs and makes no claim about their evaluations. -/
theorem transposeEmptyRows (rows : List (List value))
    (empty : ∀ row ∈ rows, row = []) : Ctx.transpose rows = pure [] := by
  cases rows with
  | nil => rfl
  | cons row rows =>
    have head := empty row (by simp)
    have tail : rows.all (fun row => row.length == 0) = true := by
      apply List.all_eq_true.mpr
      intro row hrow
      simp [empty row (by simp [hrow])]
    simp [Ctx.transpose, head, tail]

/-- info: 'P4SpecTec.Refine.transposeEmptyRows' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transposeEmptyRows
#audit_axioms transposeEmptyRows

end P4SpecTec.Refine
