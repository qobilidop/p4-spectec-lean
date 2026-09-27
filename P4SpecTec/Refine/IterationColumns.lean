import P4SpecTec.Refine.Iteration
import P4SpecTec.Interp.InterpAl.Ctx

/-! Exact column collection for list-premise iterations with explicit output encoders.
The empty batch retains its declared column count, as the actual interpreter does.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Lang.Il P4SpecTec.Prelude P4SpecTec.Interp_al

private theorem relatedColumn {α : Type} (encoders : List (α → value))
    {rows : List (List value)} {xs : List α}
    (h : List.Forall₂ (fun row x => canons row = canons (encoders.map (fun f => f x))) rows xs)
    (index : Nat) (encode : α → value) (entry : encoders[index]? = some encode) :
    canons (rows.filterMap (fun row => row[index]?)) = canons (xs.map encode) := by
  induction h with
  | nil => simp only [List.filterMap_nil, List.map_nil]
  | @cons row x rows xs head tail ih =>
    have selected := congrArg (fun values => values[index]?) head
    simp only [canons_eq_map, List.getElem?_map, entry, Option.map_some] at selected
    cases raw : row[index]? with
    | none => simp [raw] at selected
    | some value =>
      simp only [raw, Option.map_some, Option.some.injEq] at selected
      simp only [List.filterMap_cons, raw, List.map_cons, canons]
      rw [selected, ih]

private theorem forall₂RangeMap {α β : Type} {R : α → β → Prop}
    (values : List β) (f : Nat → α)
    (related : ∀ index value, values[index]? = some value → R (f index) value) :
    List.Forall₂ R ((List.range values.length).map f) values := by
  induction values generalizing f with
  | nil => exact .nil
  | cons value values ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def]
    apply List.Forall₂.cons (related 0 value rfl)
    apply ih
    intro index next entry
    exact related (index + 1) next (by simpa using entry)

private theorem relatedRowWidth {α : Type} (encoders : List (α → value))
    {rows : List (List value)} {xs : List α}
    (h : List.Forall₂ (fun row x => canons row = canons (encoders.map (fun f => f x))) rows xs) :
    ∀ row ∈ rows, row.length = encoders.length := by
  induction h with
  | nil => simp
  | @cons row x rows xs head tail ih =>
    intro next member
    rcases List.mem_cons.mp member with rfl | member
    · have length := congrArg List.length head
      simpa only [canons_length, List.length_map] using length
    · exact ih next member

/-- Collect actual rows, retaining the declared output arity when the batch is empty. -/
def collectColumns (arity : Nat) (rows : List (List value)) : Eval (List (List value)) :=
  match rows with
  | [] => pure (List.replicate arity [])
  | _ :: _ => Ctx.transpose rows

/-- Canonically related rectangular rows collect into actual ordered source columns.
Each column has its own explicit encoder, so a scalar product carrier is never flattened
by an overlapping product instance. The empty batch has the declared number of columns. -/
theorem transposeEncodedRows {α : Type} (encoders : List (α → value))
    {rows : List (List value)} {xs : List α}
    (h : List.Forall₂ (fun row x => canons row = canons (encoders.map (fun f => f x))) rows xs) :
    ∃ columns,
      collectColumns encoders.length rows = pure columns ∧
      List.Forall₂ (fun column encode => canons column = canons (xs.map encode))
        columns encoders := by
  let columns := (List.range encoders.length).map fun index =>
    rows.filterMap fun row => row[index]?
  refine ⟨columns, ?_, ?_⟩
  · have widths := relatedRowWidth encoders h
    cases rows with
    | nil => simp [columns, collectColumns, List.map_const']
    | cons row rows =>
      have width := widths row (by simp)
      have allWidths : (row :: rows).all (fun r => r.length == encoders.length) = true := by
        apply List.all_eq_true.mpr
        intro r hr
        simp [widths r hr]
      simp only [collectColumns, Ctx.transpose, width, allWidths, ite_true]
      rfl
  · apply forall₂RangeMap
    intro index encode entry
    exact relatedColumn encoders h index encode entry

/-- info: 'P4SpecTec.Refine.transposeEncodedRows' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transposeEncodedRows
#audit_axioms transposeEncodedRows

/-- Preserve the actual source context constructor when transporting a mapped input list.
The witness keeps the original positional observation available to each traversal body. -/
theorem forall₂MapSource {α β γ : Type} {P : α → β → Prop} (f : α → γ)
    {xs : List α} {ys : List β} (h : List.Forall₂ P xs ys) :
    List.Forall₂ (fun z y => ∃ x, P x y ∧ z = f x) (xs.map f) ys := by
  induction h with
  | nil => exact .nil
  | @cons x y xs ys head tail ih => exact .cons ⟨x, head, rfl⟩ ih

/-- info: 'P4SpecTec.Refine.forall₂MapSource' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms forall₂MapSource
#audit_axioms forall₂MapSource

/-- Move the empty-input branch past the actual monadic traversal.
A successful nonempty traversal always has a nonempty row result; failures are unchanged. -/
theorem collectMappedColumns {α : Type} (xs : List α)
    (f : α → Eval (List value)) (emptyColumns : List (List value)) :
    (match xs with
      | [] => pure emptyColumns
      | _ :: _ => do
        let rows ← xs.mapM f
        Ctx.transpose rows) = (do
      let rows ← xs.mapM f
      match rows with
      | [] => pure emptyColumns
      | _ :: _ => Ctx.transpose rows) := by
  cases xs <;> simp only [List.mapM_nil, List.mapM_cons, pure_bind, bind_assoc]

/-- info: 'P4SpecTec.Refine.collectMappedColumns' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms collectMappedColumns
#audit_axioms collectMappedColumns

end P4SpecTec.Refine
