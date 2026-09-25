/-!
The evaluation monad of the generated code and of the interpreter port:
failure as data, divergence as `none`. Mirrors the shape of upstream's
`'a backtrack` (`interp/interp-al/backtrack.ml`: `Ok`, `Err`, `Unmatch`)
without the failure traces, as `ExceptT Fail Option`, so that Lean's
`partial_fixpoint` accepts recursive definitions written in it: the
sequential choice `orElse` retries only on `Unmatch`, as
`choose_sequential` does, and is monotone in the flat order on `Option`
(design section 5.1, "failure vs divergence").

A generated definition has the type `Option (Except Fail T)` (the form
`partial_fixpoint` derives `partial_correctness` for), its body is
`ExceptT.run` of a `do` block in `Eval`, and calls are lifted back with
`ExceptT.mk`. The `run_*` lemmas below are the symbolic-execution rules
the generated soundness proofs use.
-/

namespace P4SpecTec.Prelude

open Lean.Order

/-- Why an evaluation failed: `err` is upstream's `Err` (an error the
interpreter never backtracks over), `unmatch` its `Unmatch` (a rule or
clause that does not apply, tried past by sequential choice). -/
inductive Fail where
  /-- Upstream's `Err`. -/
  | err
  /-- Upstream's `Unmatch`. -/
  | unmatch
  deriving BEq, Repr, DecidableEq, Inhabited

/-- The evaluation monad: `none` is divergence, `some (.error f)` failure,
`some (.ok a)` success. -/
abbrev Eval := ExceptT Fail Option

namespace Eval

/-- An `if` premise: holds or does not match (`eval_if_prem`). -/
def check (b : Bool) : Eval Unit := if b then pure () else throw .unmatch

/-- Sequential choice, `choose_sequential`: the second alternative runs
only when the first does not match; an error stops the search. -/
def orElse {α : Type} (a b : Eval α) : Eval α :=
  ExceptT.mk (do
    match ← a.run with
    | .ok x => pure (.ok x)
    | .error .err => pure (.error .err)
    | .error .unmatch => b.run)

/-- `a <|> b` on `Eval` is `orElse`: sequential choice that retries only
on a mismatch. This instance shadows the one `ExceptT` inherits from
`MonadExcept`, which would retry on an error too; generated code chains
alternatives with `<|>`. -/
instance instOrElse {α : Type} : OrElse (Eval α) := ⟨fun a b => orElse a (b ())⟩

/-- A `does not hold` premise (`eval_if_not_hold_prem`): success is a
mismatch, an error stays an error, a mismatch is success. -/
def notHold {α : Type} (a : Eval α) : Eval Unit :=
  ExceptT.mk (do
    match ← a.run with
    | .ok _ => pure (.error .unmatch)
    | .error .err => pure (.error .err)
    | .error .unmatch => pure (.ok ()))

/-- Lift an `Option` result, `none` failing with `f`. -/
def ofOption {α : Type} (f : Fail) : Option α → Eval α
  | some a => pure a
  | none => throw f

/-- An `Option` whose `none` is an error: indexing and slicing out of
bounds, division by zero, a failed downcast, a pattern shape that does not
match (upstream errors or aborts at each). -/
def err? {α : Type} (o : Option α) : Eval α := ofOption .err o

/-- An `Option` whose `none` is a mismatch: a builtin's failure
(`invoke_builtin_func` turns `BuiltinError` into `Unmatch`). -/
def unmatch? {α : Type} (o : Option α) : Eval α := ofOption .unmatch o

/-- Divergence. -/
def diverge {α : Type} : Eval α := ExceptT.mk none

/-! ## Monotonicity, for `partial_fixpoint` -/

/-- `ExceptT.mk` is monotone (it is the identity on the carrier). -/
@[partial_fixpoint_monotone]
theorem monotone_mk {γ : Type} [PartialOrder γ] {α : Type}
    (f : γ → Option (Except Fail α)) (hf : monotone f) :
    monotone (fun x => (ExceptT.mk (f x) : Eval α)) := hf

/-- `orElse` is monotone in both alternatives. -/
@[partial_fixpoint_monotone]
theorem monotone_orElse {γ : Type} [PartialOrder γ] {α : Type} (f g : γ → Eval α)
    (hf : monotone f) (hg : monotone g) : monotone (fun x => orElse (f x) (g x)) := by
  unfold orElse
  apply monotone_bind
  · exact hf
  · apply monotone_of_monotone_apply
    intro r
    match r with
    | .ok _ => apply monotone_const
    | .error .err => apply monotone_const
    | .error .unmatch => exact hg

/-- `<|>` on `Eval` is monotone in both alternatives. -/
@[partial_fixpoint_monotone]
theorem monotone_hOrElse {γ : Type} [PartialOrder γ] {α : Type} (f g : γ → Eval α)
    (hf : monotone f) (hg : monotone g) : monotone (fun x => (f x <|> g x : Eval α)) :=
  monotone_orElse f g hf hg

/-- `notHold` is monotone. -/
@[partial_fixpoint_monotone]
theorem monotone_notHold {γ : Type} [PartialOrder γ] {α : Type} (f : γ → Eval α)
    (hf : monotone f) : monotone (fun x => notHold (f x)) := by
  unfold notHold
  apply monotone_bind
  · exact hf
  · apply monotone_of_monotone_apply
    intro r
    match r with
    | .ok _ => apply monotone_const
    | .error .err => apply monotone_const
    | .error .unmatch => apply monotone_const

/-! ## Symbolic execution: when does a run succeed -/

/-- `ExceptT.run` and `ExceptT.mk` cancel. -/
@[simp] theorem run_mk {α : Type} (m : Option (Except Fail α)) :
    (ExceptT.mk m : Eval α).run = m := rfl

/-- A bind succeeds when both halves do. -/
@[simp] theorem run_bind_ok {α β : Type} {m : Eval α} {k : α → Eval β} {b : β} :
    (m >>= k).run = some (.ok b) ↔ ∃ a, m.run = some (.ok a) ∧ (k a).run = some (.ok b) := by
  cases m with
  | none => simp [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk]
  | some r =>
    cases r with
    | ok a =>
      simp only [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, ExceptT.bindCont,
        Option.bind_some]
      constructor
      · intro h; exact ⟨a, rfl, h⟩
      · intro ⟨a', h1, h2⟩; cases h1; exact h2
    | error e =>
      simp [Bind.bind, ExceptT.bind, ExceptT.run, ExceptT.mk, ExceptT.bindCont]

/-- `pure` succeeds with its value. -/
@[simp] theorem run_pure_ok {α : Type} {a b : α} :
    (pure a : Eval α).run = some (.ok b) ↔ a = b := by
  simp [Pure.pure, ExceptT.pure, ExceptT.run, ExceptT.mk]

/-- `throw` never succeeds. -/
@[simp] theorem run_throw_ok {α : Type} {e : Fail} {b : α} :
    (throw e : Eval α).run = some (.ok b) ↔ False := by
  simp [throw, throwThe, MonadExceptOf.throw, ExceptT.run, ExceptT.mk]

/-- `check` succeeds when the condition holds. -/
@[simp] theorem run_check_ok {b : Bool} {u : Unit} :
    (check b).run = some (.ok u) ↔ b = true := by
  unfold check; split <;> simp_all

/-- `orElse` succeeds through the first alternative, or through the second
after the first did not match. -/
@[simp] theorem run_orElse_ok {α : Type} {a b : Eval α} {x : α} :
    (orElse a b).run = some (.ok x) ↔
      a.run = some (.ok x) ∨ (a.run = some (.error .unmatch) ∧ b.run = some (.ok x)) := by
  unfold orElse
  cases h : a.run with
  | none => simp [Bind.bind]
  | some r =>
    cases r with
    | ok y => simp [Bind.bind]
    | error e => cases e <;> simp [Bind.bind]

/-- `<|>` succeeds as `orElse` does. -/
@[simp] theorem run_hOrElse_ok {α : Type} {a b : Eval α} {x : α} :
    (a <|> b : Eval α).run = some (.ok x) ↔
      a.run = some (.ok x) ∨ (a.run = some (.error .unmatch) ∧ b.run = some (.ok x)) :=
  run_orElse_ok

/-- `notHold` succeeds when the relation does not match. -/
@[simp] theorem run_notHold_ok {α : Type} {a : Eval α} {u : Unit} :
    (notHold a).run = some (.ok u) ↔ a.run = some (.error .unmatch) := by
  unfold notHold
  cases h : a.run with
  | none => simp [Bind.bind]
  | some r =>
    cases r with
    | ok y => simp [Bind.bind]
    | error e => cases e <;> simp [Bind.bind]

/-- `ofOption` succeeds with the option's value. -/
@[simp] theorem run_ofOption_ok {α : Type} {f : Fail} {o : Option α} {a : α} :
    (ofOption f o).run = some (.ok a) ↔ o = some a := by
  cases o <;> simp [ofOption]

/-- `err?` succeeds with the option's value. -/
@[simp] theorem run_err_ok {α : Type} {o : Option α} {a : α} :
    (err? o).run = some (.ok a) ↔ o = some a := run_ofOption_ok

/-- `unmatch?` succeeds with the option's value. -/
@[simp] theorem run_unmatch_ok {α : Type} {o : Option α} {a : α} :
    (unmatch? o).run = some (.ok a) ↔ o = some a := run_ofOption_ok

/-- A successful `mapM` succeeds on every element, pointwise along the
zip, and preserves the length. -/
theorem run_mapM_ok {α β : Type} {f : α → Eval β} : ∀ {xs : List α} {ys : List β},
    (List.mapM f xs).run = some (.ok ys) →
      xs.length = ys.length ∧ ∀ x y, (x, y) ∈ List.zip xs ys → (f x).run = some (.ok y) := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    simp only [List.mapM_nil, run_pure_ok] at h
    subst h
    exact ⟨rfl, by simp⟩
  | cons x xs ih =>
    intro ys h
    simp only [List.mapM_cons, run_bind_ok, run_pure_ok] at h
    obtain ⟨y, hy, ys', hys', rfl⟩ := h
    obtain ⟨hlen, hall⟩ := ih hys'
    refine ⟨by simp [hlen], ?_⟩
    intro x' y' hmem
    simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem
    · exact hy
    · exact hall x' y' hmem

end Eval

end P4SpecTec.Prelude
