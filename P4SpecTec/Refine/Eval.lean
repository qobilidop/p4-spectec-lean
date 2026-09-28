import P4SpecTec.Prelude.Eval

/-! Forward simulation of terminating computations and its composition rules. -/

namespace P4SpecTec.Refine

open P4SpecTec.Prelude


/-- Results agree: the same failure, or related values. -/
def ResRel {α β : Type} (P : α → β → Prop) : Except Fail α → Except Fail β → Prop
  | .ok a, .ok b => P a b
  | .error e, .error e' => e = e'
  | _, _ => False

/-- `m` (the interpreter) refines `n` (generated code): every defined result
of `m` is matched by a defined result of `n`. -/
def Refines {α β : Type} (P : α → β → Prop) (m : Eval α) (n : Eval β) : Prop :=
  ∀ r, m.run = some r → ∃ r', n.run = some r' ∧ ResRel P r r'

/-- A computation that cannot fail: every defined result is a success
satisfying `P`. -/
def Evals {α : Type} (m : Eval α) (P : α → Prop) : Prop :=
  ∀ r, m.run = some r → ∃ a, r = .ok a ∧ P a

/-- The run of a bind. -/
theorem run_bind {α β : Type} {m : Eval α} {k : α → Eval β} :
    (m >>= k).run = m.run.bind fun | .ok a => (k a).run | .error e => some (.error e) := by
  cases m with
  | none => rfl
  | some r => cases r <;> rfl

/-- The run of `orElse`. -/
theorem run_orElse {α : Type} {a b : Eval α} :
    (Eval.orElse a b).run = a.run.bind fun
      | .ok x => some (.ok x) | .error .err => some (.error .err) | .error .unmatch => b.run := by
  cases a with
  | none => rfl
  | some r => cases r with
    | ok x => rfl
    | error e => cases e <;> rfl

/-- The run of `notHold`. -/
theorem run_notHold {α : Type} {a : Eval α} :
    (Eval.notHold a).run = a.run.bind fun
      | .ok _ => some (.error .unmatch) | .error .err => some (.error .err)
      | .error .unmatch => some (.ok ()) := by
  cases a with
  | none => rfl
  | some r => cases r with
    | ok x => rfl
    | error e => cases e <;> rfl

/-- `<|>` on `Eval` is `orElse`. -/
theorem hOrElse_eq {α : Type} {a b : Eval α} : (a <|> b) = Eval.orElse a b := rfl

/-- A choice whose second alternative is a mismatch is its first. -/
theorem orElse_unmatch {α : Type} {a : Eval α} : Eval.orElse a (throw .unmatch) = a := by
  cases a with
  | none => rfl
  | some r => cases r with
    | ok x => rfl
    | error e => cases e <;> rfl

/-- `ExceptT.mk` of a run is the computation. -/
@[simp] theorem mk_run {α : Type} (m : Eval α) : ExceptT.mk m.run = m := rfl

/-- A present option lifts to `pure`. -/
@[simp] theorem err_some {α : Type} (a : α) : Eval.err? (some a) = pure a := rfl

/-- An absent option lifts to an error. -/
@[simp] theorem err_none {α : Type} : (Eval.err? none : Eval α) = throw .err := rfl

/-- A present option lifts to `pure`. -/
@[simp] theorem unmatch_some {α : Type} (a : α) : Eval.unmatch? (some a) = pure a := rfl

/-- An absent option lifts to a mismatch. -/
@[simp] theorem unmatch_none {α : Type} : (Eval.unmatch? none : Eval α) = throw .unmatch := rfl

/-- A check that holds. -/
@[simp] theorem check_true : Eval.check true = pure () := rfl

/-- A check that fails. -/
@[simp] theorem check_false : Eval.check false = throw .unmatch := rfl

/-- Generated membership as a disjunction, the form the reference's `List.any` takes;
core's `List.elem_cons` leaves a Boolean `match` that never meets it. -/
theorem elem_cons_or {α : Type} [BEq α] (a b : α) (bs : List α) :
    List.elem a (b :: bs) = (a == b || List.elem a bs) := by
  simp only [List.elem_cons]; cases a == b <;> rfl

/-- Generated option tests (`eps = $f(…)`) compare with the derived `Option` equality;
these decide it on constructors, leaving element equality for `some`. -/
@[simp] theorem option_beq_none_none {α : Type} [BEq α] :
    Option.instBEq.beq (none : Option α) none = true := rfl

/-- An absent option differs from a present one. -/
@[simp] theorem option_beq_none_some {α : Type} [BEq α] (a : α) :
    Option.instBEq.beq (none : Option α) (some a) = false := rfl

/-- A present option differs from an absent one. -/
@[simp] theorem option_beq_some_none {α : Type} [BEq α] (a : α) :
    Option.instBEq.beq (some a) (none : Option α) = false := rfl

/-- Present options compare their elements. -/
@[simp] theorem option_beq_some_some {α : Type} [BEq α] (a b : α) :
    Option.instBEq.beq (some a) (some b) = (a == b) := rfl

/-- Divergence absorbs a continuation. -/
@[simp] theorem diverge_bind {α β : Type} {k : α → Eval β} : (Eval.diverge >>= k) = Eval.diverge :=
  rfl

/-- A failure absorbs a continuation. -/
@[simp] theorem throw_bind {α β : Type} {e : Fail} {k : α → Eval β} :
    ((throw e : Eval α) >>= k) = throw e := rfl

/-- Divergence refines anything. -/
theorem refines_diverge {α β : Type} {P : α → β → Prop} {n : Eval β} :
    Refines P Eval.diverge n := by
  intro r h; cases h

/-- A computation with no defined result refines anything. -/
theorem refines_of_none {α β : Type} {P : α → β → Prop} {m : Eval α} {n : Eval β}
    (h : m.run = none) : Refines P m n := by
  intro r hr; rw [h] at hr; cases hr

/-- A first step with no defined result, before its continuation, refines anything. -/
theorem refines_bind_of_none {α γ β : Type} {P : γ → β → Prop} {m : Eval α}
    {k : α → Eval γ} {n : Eval β} (h : m.run = none) : Refines P (m >>= k) n := by
  intro r hr; rw [run_bind, h] at hr; cases hr

/-- Related values. -/
theorem refines_pure {α β : Type} {P : α → β → Prop} {a : α} {b : β} (h : P a b) :
    Refines P (pure a) (pure b) := by
  intro r hr
  cases hr
  exact ⟨.ok b, rfl, h⟩

/-- The same failure. -/
theorem refines_throw {α β : Type} {P : α → β → Prop} {e : Fail} :
    Refines P (throw e : Eval α) (throw e : Eval β) := by
  intro r hr
  cases hr
  exact ⟨.error e, rfl, rfl⟩

/-- Weaken the value relation. -/
theorem refines_mono {α β : Type} {P Q : α → β → Prop} {m : Eval α} {n : Eval β}
    (h : ∀ a b, P a b → Q a b) (hr : Refines P m n) : Refines Q m n := by
  intro r hr'
  obtain ⟨r', hn, hres⟩ := hr r hr'
  refine ⟨r', hn, ?_⟩
  cases r <;> cases r' <;> simp_all [ResRel]

/-- Refinement composes along binds. -/
theorem refines_bind {α β γ δ : Type} {P : α → β → Prop} {Q : γ → δ → Prop}
    {m : Eval α} {n : Eval β} {k : α → Eval γ} {l : β → Eval δ}
    (h₁ : Refines P m n) (h₂ : ∀ a b, P a b → Refines Q (k a) (l b)) :
    Refines Q (m >>= k) (n >>= l) := by
  intro r hr
  rw [run_bind] at hr
  cases hm : m.run with
  | none => rw [hm] at hr; cases hr
  | some s =>
    rw [hm] at hr
    obtain ⟨s', hn, hres⟩ := h₁ s hm
    cases s with
    | error e =>
      cases s' with
      | ok _ => exact absurd hres id
      | error e' =>
        simp only [ResRel] at hres
        subst hres
        simp only [Option.bind_some] at hr
        exact ⟨.error e, by rw [run_bind, hn]; rfl, by cases hr; rfl⟩
    | ok a =>
      cases s' with
      | error _ => exact absurd hres id
      | ok b =>
        simp only [ResRel] at hres
        simp only [Option.bind_some] at hr
        obtain ⟨r', hl, hres'⟩ := h₂ a b hres r hr
        exact ⟨r', by rw [run_bind, hn]; exact hl, hres'⟩

/-- An interpreter-only step that cannot fail, then refinement. -/
theorem refines_bind_evals {α γ δ : Type} {Q : γ → δ → Prop} {m : Eval α} {P : α → Prop}
    {k : α → Eval γ} {n : Eval δ}
    (h₁ : Evals m P) (h₂ : ∀ a, P a → Refines Q (k a) n) : Refines Q (m >>= k) n := by
  intro r hr
  rw [run_bind] at hr
  cases hm : m.run with
  | none => rw [hm] at hr; cases hr
  | some s =>
    rw [hm] at hr
    obtain ⟨a, rfl, ha⟩ := h₁ s hm
    exact h₂ a ha r hr

/-- A generated computation without continuation, given one. -/
theorem refines_of_bind_pure {α β : Type} {P : α → β → Prop} {m : Eval α} {n : Eval β}
    (h : Refines P m (n >>= pure)) : Refines P m n := by
  rw [bind_pure] at h; exact h

/-- Sequential choice, alternative by alternative. -/
theorem refines_orElse {α β : Type} {P : α → β → Prop} {m₁ m₂ : Eval α} {n₁ n₂ : Eval β}
    (h₁ : Refines P m₁ n₁) (h₂ : Refines P m₂ n₂) :
    Refines P (Eval.orElse m₁ m₂) (Eval.orElse n₁ n₂) := by
  intro r hr
  rw [run_orElse] at hr
  cases hm : m₁.run with
  | none => rw [hm] at hr; cases hr
  | some s =>
    rw [hm] at hr
    obtain ⟨s', hn, hres⟩ := h₁ s hm
    cases s with
    | ok a =>
      cases s' with
      | error _ => exact absurd hres id
      | ok b =>
        simp only [Option.bind_some] at hr
        cases hr
        exact ⟨.ok b, by rw [run_orElse, hn]; rfl, hres⟩
    | error e =>
      cases s' with
      | ok _ => exact absurd hres id
      | error e' =>
        simp only [ResRel] at hres
        subst hres
        cases e with
        | err =>
          simp only [Option.bind_some] at hr
          cases hr
          exact ⟨.error .err, by rw [run_orElse, hn]; rfl, rfl⟩
        | unmatch =>
          simp only [Option.bind_some] at hr
          obtain ⟨r', hl, hres'⟩ := h₂ r hr
          exact ⟨r', by rw [run_orElse, hn]; exact hl, hres'⟩

/-- Sequential choice written with `<|>`. -/
theorem refines_hOrElse {α β : Type} {P : α → β → Prop} {m₁ m₂ : Eval α} {n₁ n₂ : Eval β}
    (h₁ : Refines P m₁ n₁) (h₂ : Refines P m₂ n₂) : Refines P (m₁ <|> m₂) (n₁ <|> n₂) :=
  refines_orElse h₁ h₂

/-- `notHold` on both sides. -/
theorem refines_notHold {α β : Type} {P : α → β → Prop} {m : Eval α} {n : Eval β}
    (h : Refines P m n) : Refines (fun _ _ => True) (Eval.notHold m) (Eval.notHold n) := by
  intro r hr
  rw [run_notHold] at hr
  cases hm : m.run with
  | none => rw [hm] at hr; cases hr
  | some s =>
    rw [hm] at hr
    obtain ⟨s', hn, hres⟩ := h s hm
    cases s with
    | ok a =>
      cases s' with
      | error _ => exact absurd hres id
      | ok b =>
        simp only [Option.bind_some] at hr
        cases hr
        exact ⟨.error .unmatch, by rw [run_notHold, hn]; rfl, rfl⟩
    | error e =>
      cases s' with
      | ok _ => exact absurd hres id
      | error e' =>
        simp only [ResRel] at hres
        subst hres
        cases e <;> simp only [Option.bind_some] at hr <;> cases hr
        · exact ⟨.error .err, by rw [run_notHold, hn]; rfl, rfl⟩
        · exact ⟨.ok (), by rw [run_notHold, hn]; rfl, trivial⟩

/-- A `have` on the generated side: the bound variable with its equation. -/
theorem refines_have {α β γ : Type} {P : α → β → Prop} {m : Eval α} {t : γ}
    {f : γ → Eval β} (h : ∀ x, x = t → Refines P m (f x)) :
    Refines P m (have x := t; f x) :=
  h t rfl

/-- A `let` on the generated side. -/
theorem refines_let {α β γ : Type} {P : α → β → Prop} {m : Eval α} {t : γ}
    {f : γ → Eval β} (h : ∀ x, x = t → Refines P m (f x)) : Refines P m (let x := t; f x) :=
  h t rfl

/-- A pure result on the interpreter side is a refinement of `pure`. -/
theorem refines_of_evals {α β : Type} {P : α → β → Prop} {m : Eval α} {b : β}
    (h : Evals m fun a => P a b) : Refines P m (pure b) := by
  intro r hr
  obtain ⟨a, rfl, ha⟩ := h r hr
  exact ⟨.ok b, rfl, ha⟩

/-- `Evals` of `pure`. -/
theorem evals_pure {α : Type} {P : α → Prop} {a : α} (h : P a) : Evals (pure a) P := by
  intro r hr; cases hr; exact ⟨a, rfl, h⟩

/-- `Evals` of divergence. -/
theorem evals_diverge {α : Type} {P : α → Prop} : Evals (Eval.diverge : Eval α) P := by
  intro r hr; cases hr

/-- `Evals` composes along binds. -/
theorem evals_bind {α β : Type} {P : α → Prop} {Q : β → Prop} {m : Eval α} {k : α → Eval β}
    (h₁ : Evals m P) (h₂ : ∀ a, P a → Evals (k a) Q) : Evals (m >>= k) Q := by
  intro r hr
  rw [run_bind] at hr
  cases hm : m.run with
  | none => rw [hm] at hr; cases hr
  | some s =>
    rw [hm] at hr
    obtain ⟨a, rfl, ha⟩ := h₁ s hm
    exact h₂ a ha r hr

/-- Weaken `Evals`. -/
theorem evals_mono {α : Type} {P Q : α → Prop} {m : Eval α} (h : ∀ a, P a → Q a)
    (he : Evals m P) : Evals m Q := by
  intro r hr
  obtain ⟨a, rfl, ha⟩ := he r hr
  exact ⟨a, rfl, h a ha⟩

/-- `Evals` of a successful option lift. -/
theorem evals_err_some {α : Type} {P : α → Prop} {a : α} (h : P a) :
    Evals (Eval.err? (some a)) P := evals_pure h


end P4SpecTec.Refine
