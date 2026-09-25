import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTec.Refine.Value
import P4SpecTec.Refine.Quote

/-!
The refinement calculus of rung 3 (design section 5.1). `Refines P m n`
says that the interpreter's computation `m` is simulated by the generated
computation `n`: every defined result of `m` (a success or a failure,
never divergence) is matched by a defined result of `n`, the same
failure or values related by `P`. The lemmas below are the rules the
driver tactic (`Tactic/Refine.lean`) applies: `bind` in step, a
`pure`/`throw` at the leaves, sequential choice alternative by
alternative, and an interpreter-only step that cannot fail (`Evals`).
`Holds` states that a global table holds a quoted definition, the
hypothesis every refinement theorem takes for its callees.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il
open P4SpecTec.Prelude
open P4SpecTec.Runtime
open P4SpecTec.Runtime.Dynamic
open P4SpecTec.Runtime.Dynamic_al
open P4SpecTec.Interp_al
open P4SpecTec.Interp_al.Backtrack
open P4SpecTec.Interp_al.Interp

/-! ## Results and refinement -/

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

/-! ## The global tables -/

/-- The global table holds the quoted definition `d` (as `Ctx.load_def`
would enter it). -/
def Holds (g : Ctx.global) (d : Lang.Al.def) : Prop :=
  match d.it with
  | .ExternTypD i _ => g.tdtbl.get? i.it = some .Extern
  | .TypD i tparams deftyp _ => g.tdtbl.get? i.it = some (.Defined tparams deftyp)
  | .VarD .. => True
  | .ExternRelD i nottyp inputs _ => g.rtbl.get? i.it = some (.Extern nottyp inputs)
  | .RelD i nottyp inputs rulegroups elsegroup_opt _ =>
    g.rtbl.get? i.it = some (.Defined nottyp inputs rulegroups elsegroup_opt)
  | .ExternDecD i tparams params typ _ => g.ftbl.get? i.it = some (.Extern tparams params typ)
  | .BuiltinDecD i tparams params typ _ => g.ftbl.get? i.it = some (.Builtin tparams params typ)
  | .TableDecD i params typ tablerows _ => g.ftbl.get? i.it = some (.Table params typ tablerows)
  | .FuncDecD i tparams params typ clauses elseclause_opt _ =>
    g.ftbl.get? i.it = some (.Defined tparams params typ clauses elseclause_opt)

/-- The global tables hold every quoted definition of a spec: the one
hypothesis of a refinement theorem about the tables. -/
def HoldsSpec (spec : List Lang.Al.def) (g : Ctx.global) : Prop := ∀ d, d ∈ spec → Holds g d

/-! ### The witness: `Ctx.init` builds tables that hold the spec -/

/-- An `if` equal to a value: one branch is, under its condition. -/
theorem ite_eq_iff' {α : Type} {c : Prop} [Decidable c] {a b x : α} :
    (if c then a else b) = x ↔ (c ∧ a = x) ∨ (¬c ∧ b = x) := by
  split <;> simp [*]

/-- A key present in a table has an entry. -/
theorem mem_of_getElem?_eq_some {α β : Type} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : Std.HashMap α β} {k : α} {v : β} (h : m[k]? = some v) : k ∈ m := by
  rw [Std.HashMap.mem_iff_contains, Std.HashMap.contains_eq_isSome_getElem?, h]; rfl

/-- A loaded definition's entry survives the loads that follow. -/
theorem holds_of_load_def {g g' : Ctx.global} {d e : Lang.Al.def}
    (h : Holds g d) (hl : Ctx.load_def g e = .ok g') : Holds g' d := by
  obtain ⟨di, dn, da⟩ := d
  obtain ⟨ei, en, ea⟩ := e
  unfold Holds at h ⊢
  unfold Ctx.load_def at hl
  cases di <;> cases ei <;> (try dsimp only at h ⊢) <;>
    simp only [Ctx.add_typdef_global, Ctx.add_rel_global, Ctx.add_func_global, ite_eq_iff',
      pure, Except.pure, throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_or,
      and_false, Except.ok.injEq] at hl <;>
    (try (obtain ⟨hc, rfl⟩ := hl)) <;> (try trivial) <;> (try assumption) <;>
    (try simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq]
      at h ⊢) <;>
    (try assumption) <;>
    (try (split <;> (try assumption) <;>
      (rename_i hk
       exact absurd (Std.HashMap.mem_iff_contains.mp (mem_of_getElem?_eq_some h)) (hk ▸ hc))))

/-- A loaded definition holds in the table it was loaded into. -/
theorem holds_load_def {g g' : Ctx.global} {e : Lang.Al.def}
    (hl : Ctx.load_def g e = .ok g') : Holds g' e := by
  obtain ⟨ei, en, ea⟩ := e
  unfold Holds
  unfold Ctx.load_def at hl
  cases ei <;> (try dsimp only) <;>
    simp only [Ctx.add_typdef_global, Ctx.add_rel_global, Ctx.add_func_global, ite_eq_iff',
      pure, Except.pure, throw, throwThe, MonadExceptOf.throw, reduceCtorEq, false_or,
      and_false, Except.ok.injEq] at hl <;>
    (try (obtain ⟨hc, rfl⟩ := hl)) <;>
    simp [Std.HashMap.get?_eq_getElem?]

/-- Loading a list of definitions keeps every entry and enters every definition. -/
theorem holds_load_defs : ∀ (ds : List Lang.Al.def) {g g' : Ctx.global},
    Ctx.load_defs g ds = .ok g' →
      (∀ d, Holds g d → Holds g' d) ∧ ∀ d, d ∈ ds → Holds g' d
  | [], g, g', h => by
    simp only [Ctx.load_defs, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fun _ hd => hd, fun _ hd => nomatch hd⟩
  | e :: ds, g, g', h => by
    simp only [Ctx.load_defs, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i g1 hl
      obtain ⟨keep, mem⟩ := holds_load_defs ds h
      refine ⟨fun d hd => keep d (holds_of_load_def hd hl), ?_⟩
      intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd
      · exact keep d (holds_load_def hl)
      · exact mem d hd

/-- The tables `Ctx.init` builds from a spec hold every definition of it:
the witness of the refinement theorems' `HoldsSpec` hypothesis. -/
theorem holdsSpec_of_init {spec : List Lang.Al.def} {g : Ctx.global}
    (h : Interp.init spec = .ok g) : HoldsSpec spec g :=
  fun d hd => (holds_load_defs spec h).2 d hd

/-- The outputs of a relation are related to a tuple's values. -/
def Outs (vs : List value) (ws : List value) : Prop := canons vs = canons ws

/-! ## The interpreter with the guard off -/

/-- Tracing is the identity. -/
@[simp] theorem traced_eq {α : Type} (cfg : Config) (what : String) (r : backtrack α) :
    traced cfg what r = r := by
  unfold traced; split <;> rfl

/-- Input checks are off. -/
@[simp] theorem check_rel_inputs_off {cfg : Config} (h : cfg.guard = false) (ctx : Ctx.t)
    (i : Lang.Il.id) (vs : List value) : check_rel_inputs cfg ctx i vs = pure () := by
  unfold check_rel_inputs; simp [h]

/-- Output checks are off. -/
@[simp] theorem check_rel_outputs_off {cfg : Config} (h : cfg.guard = false) (ctx : Ctx.t)
    (i : Lang.Il.id) (n : nottyp) (inputs : Lang.Il.Hints.Input.t) (vs : List value) :
    check_rel_outputs cfg ctx i n inputs vs = pure () := by
  unfold check_rel_outputs; simp [h]

/-- Function input checks are off. -/
@[simp] theorem check_func_inputs_off {cfg : Config} (h : cfg.guard = false) (ctx : Ctx.t)
    (i : Lang.Il.id) (targs : List targ) (vs : List value) :
    check_func_inputs cfg ctx i targs vs = pure () := by
  unfold check_func_inputs; simp [h]

/-- Function output checks are off. -/
@[simp] theorem check_func_output_off {cfg : Config} (h : cfg.guard = false) (ctx : Ctx.t)
    (i : Lang.Il.id) (tparams : List tparam) (t : typ) (targs : List targ) (v : value) :
    check_func_output cfg ctx i tparams t targs v = pure () := by
  unfold check_func_output; simp [h]

/-! ## Quoted syntax, accessed -/

/-- The payload of a quoted phrase. -/
@[simp] theorem Q.p_it {α : Type} (x : α) : (Q.p x).it = x := rfl
/-- The payload of a quoted identifier. -/
@[simp] theorem Q.i_it (s : String) : (Q.i s).it = s := rfl
/-- The payload of a quoted atom. -/
@[simp] theorem Q.a_it (x : Atom.t) : (Q.a x).it = x := rfl
/-- The payload of a quoted type. -/
@[simp] theorem Q.t_it (x : typ') : (Q.t x).it = x := rfl
/-- The payload of a quoted expression. -/
@[simp] theorem Q.e_it (x : exp') (n : typ') : (Q.e x n).it = x := rfl
/-- The note of a quoted expression. -/
@[simp] theorem Q.e_note (x : exp') (n : typ') : (Q.e x n).note = n := rfl
/-- The payload of a quoted path. -/
@[simp] theorem Q.pa_it (x : path') (n : typ') : (Q.pa x n).it = x := rfl
/-- The note of a quoted path. -/
@[simp] theorem Q.pa_note (x : path') (n : typ') : (Q.pa x n).note = n := rfl
/-- The payload of a quoted premise. -/
@[simp] theorem Q.pr_it (x : prem') : (Q.pr x).it = x := rfl
/-- The payload of a quoted argument. -/
@[simp] theorem Q.ar_it (x : arg') : (Q.ar x).it = x := rfl
/-- The payload of a quoted parameter. -/
@[simp] theorem Q.pm_it (x : param') : (Q.pm x).it = x := rfl
/-- The payload of a quoted notation type. -/
@[simp] theorem Q.nt_it (x : nottyp') : (Q.nt x).it = x := rfl
/-- The payload of a quoted definition type. -/
@[simp] theorem Q.dt_it (x : deftyp') : (Q.dt x).it = x := rfl
/-- The payload of a quoted clause. -/
@[simp] theorem Q.cl_it (args : List arg) (out : exp) (prems : List prem) :
    (Q.cl args out prems).it = (args, out, prems) := rfl
/-- The payload of a quoted rule group. -/
@[simp] theorem Q.rg_it (gid : String) (m : Lang.Al.rulematch) (paths : List Lang.Al.rulepath) :
    (Q.rg gid m paths).it = (Q.i gid, m, paths) := rfl
/-- The payload of a quoted else group. -/
@[simp] theorem Q.eg_it (gid : String) (m : Lang.Al.rulematch) (path : Lang.Al.rulepath) :
    (Q.eg gid m path).it = (Q.i gid, m, path) := rfl
/-- The payload of a quoted table row. -/
@[simp] theorem Q.tr_it (pats : List exp) (args : List arg) (out : exp) (prems : List prem) :
    (Q.tr pats args out prems).it = (pats, args, out, prems) := rfl
/-- The payload of a quoted definition. -/
@[simp] theorem Q.d_it (x : Lang.Al.def') : (Q.d x).it = x := rfl
/-- A quoted rule path. -/
@[simp] theorem Q.rp_eq (pid : String) (prems : List prem) (outs : List exp) :
    Q.rp pid prems outs = (Q.i pid, prems, outs) := rfl
/-- A quoted variable. -/
@[simp] theorem Q.v_eq (s : String) (typ : typ') (iters : List iter) :
    Q.v s typ iters = .mk (Q.i s) (Q.t typ) iters := rfl

/-! ## Values, exposed

The facts the driver keeps are `canon v = canon (toValue x)` (a `Rel`
unfolded) for an interpreter value `v` and a generated value `x`. Once `x`
is a constructor, the right-hand side computes to a literal and the
lemmas below expose the shape of `v` one constructor at a time. -/

-- Decidable equality of atoms, for the driver's decisions on quoted syntax.
deriving instance DecidableEq for Atom.t

/-- Atom equality is decided. -/
@[simp] theorem Atom.eq_eq (a b : Atom.t) : Atom.eq a b = decide (a = b) := by
  unfold Atom.eq
  rw [Bool.eq_iff_iff, beq_iff_eq, Atom.compare_eq_iff]
  simp

/-- `canon` of a literal. -/
@[simp] theorem canon_mk (p : value') (n : vnote) (r : region) :
    canon ⟨p, n, r⟩ = ⟨canon' p, dummy, no_region⟩ := by rw [canon]

/-- The payload of a canonical value. -/
theorem canon_it (v : value) : (canon v).it = canon' v.it := by rw [canon]

/-- A canonical value equal to a literal: its payload. -/
theorem canon_eq_it {v : value} {q : value'} {n : vnote} {r : region} (h : canon v = ⟨q, n, r⟩) :
    canon' v.it = q := by
  rw [← canon_it, h]

/-- Equality of naturals. -/
@[simp] theorem eq_nat (a b : Nat) (n n' : vnote) (r r' : region) :
    Runtime.Value.eq ⟨.NumV (.Nat a), n, r⟩ ⟨.NumV (.Nat b), n', r'⟩ = decide (a = b) := by
  rw [Bool.eq_iff_iff, eq_iff_canon]
  simp [canon_mk, canon']

/-- Equality of integers. -/
@[simp] theorem eq_int (a b : Int) (n n' : vnote) (r r' : region) :
    Runtime.Value.eq ⟨.NumV (.Int a), n, r⟩ ⟨.NumV (.Int b), n', r'⟩ = decide (a = b) := by
  rw [Bool.eq_iff_iff, eq_iff_canon]
  simp [canon_mk, canon']

/-- Equality of booleans. -/
@[simp] theorem eq_bool (a b : Bool) (n n' : vnote) (r r' : region) :
    Runtime.Value.eq ⟨.BoolV a, n, r⟩ ⟨.BoolV b, n', r'⟩ = decide (a = b) := by
  rw [Bool.eq_iff_iff, eq_iff_canon]
  simp [canon_mk, canon']

/-- Equality of texts. -/
@[simp] theorem eq_text (a b : ByteText) (n n' : vnote) (r r' : region) :
    Runtime.Value.eq ⟨.TextV a, n, r⟩ ⟨.TextV b, n', r'⟩ = decide (a = b) := by
  rw [Bool.eq_iff_iff, eq_iff_canon]
  simp [canon_mk, canon']

/-- The interpreter's equality is reflexive. -/
@[simp] theorem eq_refl (v : value) : Runtime.Value.eq v v = true := by
  rw [eq_iff_canon]

/-- An equality test on canonically equal values holds. -/
theorem eq_true_of_canon {v w : value} (h : canon v = canon w) : Runtime.Value.eq v w = true :=
  eq_iff_canon.mpr h

/-- An equality test on canonically different values fails. -/
theorem eq_false_of_canon {v w : value} (h : canon v ≠ canon w) :
    Runtime.Value.eq v w = false := by
  cases hv : Runtime.Value.eq v w
  · rfl
  · exact absurd (eq_iff_canon.mp hv) h

/-- `Value.eq` on values related to generated values. -/
theorem eq_of_canon {v w : value} {x y : value} (hv : canon v = canon x) (hw : canon w = canon y) :
    Runtime.Value.eq v w = Runtime.Value.eq x y := by
  rw [Bool.eq_iff_iff, eq_iff_canon, eq_iff_canon, hv, hw]

/-- A canonical boolean payload. -/
theorem canon'_eq_bool {p : value'} {b : Bool} (h : canon' p = .BoolV b) : p = .BoolV b := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  rw [h]

/-- A canonical number payload. -/
theorem canon'_eq_num {p : value'} {m : Num.t} (h : canon' p = .NumV m) : p = .NumV m := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  rw [h]

/-- A canonical text payload. -/
theorem canon'_eq_text {p : value'} {t : ByteText} (h : canon' p = .TextV t) : p = .TextV t := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  rw [h]

/-- A canonical struct payload. -/
theorem canon'_eq_struct {p : value'} {fs : List (Lang.Il.atom × value)}
    (h : canon' p = .StructV fs) : ∃ fs', p = .StructV fs' ∧ canonFields fs' = fs := by
  rcases p with b' | n | s | fs' | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- A canonical case payload. -/
theorem canon'_eq_case {p : value'} {m : Mixfix.t value} (h : canon' p = .CaseV m) :
    ∃ m', p = .CaseV m' ∧ canonMixfix m' = m := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- A canonical tuple payload. -/
theorem canon'_eq_tuple {p : value'} {vs : List value} (h : canon' p = .TupleV vs) :
    ∃ vs', p = .TupleV vs' ∧ canons vs' = vs := by
  rcases p with b' | n | s | fs | c | vs' | (_ | w) | vs' | i | j <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- A canonical list payload. -/
theorem canon'_eq_list {p : value'} {vs : List value} (h : canon' p = .ListV vs) :
    ∃ vs', p = .ListV vs' ∧ canons vs' = vs := by
  rcases p with b' | n | s | fs | c | vs' | (_ | w) | vs' | i | j <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- A canonical `none` payload. -/
theorem canon'_eq_none {p : value'} (h : canon' p = .OptV none) : p = .OptV none := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  rfl

/-- A canonical `some` payload. -/
theorem canon'_eq_some {p : value'} {w : value} (h : canon' p = .OptV (some w)) :
    ∃ w', p = .OptV (some w') ∧ canon w' = w := by
  rcases p with b' | n | s | fs | c | vs | (_ | w') | vs | i | j <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- Canonical lists are empty together. -/
theorem canons_eq_nil {vs : List value} (h : canons vs = []) : vs = [] := by
  cases vs <;> simp [canons] at h; rfl

/-- Canonical lists extend together. -/
theorem canons_eq_cons {vs : List value} {w : value} {ws : List value}
    (h : canons vs = w :: ws) : ∃ v' vs', vs = v' :: vs' ∧ canon v' = w ∧ canons vs' = ws := by
  cases vs <;> simp [canons] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

/-- Canonical field lists are empty together. -/
theorem canonFields_eq_nil {fs : List (Lang.Il.atom × value)} (h : canonFields fs = []) :
    fs = [] := by
  cases fs <;> simp [canonFields] at h; rfl

/-- Canonical field lists extend together. -/
theorem canonFields_eq_cons {fs : List (Lang.Il.atom × value)} {a : Lang.Il.atom} {w : value}
    {ws : List (Lang.Il.atom × value)} (h : canonFields fs = (a, w) :: ws) :
    ∃ a' v' fs', fs = (a', v') :: fs' ∧ a'.it = a.it ∧ canon v' = w ∧ canonFields fs' = ws := by
  cases fs with
  | nil => simp [canonFields] at h
  | cons f fs =>
    obtain ⟨a', v'⟩ := f
    simp only [canonFields, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨a', v', fs, rfl, ?_, h2, h3⟩
    have := congrArg (·.it) h1
    simpa [mkPhrase] using this

/-- A canonical argument. -/
theorem canonMixfix_eq_arg {m : Mixfix.t value} {w : value} (h : canonMixfix m = .Arg w) :
    ∃ w', m = .Arg w' ∧ canon w' = w := by
  cases m <;> simp [canonMixfix] at h
  exact ⟨_, rfl, h⟩

/-- A canonical atom. -/
theorem canonMixfix_eq_atom {m : Mixfix.t value} {a : Lang.Il.atom} (h : canonMixfix m = .Atom a) :
    ∃ a', m = .Atom a' ∧ a'.it = a.it := by
  cases m <;> simp [canonMixfix] at h
  refine ⟨_, rfl, ?_⟩
  have := congrArg (·.it) h
  simpa [mkPhrase] using this

/-- A canonical bracket. -/
theorem canonMixfix_eq_brack {m : Mixfix.t value} {l r : Lang.Il.atom} {mi : Mixfix.t value}
    (h : canonMixfix m = .Brack l mi r) :
    ∃ l' mi' r', m = .Brack l' mi' r' ∧ l'.it = l.it ∧ canonMixfix mi' = mi ∧ r'.it = r.it := by
  cases m <;> simp [canonMixfix] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨_, _, _, rfl, ?_, h2, ?_⟩
  · have := congrArg (·.it) h1; simpa [mkPhrase] using this
  · have := congrArg (·.it) h3; simpa [mkPhrase] using this

/-- A canonical infix. -/
theorem canonMixfix_eq_infix {m : Mixfix.t value} {a : Lang.Il.atom} {l r : Mixfix.t value}
    (h : canonMixfix m = .Infix l a r) :
    ∃ l' a' r', m = .Infix l' a' r' ∧ canonMixfix l' = l ∧ a'.it = a.it ∧ canonMixfix r' = r := by
  cases m <;> simp [canonMixfix] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨_, _, _, rfl, h1, ?_, h3⟩
  have := congrArg (·.it) h2; simpa [mkPhrase] using this

/-- A canonical sequence. -/
theorem canonMixfix_eq_seq {m : Mixfix.t value} {ms : List (Mixfix.t value)}
    (h : canonMixfix m = .Seq ms) : ∃ ms', m = .Seq ms' ∧ canonMixfixes ms' = ms := by
  cases m <;> simp [canonMixfix] at h
  exact ⟨_, rfl, h⟩

/-- Canonical sequences are empty together. -/
theorem canonMixfixes_eq_nil {ms : List (Mixfix.t value)} (h : canonMixfixes ms = []) :
    ms = [] := by
  cases ms <;> simp [canonMixfixes] at h; rfl

/-- Canonical sequences extend together. -/
theorem canonMixfixes_eq_cons {ms : List (Mixfix.t value)} {n : Mixfix.t value}
    {ns : List (Mixfix.t value)} (h : canonMixfixes ms = n :: ns) :
    ∃ m' ms', ms = m' :: ms' ∧ canonMixfix m' = n ∧ canonMixfixes ms' = ns := by
  cases ms <;> simp [canonMixfixes] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

/-- `canons` of an append. -/
@[simp] theorem canons_append (a b : List value) : canons (a ++ b) = canons a ++ canons b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [canons, ih]

/-- `canons` of a map is a map. -/
theorem canons_eq_map (vs : List value) : canons vs = vs.map canon := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [canons, ih]

/-- The length of a canonical list. -/
@[simp] theorem canons_length (vs : List value) : (canons vs).length = vs.length := by
  rw [canons_eq_map, List.length_map]

/-- A canonical `Make.mk`. -/
@[simp] theorem canon_make_mk (t : typ') (p : value') :
    canon (Runtime.Value.Make.mk t p) = ⟨canon' p, dummy, no_region⟩ := by rw [canon]; rfl

/-! ## Variables -/

/-- Comparison of iteration lists. -/
theorem Var.compare_iters_eq_iff : ∀ (a b : List iter), Var.compare_iters a b = .eq ↔ a = b
  | [], [] => by simp [Var.compare_iters]
  | [], _ :: _ => by simp [Var.compare_iters]
  | _ :: _, [] => by simp [Var.compare_iters]
  | x :: xs, y :: ys => by
    simp only [Var.compare_iters, then_eq_iff, List.cons.injEq]
    have : Var.compare_iter x y = .eq ↔ x = y := by cases x <;> cases y <;> simp [Var.compare_iter]
    rw [this, Var.compare_iters_eq_iff xs ys]

/-- Decidable equality of iterators. -/
instance : DecidableEq iter := fun a b =>
  match a, b with
  | .Opt, .Opt => isTrue rfl
  | .List, .List => isTrue rfl
  | .Opt, .List => isFalse (by intro h; cases h)
  | .List, .Opt => isFalse (by intro h; cases h)

/-- The derived equality of iterators is decided. -/
@[simp] theorem iter_beq (a b : iter) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

/-- Equality of variables is equality of the name and the dimensions. -/
@[simp] theorem Var.eq_eq (a b : Var.t) : Var.eq a b = decide (a.1.it = b.1.it ∧ a.2 = b.2) := by
  unfold Var.eq Var.compare
  rw [Bool.eq_iff_iff, beq_iff_eq, then_eq_iff, compareString_eq_iff, Var.compare_iters_eq_iff]
  simp

end P4SpecTec.Refine
