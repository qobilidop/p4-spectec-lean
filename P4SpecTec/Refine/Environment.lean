import P4SpecTec.Interp.InterpAl.Interp

/-! Global-table initialization and the guard-free reference execution profile. -/

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


end P4SpecTec.Refine
