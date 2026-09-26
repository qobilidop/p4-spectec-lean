import NanoP4Spec.Refinement.Spec

/-!
A concrete initialized environment for the quoted Nano-P4 specification.
Logical hash-map laws, rather than reduction of opaque string hashing, prove
that initialization succeeds. Only finite definition names are computed.
This module is our own consumer support, not an upstream mirror.
-/

namespace NanoP4Proofs.FieldUpdate.Environment

-- Match the quoted specification's existing proof budgets for its deep list.
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

open P4SpecTec
open P4SpecTec.Interp_al

private inductive Table where
  | typ | rel | func
  deriving DecidableEq

private abbrev Key := Table × String

private def key (d : Lang.Al.def) : Option Key :=
  match d.it with
  | .ExternTypD i _ | .TypD i .. => some (.typ, i.it)
  | .VarD .. => none
  | .ExternRelD i .. | .RelD i .. => some (.rel, i.it)
  | .ExternDecD i .. | .BuiltinDecD i .. | .TableDecD i .. | .FuncDecD i .. =>
    some (.func, i.it)

private def keys (ds : List Lang.Al.def) : List Key := ds.filterMap key

private theorem keysCons (d : Lang.Al.def) (ds : List Lang.Al.def) :
    keys (d :: ds) = match key d with
      | none => keys ds
      | some k => k :: keys ds := by
  simp only [keys, List.filterMap_cons]
  cases key d <;> rfl

private def contains (g : Ctx.global) (k : Key) : Bool :=
  match k.1 with
  | .typ => g.tdtbl.contains k.2
  | .rel => g.rtbl.contains k.2
  | .func => g.ftbl.contains k.2

private def load (g : Ctx.global) (d : Lang.Al.def) : Ctx.global :=
  match d.it with
  | .ExternTypD i _ =>
    { g with tdtbl := g.tdtbl.insert i.it .Extern }
  | .TypD i ps t _ =>
    { g with tdtbl := g.tdtbl.insert i.it (.Defined ps t) }
  | .VarD .. => g
  | .ExternRelD i t ins _ =>
    { g with rtbl := g.rtbl.insert i.it (.Extern t ins) }
  | .RelD i t ins groups els _ =>
    { g with rtbl := g.rtbl.insert i.it (.Defined t ins groups els) }
  | .ExternDecD i ps args t _ =>
    { g with ftbl := g.ftbl.insert i.it (.Extern ps args t) }
  | .BuiltinDecD i ps args t _ =>
    { g with ftbl := g.ftbl.insert i.it (.Builtin ps args t) }
  | .TableDecD i args t rows _ =>
    { g with ftbl := g.ftbl.insert i.it (.Table args t rows) }
  | .FuncDecD i ps args t clauses els _ =>
    { g with ftbl := g.ftbl.insert i.it (.Defined ps args t clauses els) }

private def loads (g : Ctx.global) : List Lang.Al.def → Ctx.global
  | [] => g
  | d :: ds => loads (load g d) ds

private theorem containsLoad (g : Ctx.global) (d : Lang.Al.def) (k : Key) :
    contains (load g d) k =
      if key d = some k then true else contains g k := by
  obtain ⟨table, name⟩ := k
  obtain ⟨di, dn, da⟩ := d
  cases di <;> cases table <;>
    simp [load, key, contains, Std.HashMap.contains_insert,
      Bool.beq_eq_decide_eq, eq_comm]

private theorem loadEqOk (g : Ctx.global) (d : Lang.Al.def)
    (fresh : ∀ k, key d = some k → contains g k = false) :
    Ctx.load_def g d = .ok (load g d) := by
  obtain ⟨di, dn, da⟩ := d
  cases di <;> try rfl
  all_goals have hf := fresh _ rfl
  all_goals
    simp only [contains] at hf
    simp [Ctx.load_def, Ctx.add_typdef_global, Ctx.add_rel_global,
      Ctx.add_func_global, load, hf, pure, Except.pure]

private theorem loadsEqOk (ds : List Lang.Al.def) (g : Ctx.global)
    (unique : (keys ds).Nodup)
    (fresh : ∀ k ∈ keys ds, contains g k = false) :
    Ctx.load_defs g ds = .ok (loads g ds) := by
  induction ds generalizing g with
  | nil => rfl
  | cons d ds ih =>
    have headFresh : ∀ k, key d = some k → contains g k = false := by
      intro k hk
      apply fresh k
      simp only [keysCons, hk, List.mem_cons, true_or]
    rw [Ctx.load_defs, loadEqOk g d headFresh]
    simp only [bind, Except.bind]
    apply ih
    · cases hk : key d with
      | none => simpa only [keysCons, hk] using unique
      | some head =>
        have h := unique
        simp only [keysCons, hk, List.nodup_cons] at h
        exact h.2
    · intro k hk
      rw [containsLoad]
      have old : contains g k = false := by
        apply fresh k
        cases hd : key d <;> simp only [keysCons, hd, List.mem_cons]
        · exact hk
        · exact Or.inr hk
      have different : key d ≠ some k := by
        intro hd
        have h := unique
        simp only [keysCons, hd, List.nodup_cons] at h
        exact h.1 hk
      simp [different, old]

private theorem nanoKeysUnique : (keys NanoP4Spec.spec).Nodup := by decide

/-- The concrete global tables built from every quoted Nano-P4 definition. -/
def global : Ctx.global := loads {} NanoP4Spec.spec

/-- Actual Nano-P4 initialization succeeds and yields the concrete tables. -/
theorem initEqOk : Ctx.init NanoP4Spec.spec = .ok global := by
  apply loadsEqOk _ _ nanoKeysUnique
  intro k _
  obtain ⟨table, name⟩ := k
  cases table <;> simp [contains]

/-- info: 'NanoP4Proofs.FieldUpdate.Environment.initEqOk' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms initEqOk
#audit_axioms initEqOk

/-- The concrete environment holds the entire quoted specification. -/
theorem holdsSpec : Refine.HoldsSpec NanoP4Spec.spec global :=
  Refine.holdsSpec_of_init initEqOk

/-- info: 'NanoP4Proofs.FieldUpdate.Environment.holdsSpec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms holdsSpec
#audit_axioms holdsSpec

/-- A concrete interpreter context with no local bindings. -/
def ctx : Ctx.t := Ctx.empty global

/-- The initialized consumer context has no local function overrides. -/
theorem localFenvEmpty : ctx.local.fenv = [] := rfl

/-- info: 'NanoP4Proofs.FieldUpdate.Environment.localFenvEmpty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms localFenvEmpty
#audit_axioms localFenvEmpty

end NanoP4Proofs.FieldUpdate.Environment
