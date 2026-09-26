import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Value
import P4SpecTec.Runtime.Dynamic.Var

/-! Quoted syntax projections and the equality facts used in symbolic execution. -/

namespace P4SpecTec.Refine

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il
open P4SpecTec.Prelude
open P4SpecTec.Runtime
open P4SpecTec.Runtime.Dynamic


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

-- Decidable equality of atoms, for decisions on quoted syntax.
deriving instance DecidableEq for Atom.t

/-- Atom equality is decided. -/
@[simp] theorem Atom.eq_eq (a b : Atom.t) : Atom.eq a b = decide (a = b) := by
  unfold Atom.eq
  rw [Bool.eq_iff_iff, beq_iff_eq, Atom.compare_eq_iff]
  simp

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
