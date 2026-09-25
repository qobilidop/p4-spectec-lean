import P4SpecTec.Lang.Al.Ast

/-!
Smart constructors for quoted AL terms (`⌜d⌝`, design section 5): the
generated `d.al` data (`Codegen/Reify.lean`) is built from these so that
every node's type is known to the elaborator from the constructor alone,
regions are `no_region` and hints are dropped. The interpreter reads
neither regions nor hints (design section 5.3), so a definition quoted
this way evaluates as the exported one. The constructors are reducible,
so that the driver tactic's `simp` sees through them definitionally
(rewriting under `decide` needs that).
-/

namespace P4SpecTec.Refine.Q

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al

/-- A phrase without region. -/
@[reducible] def p {α : Type} (it : α) : phrase α := mkPhrase it

/-- An identifier phrase. -/
@[reducible] def i (s : String) : Lang.Il.id := mkPhrase s

/-- An atom phrase. -/
@[reducible] def a (x : Atom.t) : Lang.Il.atom := mkPhrase x

/-- A type phrase. -/
@[reducible] def t (it : typ') : typ := mkPhrase it

/-- A type variable. -/
@[reducible] def varT (s : String) (targs : List typ := []) : typ' := .VarT (i s) targs

/-- An expression with its type note. -/
@[reducible] def e (it : exp') (note : typ') : exp := ⟨it, note, no_region⟩

/-- A path with its type note. -/
@[reducible] def pa (it : path') (note : typ') : path := ⟨it, note, no_region⟩

/-- A premise phrase. -/
@[reducible] def pr (it : prem') : prem := mkPhrase it

/-- An argument phrase. -/
@[reducible] def ar (it : arg') : arg := mkPhrase it

/-- A parameter phrase. -/
@[reducible] def pm (it : param') : param := mkPhrase it

/-- A notation type. -/
@[reducible] def nt (it : nottyp') : nottyp := mkPhrase it

/-- A type case without hints. -/
@[reducible] def tc (n : nottyp') (origin : String) (targs : List typ := []) : typcase :=
  .mk (nt n) (mkPhrase (.mk (i origin) targs)) []

/-- A definition type phrase. -/
@[reducible] def dt (it : deftyp') : deftyp := mkPhrase it

/-- An iteration variable. -/
@[reducible] def v (s : String) (typ : typ') (iters : List iter := []) : var :=
  .mk (i s) (t typ) iters

/-- A clause phrase. -/
@[reducible] def cl (args : List arg) (out : exp) (prems : List prem) : clause :=
  mkPhrase (args, out, prems)

/-- A rule group phrase. -/
@[reducible] def rg (gid : String) (m : rulematch) (paths : List rulepath) : Lang.Al.rulegroup :=
  mkPhrase (i gid, m, paths)

/-- An else group phrase. -/
@[reducible] def eg (gid : String) (m : rulematch) (path : rulepath) : Lang.Al.elsegroup :=
  mkPhrase (i gid, m, path)

/-- A rule path. -/
@[reducible] def rp (pid : String) (prems : List prem) (outs : List exp) : rulepath :=
  (i pid, prems, outs)

/-- A table row phrase. -/
@[reducible] def tr (pats : List exp) (args : List arg) (out : exp) (prems : List prem) :
    Lang.Al.tablerow :=
  mkPhrase (pats, args, out, prems)

/-- A definition phrase. -/
@[reducible] def d (it : Lang.Al.def') : Lang.Al.def := mkPhrase it

end P4SpecTec.Refine.Q
