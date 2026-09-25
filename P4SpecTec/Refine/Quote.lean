import P4SpecTec.Lang.Al.Ast

/-!
Smart constructors for quoted AL terms (`⌜d⌝`, design section 5): the
generated `d.al` data (`Codegen/Reify.lean`) is built from these so that
every node's type is known to the elaborator from the constructor alone,
regions are `no_region` and hints are dropped. The interpreter reads
neither regions nor hints (design section 5.3), so a definition quoted
this way evaluates as the exported one.
-/

namespace P4SpecTec.Refine.Q

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al

/-- A phrase without region. -/
def p {α : Type} (it : α) : phrase α := mkPhrase it

/-- An identifier phrase. -/
def i (s : String) : Lang.Il.id := mkPhrase s

/-- An atom phrase. -/
def a (x : Atom.t) : Lang.Il.atom := mkPhrase x

/-- A type phrase. -/
def t (it : typ') : typ := mkPhrase it

/-- A type variable. -/
def varT (s : String) (targs : List typ := []) : typ' := .VarT (i s) targs

/-- An expression with its type note. -/
def e (it : exp') (note : typ') : exp := ⟨it, note, no_region⟩

/-- A path with its type note. -/
def pa (it : path') (note : typ') : path := ⟨it, note, no_region⟩

/-- A premise phrase. -/
def pr (it : prem') : prem := mkPhrase it

/-- An argument phrase. -/
def ar (it : arg') : arg := mkPhrase it

/-- A parameter phrase. -/
def pm (it : param') : param := mkPhrase it

/-- A notation type. -/
def nt (it : nottyp') : nottyp := mkPhrase it

/-- A type case without hints. -/
def tc (n : nottyp') (origin : String) (targs : List typ := []) : typcase :=
  .mk (nt n) (mkPhrase (.mk (i origin) targs)) []

/-- A definition type phrase. -/
def dt (it : deftyp') : deftyp := mkPhrase it

/-- An iteration variable. -/
def v (s : String) (typ : typ') (iters : List iter := []) : var := .mk (i s) (t typ) iters

/-- A clause phrase. -/
def cl (args : List arg) (out : exp) (prems : List prem) : clause := mkPhrase (args, out, prems)

/-- A rule group phrase. -/
def rg (gid : String) (m : rulematch) (paths : List rulepath) : Lang.Al.rulegroup :=
  mkPhrase (i gid, m, paths)

/-- An else group phrase. -/
def eg (gid : String) (m : rulematch) (path : rulepath) : Lang.Al.elsegroup :=
  mkPhrase (i gid, m, path)

/-- A rule path. -/
def rp (pid : String) (prems : List prem) (outs : List exp) : rulepath := (i pid, prems, outs)

/-- A table row phrase. -/
def tr (pats : List exp) (args : List arg) (out : exp) (prems : List prem) : Lang.Al.tablerow :=
  mkPhrase (pats, args, out, prems)

/-- A definition phrase. -/
def d (it : Lang.Al.def') : Lang.Al.def := mkPhrase it

end P4SpecTec.Refine.Q
