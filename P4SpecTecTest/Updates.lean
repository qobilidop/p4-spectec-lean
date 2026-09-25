import Lean.Elab.Command
import P4SpecTec.Codegen.Exp
import P4SpecTec.Prelude

/-!
List-index update regressions. The checks elaborate the real expression
compiler's term and run it in `Eval`; unsupported path shapes stay errors.
-/

namespace P4SpecTecTest.Updates

open P4SpecTec P4SpecTec.Util.Source P4SpecTec.Lang.Il
open P4SpecTec.Codegen P4SpecTec.Prelude

def nat : typ' := .NumT .NatT
def listNat : typ' := .IterT (mkPhrase nat) .List
def nestedList : typ' := .IterT (mkPhrase listNat) .List

def env : Env := { lib := "P4SpecTecTest.Updates" }

def varExp (name : String) (ty : typ') : exp :=
  ⟨.VarE (mkPhrase name), ty, no_region⟩

def root (ty : typ') : path := ⟨.RootP, ty, no_region⟩

def index (p : path) (i : exp) (ty : typ') : path :=
  ⟨.IdxP p i, ty, no_region⟩

def update (base replacement : exp) (p : path) : exp :=
  ⟨.UpdE base p replacement, base.note, no_region⟩

def listUpdate : exp := update (varExp "xs" listNat) (varExp "v" nat)
  (index (root listNat) (varExp "i" nat) nat)

def compile (e : exp) : Except String (Term × List Exp.Stmt) :=
  Exp.run { env } (Exp.subBlock (Exp.compileExp e))

#guard (compile listUpdate).isOk

def textUpdate : exp := update (varExp "s" .TextT) (varExp "char" .TextT)
  (index (root .TextT) (varExp "i" nat) .TextT)

def sliceUpdate : exp := update (varExp "xs" listNat) (varExp "ys" listNat)
  ⟨.SliceP (root listNat) (varExp "i" nat) (varExp "n" nat), listNat, no_region⟩

def nestedUpdate : exp := update (varExp "xss" nestedList) (varExp "v" nat)
  (index (index (root nestedList) (varExp "i" nat) listNat)
    (varExp "j" nat) nat)

#guard !(compile textUpdate).isOk
#guard !(compile sliceUpdate).isOk
#guard !(compile nestedUpdate).isOk

-- Calls in the three expression positions expose evaluation order in the
-- structured statement stream, before any later renderer rearrangement.
def call (name : String) (ty : typ') : exp :=
  ⟨.CallE (mkPhrase name) [] [], ty, no_region⟩

def orderedUpdate : exp := update (call "base" listNat) (call "replacement" nat)
  (index (root listNat) (call "index" nat) nat)

def orderedStatements : Option (List String) := do
  let (_, stmts) ← (compile orderedUpdate).toOption
  pure (stmts.map fun s => match s with
    | .call _ _ f => Codegen.render f.fmt
    | .opt .. => "update"
    | _ => "unexpected")

#guard orderedStatements == some [
  "P4SpecTecTest.Updates.«$base»",
  "P4SpecTecTest.Updates.«$replacement»",
  "P4SpecTecTest.Updates.«$index»",
  "update"]

open Lean Elab Command in
run_cmd do
  let source ← match compile listUpdate with
    | .error err => throwError "list update did not compile: {err}"
    | .ok (result, stmts) => pure (Codegen.render (Exp.doOf stmts result).fmt)
  let decl := "def runUpdate (xs : List Nat) (v i : Nat) : " ++
    "Option (Except Fail (List Nat)) := (" ++ source ++ " : Eval (List Nat)).run"
  let checks := [
    "#guard (match runUpdate [10, 20, 30] 7 0 with " ++
      "| some (.ok ys) => ys == [7, 20, 30] | _ => false)",
    "#guard (match runUpdate [10, 20, 30] 7 1 with " ++
      "| some (.ok ys) => ys == [10, 7, 30] | _ => false)",
    "#guard (match runUpdate [10, 20, 30] 7 2 with " ++
      "| some (.ok ys) => ys == [10, 20, 7] | _ => false)",
    "#guard (match runUpdate [10, 20, 30] 7 3 with " ++
      "| some (.error .err) => true | _ => false)"]
  for command in decl :: checks do
    let stx ← match Lean.Parser.runParserCategory (← getEnv) `command command with
      | .ok stx => pure stx
      | .error err => throwError "generated update did not parse:\n{command}\n{err}"
    Lean.Elab.Command.elabCommand stx

end P4SpecTecTest.Updates
