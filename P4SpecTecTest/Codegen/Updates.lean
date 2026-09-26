import Lean.Elab.Command
import P4SpecTec.Codegen.Exp
import P4SpecTec.Codegen.Reify
import P4SpecTec.Prelude

/-!
List-index update and byte-text regressions. The checks elaborate the real expression
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

#guard (compile textUpdate).isOk
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

open Lean Elab Command in
run_cmd do
  let source ← match compile textUpdate with
    | .error err => throwError "text update did not compile: {err}"
    | .ok (result, stmts) => pure (Codegen.render (Exp.doOf stmts result).fmt)
  let decl := "def runTextUpdate (s char : ByteText) (i : Nat) : " ++
    "Option (Except Fail ByteText) := (" ++ source ++ " : Eval ByteText).run"
  let checks := [
    "#guard (match runTextUpdate (ByteText.ofString \"é\") (ByteText.ofString \"X\") 0 with " ++
      "| some (.ok t) => t.toBytes == ByteArray.mk #[0x58, 0xa9] | _ => false)",
    "#guard (match runTextUpdate (ByteText.ofString \"é\") (ByteText.ofString \"X\") 2 with " ++
      "| some (.error .err) => true | _ => false)",
    "#guard (match runTextUpdate (ByteText.ofString \"abc\") (ByteText.ofString \"é\") 0 with " ++
      "| some (.error .err) => true | _ => false)"]
  for command in decl :: checks do
    let stx ← match Lean.Parser.runParserCategory (← getEnv) `command command with
      | .ok stx => pure stx
      | .error err => throwError "generated text update did not parse:\n{command}\n{err}"
    Lean.Elab.Command.elabCommand stx

-- Compile literal and byte operations through the production emitter,
-- including an invalid-UTF-8 payload that cannot use a Lean string literal.
open Lean Elab Command in
run_cmd do
  let raw := ByteText.ofBytes (ByteArray.mk #[0, 0xff, 0xa9])
  let rawExp : exp := ⟨.TextE raw, .TextT, no_region⟩
  let unicode : exp := ⟨.TextE (ByteText.ofString "é"), .TextT, no_region⟩
  let number (n : Nat) : exp := ⟨.NumE (.Nat n), nat, no_region⟩
  let cases : List (String × exp × String × String) := [
    ("rawLiteral", rawExp, "ByteText", "v.toBytes == ByteArray.mk #[0, 0xff, 0xa9]"),
    ("unicodeLiteral", unicode, "ByteText", "v.toBytes == ByteArray.mk #[0xc3, 0xa9]"),
    ("byteLength", ⟨.LenE unicode, nat, no_region⟩, "Nat", "v == 2"),
    ("byteIndex", ⟨.IdxE unicode (number 1), .TextT, no_region⟩,
      "ByteText", "v.toBytes == ByteArray.mk #[0xa9]"),
    ("byteSlice", ⟨.SliceE rawExp (number 1) (number 2), .TextT, no_region⟩,
      "ByteText", "v.toBytes == ByteArray.mk #[0xff, 0xa9]"),
    ("byteCat", ⟨.CatE unicode rawExp, .TextT, no_region⟩,
      "ByteText", "v.toBytes == ByteArray.mk #[0xc3, 0xa9, 0, 0xff, 0xa9]")]
  for (name, input, ty, expected) in cases do
    let source ← match compile input with
      | .error err => throwError "byte expression did not compile: {err}"
      | .ok (result, stmts) => pure (Codegen.render (Exp.doOf stmts result).fmt)
    let decl := s!"def {name} : Eval {ty} := {source}"
    let check := s!"#guard (match {name}.run with | some (.ok v) => {expected} | _ => false)"
    for command in [decl, check] do
      let stx ← match Lean.Parser.runParserCategory (← getEnv) `command command with
        | .ok stx => pure stx
        | .error err => throwError "byte expression did not parse:\n{command}\n{err}"
      Lean.Elab.Command.elabCommand stx
  let quoted := Codegen.render (Reify.exp' rawExp.it).fmt
  let decl := s!"def quotedRaw : exp' := {quoted}"
  let check := "#guard (match quotedRaw with | .TextE s => " ++
    "s.toBytes == ByteArray.mk #[0, 0xff, 0xa9] | _ => false)"
  for command in [decl, check] do
    let stx ← match Lean.Parser.runParserCategory (← getEnv) `command command with
      | .ok stx => pure stx
      | .error err => throwError "byte quotation did not parse:\n{command}\n{err}"
    Lean.Elab.Command.elabCommand stx

end P4SpecTecTest.Updates
