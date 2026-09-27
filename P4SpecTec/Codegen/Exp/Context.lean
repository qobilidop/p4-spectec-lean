import P4SpecTec.Codegen.Exp.Stmt

/-!
Compilation context, temporary state, block isolation and resolved type lookup.
-/

namespace P4SpecTec.Codegen.Exp

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types

/-- What the compiler knows while compiling one definition. -/
structure Ctx where
  /-- The spec environment. -/
  env : Env
  /-- The prefix of temporaries, chosen to clash with no spec variable. -/
  tmpPrefix : String := "tmp_"
  /-- Names of extern functions and relations, called through `Externs`. -/
  externs : List String := []
  /-- Lexically bound callable arguments, resolved before globals/externs. -/
  callbacks : List String := []

/-- The statements hoisted so far and the temporary counter. -/
structure St where
  /-- Statements of the current block, in order. -/
  stmts : Array Stmt := #[]
  /-- The next temporary. -/
  tmp : Nat := 0

/-- The compilation monad. -/
abbrev CgM := ReaderT Ctx (StateT St (Except String))

/-- A fresh temporary. -/
def fresh : CgM String := do
  let st ← get
  set { st with tmp := st.tmp + 1 }
  pure s!"{(← read).tmpPrefix}{st.tmp}"

/-- Emit a statement into the current block. -/
def emit (s : Stmt) : CgM Unit := modify fun st => { st with stmts := st.stmts.push s }

/-- Run a compilation in a fresh block and return its result and statements. -/
def subBlock {α : Type} (m : CgM α) : CgM (α × List Stmt) := do
  let saved := (← get).stmts
  modify fun st => { st with stmts := #[] }
  let a ← m
  let stmts := (← get).stmts
  modify fun st => { st with stmts := saved }
  pure (a, stmts.toList)

/-- Fail compilation. -/
def fail {α : Type} (msg : String) : CgM α := throw msg

/-- The resolved type of an expression. -/
def resolve (t : typ') : CgM typ' := do pure ((← read).env.resolve t)

/-- The Lean type of a spec type. -/
def typOf (t : typ') : CgM Term := do pure (typTerm (← read).env [] t)

/-- The variant a resolved type names, with its cases and constructor names. -/
def variantOf (t : typ') : CgM (Option (String × List typcase × List String)) := do
  let env := (← read).env
  match env.resolve t with
  | .VarT i targs =>
    match env.variantCases i.it (targs.map (·.it)) with
    | some cases => pure (some (i.it, cases, ctorNames cases))
    | none => pure none
  | _ => pure none

/-- The qualified constructor of a case of the variant `t` names, and
whether the variant has other cases (the pattern is refutable). -/
def ctorFor (t : typ') (m : Mixfix.mixop) : CgM (String × Bool) := do
  let env := (← read).env
  match ← variantOf t with
  | some (tid, cases, names) =>
    match (cases.zip names).find? fun (c, _) => Mixfix.eq_mixop c.nottyp.it m with
    | some (_, n) => pure (env.q (Names.typeName tid) ++ "." ++ n,
        cases.length > 1 || env.representation.hasRawExtern tid)
    | none => fail s!"case {Mixfix.to_string m} is not a case of {tid}"
  | none => fail s!"case {Mixfix.to_string m} used at a non-variant type"

/-- The fields of a resolved struct type. -/
def fieldsOf (t : typ') : CgM (String × List (atom × typ)) := do
  let env := (← read).env
  match env.resolve t with
  | .VarT i targs =>
    match env.structFields i.it (targs.map (·.it)) with
    | some fields => pure (i.it, fields)
    | none => fail s!"{i.it} is not a struct"
  | _ => fail "struct expression at a non-struct type"

/-- Run a compilation for one definition. -/
def run {α : Type} (ctx : Ctx) (m : CgM α) : Except String α :=
  (m.run ctx |>.run' {})

end P4SpecTec.Codegen.Exp
