import P4SpecTec.Codegen.Types

/-!
Structured executable statements and rendering of pure and stateful Lean blocks.
-/

namespace P4SpecTec.Codegen.Exp

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types

/-- The fallback of a refutable pattern: upstream's `assign_exp` error. -/
def noMatch : Option String := some "throw Fail.err"

/-- A statement of a `do` block, structured so that the `Prop` encoding
(`Codegen/Props.lean`) can read what it binds, at which type, and what it
means; `render` prints it for the executable encoding. -/
inductive Stmt where
  /-- `let x ← ExceptT.mk f`: a call, `f : Option (Except Fail ty)`. -/
  | call (x : String) (ty : Term) (f : Term)
  /-- `let x ← Eval.err? o`: an `Option ty` whose `none` is an error. -/
  | opt (x : String) (ty : Term) (o : Term)
  /-- `let x ← m` with `m` the lifted call of the relation `id` on `ins`
  (`R.run`, or the `Externs` field when `extern`): a rule premise; `x` is
  `_` for a `holds` premise. -/
  | rel (x : String) (ty : Term) (id : String) (ins : List Term) (extern : Bool) (m : Term)
  /-- `let _ ← Eval.notHold m`, `m` the lifted call of the relation `id`. -/
  | notHold (id : String) (ins : List Term) (extern : Bool) (m : Term)
  /-- `let _ ← Eval.check b`. -/
  | check (b : Term)
  /-- `have x := v`. -/
  | have_ (x : String) (v : Term)
  /-- `let pat := v`, with `| throw Fail.err` when refutable, binding the
  variables `vars` (with their types); `patTerm` is the pattern as a term. -/
  | letPat (pat : Format) (patTerm : Term) (vars : List (String × Term)) (v : Term)
      (refutable : Bool)
  /-- `let x ← List.mapM (fun binder => do body; pure result) z`: the element
  variables `elems` range over the zipped lists `z`, and `result` (a tuple
  of inner variables, of type `resTy`) is collected into `x : List resTy`. -/
  | mapM (x : String) (resTy : Term) (binder : Format) (elems : List (String × Term))
      (body : List Stmt) (result : Term) (z : Term)
  /-- Optional premises retain their structural body: all inputs present run
  `body` and yield `someResult`; all absent yield `noneResult`; mixed inputs fail. -/
  | optM (x : String) (ty : Term) (elems : List (String × Term))
      (body : List Stmt) (someResult noneResult : Term) (options : List Term)
  /-- `let x ← m` for any other monadic term (option iterations). -/
  | bind (x : String) (ty : Term) (m : Term)

/-- A `do` block from rendered statements and a final pure result. -/
def doOfRendered (stmts : List Format) (result : Term) : Term :=
  if stmts.isEmpty then .call "pure" [result]
  else .paren (.doBlock (stmts ++ [Format.text "pure " ++ result.arg]))

/-- Print a statement and every nested block in its selected carrier. -/
partial def Stmt.renderWith (mode : ExecMode) : Stmt → Format
  | .call x _ f => Term.bindStmt x (.call "ExceptT.mk" [f])
  | .opt x _ o => Term.bindStmt x (mode.lift (.call "Eval.err?" [o]))
  | .rel x _ _ _ _ m => Term.bindStmt x m
  | .notHold _ _ _ m => Term.bindStmt "_"
      (.call (if mode == .pure then "Eval.notHold" else "StateEval.notHold") [m])
  | .check b =>
    if mode == .pure then Format.text "let _ ← Eval.check " ++ b.arg
    else Term.bindStmt "_" (mode.lift (.call "Eval.check" [b]))
  | .have_ x v => Term.haveStmt x v
  | .letPat pat _ _ v refutable => Term.letStmt pat v (if refutable then noMatch else none)
  | .mapM x _ binder _ body result z =>
    Term.bindStmt x
      (Term.call "List.mapM"
        [.lamF binder (doOfRendered (body.map (renderWith mode)) result), z])
  | .optM x _ elems body someResult noneResult options =>
    let somePat := "(" ++ ", ".intercalate (elems.map fun (n, _) => s!"some {n}") ++ ")"
    let nonePat := "(" ++ ", ".intercalate (elems.map fun _ => "none") ++ ")"
    let arms := [(Format.text somePat,
      doOfRendered (body.map (renderWith mode)) someResult),
      (Format.text nonePat, Term.call "pure" [noneResult])] ++
      (if elems.length > 1 then [(Format.text "_", Term.atom "throw Fail.err")] else [])
    Term.bindStmt x (Term.paren (.matchOn (.tuple options) arms))
  | .bind x _ m => Term.bindStmt x m

/-- Backward-compatible pure rendering. -/
def Stmt.render (stmt : Stmt) : Format := stmt.renderWith .pure

/-- A `do` block from statements and a final pure result. -/
def doOf (stmts : List Stmt) (result : Term) : Term := doOfRendered (stmts.map Stmt.render) result

/-- Render every statement, including nested iterations, in the selected carrier. -/
def doOfWith (mode : ExecMode) (stmts : List Stmt) (result : Term) : Term :=
  doOfRendered (stmts.map (Stmt.renderWith mode)) result

/-- A `do` block from statements and a final monadic term. -/
def doOfM (stmts : List Stmt) (result : Term) : Term :=
  if stmts.isEmpty then result else .paren (.doBlock (stmts.map Stmt.render ++ [result.fmt]))

/-- Mode-aware block ending in a monadic term. -/
def doOfMWith (mode : ExecMode) (stmts : List Stmt) (result : Term) : Term :=
  if stmts.isEmpty then result
  else .paren (.doBlock (stmts.map (Stmt.renderWith mode) ++ [result.fmt]))

/-- `a <|> b <|> ...`, sequential choice (`Eval.orElse` through the `OrElse`
instance of `Eval`); a mismatch for no alternatives. -/
def alternatives : List Term → Term
  | [] => .atom "(throw Fail.unmatch)"
  | [t] => t
  | t :: ts => .binop "<|>" t (alternatives ts)

end P4SpecTec.Codegen.Exp
