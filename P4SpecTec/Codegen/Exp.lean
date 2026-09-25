import P4SpecTec.Codegen.Types

/-!
Expressions, patterns and premises to Lean, in the executable encoding.

The target is a `do` block in the `Eval` monad (`Prelude/Eval.lean`):
failure is data, `Fail.unmatch` for what the interpreter backtracks over
and `Fail.err` for what it does not, and `none` is divergence, so that
`partial_fixpoint` accepts the recursive definitions. Every expression
compiles to a pure term in A-normal form: sub-expressions that can fail
(calls, downcasts, indexing, slicing) are hoisted into `let x ←`
statements of the enclosing block, so the term itself is total. Patterns
(`assign_exp` upstream) become `let` bindings with `| throw Fail.err` on
refutable shapes, and premises become statements.

Per-construct encodings (design section 5.4), each at its case below:

- `UpCastE`, `DownCastE`, `SubE` use the injection, projection and check
  between the two resolved types.
- Iterated expressions and premises zip the bound lists and map; the
  length guards upstream inserts make a mismatch unreachable.
- Numeric operators follow `Num.bin`: subtraction of naturals is an
  integer; division and modulus truncate.
- Every call is lifted into the monad with `ExceptT.mk`; the callee has the
  type `Option (Except Fail T)` that `partial_correctness` needs.
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
  /-- `let x ← m` for any other monadic term (option iterations). -/
  | bind (x : String) (ty : Term) (m : Term)

/-- A `do` block from rendered statements and a final pure result. -/
def doOfRendered (stmts : List Format) (result : Term) : Term :=
  if stmts.isEmpty then .call "pure" [result]
  else .paren (.doBlock (stmts ++ [Format.text "pure " ++ result.arg]))

/-- Print a statement. -/
partial def Stmt.render : Stmt → Format
  | .call x _ f => Term.bindStmt x (.call "ExceptT.mk" [f])
  | .opt x _ o => Term.bindStmt x (.call "Eval.err?" [o])
  | .rel x _ _ _ _ m => Term.bindStmt x m
  | .notHold _ _ _ m => Term.bindStmt "_" (.call "Eval.notHold" [m])
  | .check b => Format.text "let _ ← Eval.check " ++ b.arg
  | .have_ x v => Term.haveStmt x v
  | .letPat pat _ _ v refutable => Term.letStmt pat v (if refutable then noMatch else none)
  | .mapM x _ binder _ body result z =>
    Term.bindStmt x
      (Term.call "List.mapM" [.lamF binder (doOfRendered (body.map render) result), z])
  | .bind x _ m => Term.bindStmt x m

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

/-- A `do` block from statements and a final pure result. -/
def doOf (stmts : List Stmt) (result : Term) : Term := doOfRendered (stmts.map Stmt.render) result

/-- A `do` block from statements and a final monadic term. -/
def doOfM (stmts : List Stmt) (result : Term) : Term :=
  if stmts.isEmpty then result else .paren (.doBlock (stmts.map Stmt.render ++ [result.fmt]))

/-- `a <|> b <|> ...`, sequential choice (`Eval.orElse` through the `OrElse`
instance of `Eval`); a mismatch for no alternatives. -/
def alternatives : List Term → Term
  | [] => .atom "(throw Fail.unmatch)"
  | [t] => t
  | t :: ts => .binop "<|>" t (alternatives ts)

/-- Fail compilation. -/
def fail {α : Type} (msg : String) : CgM α := throw msg

/-- The resolved type of an expression. -/
def resolve (t : typ') : CgM typ' := do pure ((← read).env.resolve t)

/-- The Lean type of a spec type. -/
def typOf (t : typ') : CgM Term := do pure (typTerm (← read).env [] t)

/-- The type of an iteration variable: its base type under its dimensions
(`Typ.Make.iterate`). -/
def varTyp (w : Lang.Il.var) : typ' :=
  w.iters.foldl (fun t i => .IterT (mkPhrase t) i) w.typ.it

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
    | some (_, n) => pure (env.q (Names.typeName tid) ++ "." ++ n, cases.length > 1)
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

/-- The simple iterated variable `x*{x <- x*}` an expression is, if any:
mirrors `is_iter_var_exp`. -/
partial def iterVar? (e : exp) : Option (String × List iter) :=
  match e.it with
  | .VarE i => some (i.it, [])
  | .IterE inner (.mk iter [.mk vi _ vis]) =>
    match iterVar? inner with
    | some (i, is) => if i == vi.it && is == vis then some (i, is ++ [iter]) else none
    | none => none
  | _ => none

/-- The Lean name of a variable. -/
def var (id : String) (iters : List iter) : Term := .atom (Names.varName id iters)

/-- The zipped list of several bound lists, and the binder destructuring it. -/
def zipped (lists : List Term) (names : List String) : Term × String :=
  match lists, names with
  | [l], [n] => (l, n)
  | l :: ls, n :: ns =>
    let (rest, restPat) := zipped ls ns
    (.call "List.zip" [l, rest], s!"({n}, {restPat})")
  | _, _ => (.atom "[]", "_")

/-- The binder of a zipped iteration, ascribed with the element types. -/
def zipBinder (pat : String) (types : List Term) : Format :=
  let ty := match types with
    | [t] => t.fmt
    | ts => Format.joinSep (ts.map (·.arg)) " × "
  Term.binder (Format.text pat) ty

/-- Bind `o` to the projection `proj` of every element of the list `t`; a
single variable needs no projection. -/
def unzipStmt (o t proj : String) : Stmt :=
  if proj.isEmpty then .have_ o (.atom t)
  else .have_ o (Term.call "List.map" [.atom s!"(·{proj})", .atom t])

/-- The tuple type of several types; `Unit` for none. -/
def tupleType : List Term → Term
  | [] => .atom "Unit"
  | [t] => t
  | ts => ⟨Format.joinSep (ts.map (·.arg)) " × ", false⟩

/-- The projections of a tuple of `n` components, for unzipping. -/
def projections (n : Nat) : List String :=
  (List.range n).map fun i =>
    if n == 1 then "" else String.join ((List.range (min i (n - 1))).map fun _ => ".2") ++
      (if i == n - 1 then "" else ".1")

/-! ## Casts -/

mutual

/-- The injection of `x : sub` into `sup`, a pure term. -/
partial def castUp (sub sup : typ') (x : Term) : CgM Term := do
  let env := (← read).env
  let sub := env.resolve sub
  let sup := env.resolve sup
  if typEq sub sup then pure x
  else match sub, sup with
    | .NumT .NatT, .NumT .IntT => pure (.call "Int.ofNat" [x])
    | .VarT .., .VarT .. => pure (.call (env.q (upName sub sup)) [x])
    | .TupleT ss, .TupleT ts =>
      let names := (List.range ss.length).map fun i => s!"c{i}"
      let parts ← ((ss.zip ts).zip names).mapM fun ((a, b), n) => castUp a.it b.it (.atom n)
      let pat := Format.text (Term.tuple (names.map Term.atom)).fmt.pretty
      pure (.paren (.matchOn x [(pat, .tuple parts)]))
    | .IterT s .List, .IterT t .List =>
      let inner ← castUp s.it t.it (.atom "a")
      pure (.call "List.map" [.lam ["a"] inner, x])
    | .IterT s .Opt, .IterT t .Opt =>
      let inner ← castUp s.it t.it (.atom "a")
      pure (.call "Option.map" [.lam ["a"] inner, x])
    | _, _ =>
      fail s!"unsupported upcast from {render (typTerm env [] sub).fmt} \
        to {render (typTerm env [] sup).fmt}"

/-- The projection of `x : sup` to `sub`, an `Option` term. -/
partial def castDown (sub sup : typ') (x : Term) : CgM Term := do
  let env := (← read).env
  let sub := env.resolve sub
  let sup := env.resolve sup
  if typEq sub sup then pure (.call "pure" [x])
  else match sub, sup with
    | .NumT .NatT, .NumT .IntT => pure (.call "Num.toNat?" [x])
    | .VarT .., .VarT .. => pure (.call (env.q (downName sub sup)) [x])
    | .TupleT ss, .TupleT ts =>
      let names := (List.range ss.length).map fun i => s!"c{i}"
      let parts ← ((ss.zip ts).zip names).mapM fun ((a, b), n) => castDown a.it b.it (.atom n)
      let stmts := (names.zip parts).map fun (n, p) => Format.text s!"let {n} ← " ++ p.fmt
      pure (.paren (.matchOn x [(Format.text (Term.tuple (names.map Term.atom)).fmt.pretty,
        doOfRendered stmts (.tuple (names.map Term.atom)))]))
    | .IterT s .List, .IterT t .List =>
      let inner ← castDown s.it t.it (.atom "a")
      pure (.call "List.mapM" [.lam ["a"] inner, x])
    | .IterT s .Opt, .IterT t .Opt =>
      let inner ← castDown s.it t.it (.atom "a")
      pure (.paren (.matchOn x [(Format.text "none", .atom "pure none"),
        (Format.text "some a", .call "Option.map some" [inner])]))
    | _, _ =>
      fail s!"unsupported downcast from {render (typTerm env [] sup).fmt} \
        to {render (typTerm env [] sub).fmt}"

/-- Whether `x : sup` is a `sub`, a `Bool` term: mirrors `Value.Match.sub`. -/
partial def isSub (sub sup : typ') (x : Term) : CgM Term := do
  let env := (← read).env
  let sub := env.resolve sub
  let sup := env.resolve sup
  if typEq sub sup then pure (.atom "true")
  else match sub, sup with
    | .NumT .NatT, .NumT .IntT => pure (.call "decide" [.binop "≤" (.atom "0") x])
    | .VarT .., .VarT .. => pure (.call (env.q (isName sub sup)) [x])
    | .TupleT ss, .TupleT ts =>
      let names := (List.range ss.length).map fun i => s!"c{i}"
      let parts ← ((ss.zip ts).zip names).mapM fun ((a, b), n) => isSub a.it b.it (.atom n)
      let conj := parts.foldl (fun acc p => Term.binop "&&" acc p) (.atom "true")
      pure (.paren (.matchOn x [(Format.text (Term.tuple (names.map Term.atom)).fmt.pretty, conj)]))
    | .IterT s .List, .IterT t .List =>
      let inner ← isSub s.it t.it (.atom "a")
      pure (.call "List.all" [x, .lam ["a"] inner])
    | .IterT s .Opt, .IterT t .Opt =>
      let inner ← isSub s.it t.it (.atom "a")
      pure (.call "Option.all" [.lam ["a"] inner, x])
    | _, _ =>
      fail s!"unsupported subtype check of {render (typTerm env [] sup).fmt} \
        against {render (typTerm env [] sub).fmt}"

end

/-! ## Expressions -/

mutual

/-- Compile an expression to a pure term, hoisting what can fail. -/
partial def compileExp (e : exp) : CgM Term := do
  let env := (← read).env
  match e.it with
  | .BoolE b => pure (.atom (toString b))
  | .NumE (.Nat n) => pure (.ascribe (.natLit n) (.atom "Nat"))
  | .NumE (.Int i) => pure (.ascribe (.intLit i) (.atom "Int"))
  | .TextE s => pure (.textLit s)
  | .VarE i => pure (var i.it [])
  | .UnE op optyp a =>
    let t ← compileExp a
    match op, optyp with
    | .NotOp, _ => pure (.prefixOp "!" t)
    | .PlusOp, _ => pure t
    | .MinusOp, .NatT => pure (.prefixOp "-" (.call "Int.ofNat" [t]))
    | .MinusOp, _ => pure (.prefixOp "-" t)
  | .BinE op optyp a b =>
    let l ← compileExp a
    let r ← compileExp b
    -- the operand kind decides, as `Num.bin` does: `optyp` names the result
    let optyp : Lang.Il.optyp := match env.resolve a.note with
      | .NumT .NatT => .NatT
      | .NumT .IntT => .IntT
      | _ => optyp
    match op, optyp with
    | .AndOp, _ => pure (.binop "&&" l r)
    | .OrOp, _ => pure (.binop "||" l r)
    | .ImplOp, _ => pure (.binop "||" (.prefixOp "!" l) r)
    | .EquivOp, _ => pure (.binop "==" l r)
    | .AddOp, _ => pure (.binop "+" l r)
    | .SubOp, .NatT => pure (.call "Num.natSub" [l, r])
    | .SubOp, _ => pure (.binop "-" l r)
    | .MulOp, _ => pure (.binop "*" l r)
    | .DivOp, .NatT => hoistErr (← typOf e.note) (.call "Num.natDiv?" [l, r])
    | .DivOp, _ => hoistErr (← typOf e.note) (.call "Num.intDiv?" [l, r])
    | .ModOp, .NatT => hoistErr (← typOf e.note) (.call "Num.natMod?" [l, r])
    | .ModOp, _ => hoistErr (← typOf e.note) (.call "Num.intMod?" [l, r])
    | .PowOp, _ => hoistErr (← typOf e.note) (.call "Num.pow?" [l, r])
  | .CmpE op _ a b =>
    let l ← compileExp a
    let r ← compileExp b
    match op with
    | .EqOp => pure (.binop "==" l r)
    | .NeOp => pure (.binop "!=" l r)
    | .LtOp => pure (.call "decide" [.binop "<" l r])
    | .GtOp => pure (.call "decide" [.binop ">" l r])
    | .LeOp => pure (.call "decide" [.binop "≤" l r])
    | .GeOp => pure (.call "decide" [.binop "≥" l r])
  | .UpCastE typ a =>
    let t ← compileExp a
    castUp a.note typ.it t
  | .DownCastE typ a =>
    let t ← compileExp a
    let m ← castDown typ.it a.note t
    hoistErr (← typOf e.note) m
  | .SubE a typ _ =>
    let t ← compileExp a
    isSub typ.it a.note t
  | .MatchE a p =>
    let t ← compileExp a
    match p with
    | .CaseP m =>
      let (ctor, refutable) ← ctorFor a.note m
      if !refutable then pure (.atom "true")
      else
        let arity := Mixfix.arity m
        let wild := String.join ((List.range arity).map fun _ => " _")
        pure (.paren (.matchOn t [(Format.text (ctor ++ wild), .atom "true"),
          (Format.text "_", .atom "false")]))
    | .ListP .Cons => pure (.prefixOp "!" (.call "List.isEmpty" [t]))
    | .ListP (.Fixed n) => pure (.binop "==" (.call "List.length" [t]) (.natLit n.toNat))
    | .ListP .Nil => pure (.call "List.isEmpty" [t])
    | .OptP .Some => pure (.call "Option.isSome" [t])
    | .OptP .None => pure (.call "Option.isNone" [t])
  | .TupleE es => .tuple <$> es.mapM compileExp
  | .CaseE notexp =>
    let (ctor, _) ← ctorFor e.note (Mixfix.to_mixop notexp)
    let args ← (Mixfix.args notexp).mapM compileExp
    pure (.call ctor args)
  | .StrE fields =>
    let (tid, _) ← fieldsOf e.note
    let vals ← fields.mapM fun (a, f) => do pure (Names.fieldName a.it, ← compileExp f)
    pure (.ascribe (.structInst none vals) (.atom (env.q (Names.typeName tid))))
  | .OptE (some a) => do pure (.call "some" [← compileExp a])
  | .OptE none => pure (.ascribe (.atom "none") (← typOf e.note))
  | .ListE [] => pure (.ascribe (.atom "[]") (← typOf e.note))
  | .ListE es => .list <$> es.mapM compileExp
  | .ConsE h t => do pure (.binop "::" (← compileExp h) (← compileExp t))
  | .CatE l r => do pure (.binop "++" (← compileExp l) (← compileExp r))
  | .MemE a s => do pure (.call "List.elem" [← compileExp a, ← compileExp s])
  | .LenE a =>
    let t ← compileExp a
    match env.resolve a.note with
    | .TextT => pure (.call "P4SpecTec.ByteText.length" [t])
    | _ => pure (.call "List.length" [t])
  | .DotE a atm => do pure (.proj (← compileExp a) (Names.fieldName atm.it))
  | .IdxE b i =>
    let tb ← compileExp b
    let ti ← compileExp i
    match env.resolve b.note, env.resolve i.note with
    | .TextT, _ => hoistErr (← typOf e.note) (.call "Iter.idxText" [tb, ti])
    | _, .NumT .IntT => hoistErr (← typOf e.note) (.call "Iter.idxInt" [tb, ti])
    | _, _ => hoistErr (← typOf e.note) (.call "Iter.idx" [tb, ti])
  | .SliceE b l h =>
    let tb ← compileExp b
    let tl ← compileExp l
    let th ← compileExp h
    match env.resolve b.note with
    | .TextT => hoistErr (← typOf e.note) (.call "Iter.sliceText" [tb, tl, th])
    | _ => hoistErr (← typOf e.note) (.call "Iter.slice" [tb, tl, th])
  | .UpdE b p f =>
    let tb ← compileExp b
    let tf ← compileExp f
    match dotPath p with
    | some [] => pure tf
    | some fields => pure (.structInst (some tb) [(".".intercalate fields, tf)])
    | none =>
      match p.it with
      | .IdxP q i =>
        match q.it, env.resolve q.note, env.resolve i.note with
        | .RootP, .IterT _ .List, .NumT .NatT =>
          -- Upstream evaluates the base, replacement, then path index.
          let ti ← compileExp i
          hoistErr (← typOf e.note) (.call "Iter.setIdx" [tb, ti, tf])
        | .RootP, .TextT, .NumT .NatT =>
          let ti ← compileExp i
          hoistErr (← typOf e.note) (.call "P4SpecTec.ByteText.setIdx" [tb, ti, tf])
        | _, _, _ => fail "nested or non-natural indexed path update is not supported (design 5.4)"
      | _ => fail "sliced path updates are not supported (design section 5.4)"
  | .CallE i targs args =>
    let ctx ← read
    let info := match env.funcs.get? i.it with
      | some info => info
      | none => { kind := .defined, tparams := [], params := [], ret := .TextT, file := "" }
    let named := (info.tparams.zip targs).map fun (p, t) =>
      Term.atomicRaw (Format.text s!"({Names.tparamName p} := " ++ (typTerm env [] t.it).fmt ++ ")")
    let argTerms ← args.mapM fun a => match a.it with
      | .ExpA x => compileExp x
      | .DefA d => pure (.atom (Names.funcName d.it))
    let f := if ctx.externs.contains i.it then env.q ("Externs." ++ Names.funcName i.it)
      else env.q (Names.funcName i.it)
    let t ← fresh
    emit (.call t (← typOf e.note) (.call f (named ++ argTerms)))
    pure (.atom t)
  | .IterE inner ie =>
    match iterVar? e with
    | some (i, is) => pure (var i is)
    | none => compileIter inner ie.iter ie.vars

/-- Hoist an `Eval` term into a temporary of type `ty`. -/
partial def hoist (ty : Term) (m : Term) : CgM Term := do
  let t ← fresh
  emit (.bind t ty m)
  pure (.atom t)

/-- Hoist an `Option` term whose `none` is an error (`Eval.err?`). -/
partial def hoistErr (ty : Term) (m : Term) : CgM Term := do
  let t ← fresh
  emit (.opt t ty m)
  pure (.atom t)

/-- The field chain of a dotted path, innermost first; `none` for indexing. -/
partial def dotPath (p : path) : Option (List String) :=
  match p.it with
  | .RootP => some []
  | .DotP q a => (dotPath q).map (· ++ [Names.fieldName a.it])
  | _ => none

/-- An iterated expression over its variables. -/
partial def compileIter (inner : exp) (iter : iter) (vars : List Lang.Il.var) : CgM Term := do
  let inners := vars.map fun v => Names.varName v.id.it v.iters
  let outers := vars.map fun v => var v.id.it (v.iters ++ [iter])
  let types ← vars.mapM fun v => typOf (varTyp v)
  let (body, stmts) ← subBlock (compileExp inner)
  match iter with
  | .List =>
    if vars.isEmpty then pure (.atom "[]")
    else
      let (z, pat) := zipped outers inners
      let b := zipBinder pat types
      if stmts.isEmpty then pure (.call "List.map" [.lamF b body, z])
      else
        let t ← fresh
        emit (.mapM t (← typOf inner.note) b (inners.zip types) stmts body z)
        pure (.atom t)
  | .Opt =>
    if vars.isEmpty then pure (.call "some" [body])
    else if stmts.isEmpty then
      match outers, inners with
      | [o], [n] => pure (.call "Option.map" [.lam [n] body, o])
      | _, _ =>
        let binds := (inners.zip outers).map fun (n, o) => Format.text s!"let {n} ← " ++ o.fmt
        pure (doOfRendered binds body)
    else
      let somePat := "(" ++ ", ".intercalate (inners.map fun n => s!"some {n}") ++ ")"
      let nonePat := "(" ++ ", ".intercalate (inners.map fun _ => "none") ++ ")"
      hoist (← typOf (.IterT (mkPhrase inner.note) .Opt)) (.paren (.matchOn (.tuple outers) [
        (Format.text somePat, doOf stmts (.call "some" [body])),
        (Format.text nonePat, .atom "pure none"),
        (Format.text "_", .atom "throw Fail.err")]))

end

/-! ## Patterns -/

mutual

/-- Bind the pattern `p` to the term `v`: statements. -/
partial def assign (p : exp) (v : Term) : CgM Unit := do
  match iterVar? p with
  | some (i, is) => emit (.have_ (Names.varName i is) v)
  | none =>
  match p.it with
  | .VarE i => emit (.have_ (Names.varName i.it []) v)
  | .TupleE ps =>
    let (vars, todo) ← binders ps
    let names := vars.map (·.1)
    emit (.letPat (Term.tuple (names.map Term.atom)).fmt (Term.tuple (names.map Term.atom)) vars v
      false)
    for (q, n) in todo do assign q (.atom n)
  | .CaseE notexp =>
    let (ctor, refutable) ← ctorFor p.note (Mixfix.to_mixop notexp)
    let (vars, todo) ← binders (Mixfix.args notexp)
    let names := vars.map (·.1)
    -- the dotted form: `let C a := v` would define a local function `C`
    let dotted := "." ++ (ctor.splitOn ".").getLast!
    emit (.letPat (Term.patApp dotted names) (.call ctor (names.map Term.atom)) vars v refutable)
    for (q, n) in todo do assign q (.atom n)
  | .StrE fields =>
    let (vars, todo) ← binders (fields.map (·.2))
    let names := vars.map (·.1)
    let anon := Format.text ("⟨" ++ ", ".intercalate names ++ "⟩")
    emit (.letPat anon (.atomicRaw anon) vars v false)
    for (q, n) in todo do assign q (.atom n)
  | .OptE (some q) =>
    let (vars, todo) ← binders [q]
    let n := vars.head!.1
    emit (.letPat (Format.text s!"some {n}") (.call "some" [.atom n]) vars v true)
    for (q, n) in todo do assign q (.atom n)
  | .OptE none => emit (.letPat (Format.text "none") (.atom "none") [] v true)
  | .ListE ps =>
    let (vars, todo) ← binders ps
    let names := vars.map (·.1)
    emit (.letPat (Term.list (names.map Term.atom)).fmt (Term.list (names.map Term.atom)) vars v
      true)
    for (q, n) in todo do assign q (.atom n)
  | .ConsE h t =>
    let (vars, todo) ← binders [h, t]
    let names := vars.map (·.1)
    emit (.letPat (Format.text s!"{names[0]!} :: {names[1]!}")
      (.binop "::" (.atom names[0]!) (.atom names[1]!)) vars v true)
    for (q, n) in todo do assign q (.atom n)
  | .IterE inner ie => assignIter inner ie.iter ie.vars v
  | _ => fail s!"unsupported pattern"

/-- Binder names for sub-patterns, with their types: variables bind
directly, anything else gets a temporary to be matched afterwards. -/
partial def binders (ps : List exp) : CgM (List (String × Term) × List (exp × String)) := do
  let mut vars : List (String × Term) := []
  let mut todo : List (exp × String) := []
  for q in ps do
    let ty ← typOf q.note
    match iterVar? q with
    | some (i, is) => vars := vars ++ [(Names.varName i is, ty)]
    | none =>
      let t ← fresh
      vars := vars ++ [(t, ty)]
      todo := todo ++ [(q, t)]
  pure (vars, todo)

/-- Bind an iterated pattern: match every element and collect the
variables' bindings into lists (or options). Mirrors `assign_iter_exp`. -/
partial def assignIter (inner : exp) (iter : iter) (vars : List Lang.Il.var) (v : Term) :
    CgM Unit := do
  let inners := vars.map fun w => Names.varName w.id.it w.iters
  let outers := vars.map fun w => Names.varName w.id.it (w.iters ++ [iter])
  let innerTypes ← vars.mapM fun w => typOf (varTyp w)
  let ((), stmts) ← subBlock (assign inner (.atom "elem"))
  let result := Term.tuple (inners.map Term.atom)
  let elemTy ← typOf inner.note
  let elem := Term.binder (Format.text "elem") elemTy.fmt
  let t ← fresh
  match iter with
  | .List =>
    emit (.mapM t (tupleType innerTypes) elem [("elem", elemTy)] stmts result v)
    for (o, proj) in outers.zip (projections outers.length) do
      emit (unzipStmt o t proj)
  | .Opt =>
    let someRes := Term.tuple (inners.map fun n => Term.call "some" [.atom n])
    let noneRes := Term.tuple (inners.map fun _ => Term.atom "none")
    emit (.bind t (tupleType (innerTypes.map fun ty => Term.call "Option" [ty]))
      (Term.paren (.matchOn v [
        (Format.text "none", .call "pure" [noneRes]),
        (Format.text "some elem", doOf stmts someRes)])))
    for (o, proj) in outers.zip (projections outers.length) do
      emit (.have_ o (.atom s!"{t}{proj}"))

end

/-! ## Premises -/

/-- The lifted call of a relation's run function on input terms, and
whether the relation is extern. -/
def relCall (id : String) (ins : List Term) : CgM (Term × Bool) := do
  let ctx ← read
  let extern := ctx.externs.contains id
  let f := if extern then ctx.env.q ("Externs." ++ Names.relName id)
    else ctx.env.q (Names.relName id ++ ".run")
  pure (.call "ExceptT.mk" [.call f ins], extern)

/-- Split a relation's arguments into inputs and outputs by the hint. -/
def splitArgs {α : Type} (inputs : List Nat) (args : List α) : List α × List α :=
  let indexed := args.zipIdx
  (indexed.filter (fun (_, i) => inputs.contains i) |>.map (·.1),
   indexed.filter (fun (_, i) => !inputs.contains i) |>.map (·.1))

/-- The type of a relation's outputs, as a tuple. -/
def relOutType (id : String) : CgM Term := do
  let env := (← read).env
  match env.rels.get? id with
  | some info =>
    let (_, outs) := splitArgs info.inputs info.args
    pure (tupleType (← outs.mapM typOf))
  | none => fail s!"unknown relation {id}"

mutual

/-- Compile a premise into statements. -/
partial def compilePrem (p : prem) : CgM Unit := do
  match p.it with
  | .RulePr i notexp inputs =>
    let (ins, outs) := splitArgs (inputs.map (·.toNat)) (Mixfix.args notexp)
    let inTerms ← ins.mapM compileExp
    let (call, extern) ← relCall i.it inTerms
    let ty ← relOutType i.it
    match outs with
    | [] => emit (.rel "_" ty i.it inTerms extern call)
    | [o] =>
      let t ← fresh
      emit (.rel t ty i.it inTerms extern call)
      assign o (.atom t)
    | os =>
      let t ← fresh
      emit (.rel t ty i.it inTerms extern call)
      let (vars, todo) ← binders os
      let names := vars.map (·.1)
      emit (.letPat (Term.tuple (names.map Term.atom)).fmt (Term.tuple (names.map Term.atom)) vars
        (.atom t) false)
      for (q, n) in todo do assign q (.atom n)
  | .IfPr e =>
    let t ← compileExp e
    emit (.check t)
  | .IfHoldPr i notexp =>
    let inTerms ← (Mixfix.args notexp).mapM compileExp
    let (call, extern) ← relCall i.it inTerms
    emit (.rel "_" (.atom "Unit") i.it inTerms extern call)
  | .IfNotHoldPr i notexp =>
    let inTerms ← (Mixfix.args notexp).mapM compileExp
    let (call, extern) ← relCall i.it inTerms
    emit (.notHold i.it inTerms extern call)
  | .LetPr l r =>
    let t ← compileExp r
    assign l t
  | .IterPr q ip => iterPrem q ip.iter ip.vars_bound ip.vars_bind
  | .DebugPr _ => pure ()

/-- An iterated premise: run the premise per batch of bound values and
collect the binding variables. Mirrors `eval_iter_prem`. -/
partial def iterPrem (q : prem) (iter : iter) (bound bind : List Lang.Il.var) : CgM Unit := do
  let boundIn := bound.map fun w => Names.varName w.id.it w.iters
  let boundOut := bound.map fun w => var w.id.it (w.iters ++ [iter])
  let bindIn := bind.map fun w => Names.varName w.id.it w.iters
  let bindOut := bind.map fun w => Names.varName w.id.it (w.iters ++ [iter])
  let boundTypes ← bound.mapM fun w => typOf (varTyp w)
  let bindTypes ← bind.mapM fun w => typOf (varTyp w)
  let ((), stmts) ← subBlock (compilePrem q)
  let result := Term.tuple (bindIn.map Term.atom)
  let t ← fresh
  match iter with
  | .List =>
    if bound.isEmpty then
      for o in bindOut do emit (.have_ o (.atom "[]"))
    else
      let (z, pat) := zipped boundOut boundIn
      let b := zipBinder pat boundTypes
      emit (.mapM t (tupleType bindTypes) b (boundIn.zip boundTypes) stmts result z)
      for (o, proj) in bindOut.zip (projections bindOut.length) do
        emit (unzipStmt o t proj)
  | .Opt =>
    let someRes := Term.tuple (bindIn.map fun n => Term.call "some" [.atom n])
    let noneRes := Term.tuple (bindIn.map fun _ => Term.atom "none")
    if bound.isEmpty then
      -- `sub_opt ctx []` is `Some ctx`: the premise runs once and binds `some`
      for st in stmts do emit st
      for (o, n) in bindOut.zip bindIn do emit (.have_ o (.atom s!"some {n}"))
    else
      let somePat := "(" ++ ", ".intercalate (boundIn.map fun n => s!"some {n}") ++ ")"
      let nonePat := "(" ++ ", ".intercalate (boundIn.map fun _ => "none") ++ ")"
      let arms := [(Format.text somePat, doOf stmts someRes),
        (Format.text nonePat, Term.call "pure" [noneRes])] ++
        (if bound.length > 1 then [(Format.text "_", Term.atom "throw Fail.err")] else [])
      emit (.bind t (tupleType (bindTypes.map fun ty => Term.call "Option" [ty]))
        (Term.paren (.matchOn (.tuple boundOut) arms)))
      for (o, proj) in bindOut.zip (projections bindOut.length) do
        emit (.have_ o (.atom s!"{t}{proj}"))

end

/-- Compile premises then a result expression into a `do` term. -/
def compileBody (prems : List prem) (result : List exp) : CgM Term := do
  let ((), stmts) ← subBlock do
    for p in prems do compilePrem p
  let (res, stmts2) ← subBlock (result.mapM compileExp)
  pure (doOf (stmts ++ stmts2) (.tuple res))

/-- Run a compilation for one definition. -/
def run {α : Type} (ctx : Ctx) (m : CgM α) : Except String α :=
  (m.run ctx |>.run' {})

/-! ## The subtype pairs a spec needs -/

/-- Collect the `(sub, sup)` variant pairs of every cast and check in an
expression, resolved through aliases. -/
partial def pairsOfExp (env : Env) (e : exp) : List (typ' × typ') :=
  let here := match e.it with
    | .UpCastE t a => pairOf (env.resolve a.note) (env.resolve t.it)
    | .DownCastE t a => pairOf (env.resolve t.it) (env.resolve a.note)
    | .SubE a t _ => pairOf (env.resolve t.it) (env.resolve a.note)
    | _ => []
  here ++ (children e).flatMap (pairsOfExp env)
where
  /-- The pairs of a cast between two types, structurally. -/
  pairOf : typ' → typ' → List (typ' × typ')
    | s@(.VarT ..), t@(.VarT ..) => if typEq s t then [] else [(s, t)]
    | .TupleT ss, .TupleT ts =>
      (ss.zip ts).flatMap fun (a, b) => pairOf (env.resolve a.it) (env.resolve b.it)
    | .IterT s _, .IterT t _ => pairOf (env.resolve s.it) (env.resolve t.it)
    | _, _ => []
  /-- The direct sub-expressions. -/
  children (e : exp) : List exp :=
    match e.it with
    | .UnE _ _ a | .UpCastE _ a | .DownCastE _ a | .SubE a _ _ | .MatchE a _ | .LenE a
    | .DotE a _ | .OptE (some a) | .IterE a _ => [a]
    | .BinE _ _ a b | .CmpE _ _ a b | .ConsE a b | .CatE a b | .MemE a b | .IdxE a b => [a, b]
    | .SliceE a b c => [a, b, c]
    | .UpdE a p b => [a, b] ++ pathExps p
    | .TupleE es | .ListE es => es
    | .CaseE n => Mixfix.args n
    | .StrE fs => fs.map (·.2)
    | .CallE _ _ args => args.filterMap fun a => match a.it with | .ExpA x => some x | _ => none
    | _ => []
  /-- The expressions inside a path. -/
  pathExps (p : path) : List exp :=
    match p.it with
    | .RootP => []
    | .IdxP q i => pathExps q ++ [i]
    | .SliceP q l h => pathExps q ++ [l, h]
    | .DotP q _ => pathExps q

/-- The expressions of a premise. -/
partial def expsOfPrem (p : prem) : List exp :=
  match p.it with
  | .RulePr _ n _ | .IfHoldPr _ n | .IfNotHoldPr _ n => Mixfix.args n
  | .IfPr e | .DebugPr e => [e]
  | .LetPr l r => [l, r]
  | .IterPr q _ => expsOfPrem q

/-- The expressions of a definition. -/
def expsOfDef (d : Lang.Al.def) : List exp :=
  match d.it with
  | .RelD _ _ _ groups eg _ =>
    let ofGroup (g : Lang.Al.rulegroup) : List exp :=
      let (_, (sig, ins, prems), paths) := g.it
      sig ++ ins ++ prems.flatMap expsOfPrem ++
        paths.flatMap fun (_, ps, outs) => ps.flatMap expsOfPrem ++ outs
    groups.flatMap ofGroup ++ (match eg with
      | some e =>
        let (_, (sig, ins, prems), (_, ps, outs)) := e.it
        sig ++ ins ++ prems.flatMap expsOfPrem ++ ps.flatMap expsOfPrem ++ outs
      | none => [])
  | .FuncDecD _ _ _ _ clauses ec _ =>
    let ofClause (c : clause) : List exp :=
      let (args, out, prems) := c.it
      (args.filterMap fun a => match a.it with | .ExpA x => some x | _ => none) ++ [out] ++
        prems.flatMap expsOfPrem
    clauses.flatMap ofClause ++ (match ec with | some c => ofClause c | none => [])
  | .TableDecD _ _ _ rows _ =>
    rows.flatMap fun r =>
      let (pats, args, out, prems) := r.it
      pats ++ (args.filterMap fun a => match a.it with | .ExpA x => some x | _ => none) ++ [out] ++
        prems.flatMap expsOfPrem
  | _ => []

/-- Collect full bridge applications in encounter order, deduplicating
by region-independent type equality rather than by their head names. -/
def pairsOfSpec (env : Env) (spec : Lang.Al.spec) : List (typ' × typ') :=
  let pairs := spec.flatMap fun d => (expsOfDef d).flatMap (pairsOfExp env)
  pairs.foldl (init := []) fun acc (s, t) =>
    if acc.any (fun (a, b) => typEq s a && typEq t b) then acc else acc ++ [(s, t)]

/-- The functions an expression calls. -/
partial def callsOfExp (e : exp) : List String :=
  (match e.it with | .CallE i _ _ => [i.it] | _ => []) ++ (pairsOfExp.children e).flatMap callsOfExp

/-- The relations and functions a premise calls. -/
partial def callsOfPrem (p : prem) : List String :=
  (match p.it with
    | .RulePr i _ _ | .IfHoldPr i _ | .IfNotHoldPr i _ => [i.it]
    | _ => []) ++ (expsOfPrem p).flatMap callsOfExp ++
    (match p.it with | .IterPr q _ => callsOfPrem q | _ => [])

/-- The relations and functions a definition calls. -/
def callsOfDef (d : Lang.Al.def) : List String :=
  let ofExp := callsOfExp
  let ofPrem := callsOfPrem
  match d.it with
  | .RelD _ _ _ groups eg _ =>
    let ofGroup (g : Lang.Al.rulegroup) : List String :=
      let (_, (_, _, prems), paths) := g.it
      prems.flatMap ofPrem ++
        paths.flatMap fun (_, ps, outs) => ps.flatMap ofPrem ++ outs.flatMap ofExp
    groups.flatMap ofGroup ++ (match eg with
      | some e =>
        let (_, (_, _, prems), (_, ps, outs)) := e.it
        prems.flatMap ofPrem ++ ps.flatMap ofPrem ++ outs.flatMap ofExp
      | none => [])
  | .FuncDecD _ _ _ _ clauses ec _ =>
    let ofClause (c : clause) : List String :=
      let (_, out, prems) := c.it
      ofExp out ++ prems.flatMap ofPrem
    clauses.flatMap ofClause ++ (match ec with | some c => ofClause c | none => [])
  | .TableDecD _ _ _ rows _ =>
    rows.flatMap fun r => let (_, _, out, prems) := r.it; ofExp out ++ prems.flatMap ofPrem
  | _ => []

end P4SpecTec.Codegen.Exp
