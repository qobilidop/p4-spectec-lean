import P4SpecTec.Codegen.Exp.Context
import P4SpecTec.Codegen.Exp.Traversal

/-!
Expressions, patterns and premises to Lean, in the executable encoding.

The target is a `do` block in `Eval` or explicit-state `StateEval`:
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
  raw Option-result ABI that `partial_correctness` needs, with a final state
  parameter in stateful mode. Calls never supply or reset that state.
-/

namespace P4SpecTec.Codegen.Exp

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types

/-- The type of an iteration variable: its base type under its dimensions
(`Typ.Make.iterate`). -/
def varTyp (w : Lang.Il.var) : typ' :=
  w.iters.foldl (fun t i => .IterT (mkPhrase t) i) w.typ.it

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

/-- Compile the actual supplied subcheck when runtime extensions invalidate a
static source-membership shortcut. Unsupported recursive checks fail generation. -/
def runtimeSubcheck (t : typ') (sc : subcheck) (x : Term) : CgM Term := do
  match sc with
  | .SkipSC => pure (.atom "true")
  | .MixopSC mixops =>
    let some (tid, cases, names) ← variantOf t
      | fail "runtime extern extension: mixop subcheck needs a variant carrier"
    let env := (← read).env
    let selected := (cases.zip names).filter fun (c, _) =>
      mixops.any fun m => Mixfix.eq_mixop c.nottyp.it m
    let arms := selected.map fun (c, n) =>
      let wild := (List.replicate (Mixfix.arity c.nottyp.it) "_")
      (Term.patApp (env.q (Names.typeName tid) ++ "." ++ n) wild, Term.atom "true")
    let partial_ := selected.length < cases.length || env.representation.hasRawExtern tid
    pure (.paren (.matchOn x
      (arms ++ if partial_ then [(Format.text "_", .atom "false")] else [])))
  | _ => fail "runtime extern extension: unsupported subcheck on an affected carrier"

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
  | .SubE a typ sc =>
    let t ← compileExp a
    if env.runtimeAffected a.note then runtimeSubcheck a.note sc t
    else isSub typ.it a.note t
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
    if ctx.callbacks.contains i.it && !targs.isEmpty then
      fail "polymorphic callback applications are not supported"
    let info := match env.funcs.get? i.it with
      | some info => info
      | none => { kind := .defined, tparams := [], params := [], ret := .TextT, file := "" }
    let named := (info.tparams.zip targs).map fun (p, t) =>
      Term.atomicRaw (Format.text s!"({Names.tparamName p} := " ++ (typTerm env [] t.it).fmt ++ ")")
    let argTerms ← args.mapM fun a => match a.it with
      | .ExpA x => compileExp x
      | .DefA d => do
        unless ctx.callbacks.contains d.it do
          match env.funcs.get? d.it with
          | some info =>
            if info.kind == .builtin || info.kind == .extern then
              fail "raw builtin/extern callback aliases are not supported"
          | none => fail s!"unknown function argument: {d.it}"
        pure (.atom (if ctx.callbacks.contains d.it then Names.funcName d.it
          else if ctx.externs.contains d.it then env.q ("Externs." ++ Names.funcName d.it)
          else env.q (Names.funcName d.it)))
    let f := if ctx.callbacks.contains i.it then Names.funcName i.it
      else if ctx.externs.contains i.it then env.q ("Externs." ++ Names.funcName i.it)
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
    if vars.isEmpty then
      for stmt in stmts do emit stmt
      pure (.call "some" [body])
    else if stmts.isEmpty && vars.length == 1 then
      match outers, inners with
      | [o], [n] => pure (.call "Option.map" [.lam [n] body, o])
      | _, _ => fail "internal error: optional-expression binder count"
    else
      let somePat := "(" ++ ", ".intercalate (inners.map fun n => s!"some {n}") ++ ")"
      let nonePat := "(" ++ ", ".intercalate (inners.map fun _ => "none") ++ ")"
      let arms := [
        (Format.text somePat, doOfWith (← read).env.mode stmts (.call "some" [body])),
        (Format.text nonePat, Term.atom "pure none")] ++
        (if vars.length > 1 then [(Format.text "_", Term.atom "throw Fail.err")] else [])
      hoist (← typOf (.IterT (mkPhrase inner.note) .Opt))
        (.paren (.matchOn (.tuple outers) arms))

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
        (Format.text "some elem", doOfWith (← read).env.mode stmts someRes)])))
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
  let call := Term.call "ExceptT.mk" [.call f ins]
  -- An explicit-state relation call is memoized as upstream's cache mode memoizes it;
  -- `memoRun` is the call by definition (`Prelude/Memo.lean`).
  if extern || ctx.env.mode != .freshState then pure (call, extern)
  else pure (.call "memoRun" [.strLit id, .list (ins.map fun t => .call "MemoKey.of" [t]), call],
    extern)

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
  | .DebugPr e => let _ ← compileExp e; pure ()

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
      let arms := [(Format.text somePat, doOfWith (← read).env.mode stmts someRes),
        (Format.text nonePat, Term.call "pure" [noneRes])] ++
        (if bound.length > 1 then [(Format.text "_", Term.atom "throw Fail.err")] else [])
      let resultTy := tupleType (bindTypes.map fun ty => Term.call "Option" [ty])
      if (← read).env.mode == .freshState then
        emit (.optM t resultTy (boundIn.zip boundTypes) stmts someRes noneRes boundOut)
      else
        emit (.bind t resultTy (Term.paren (.matchOn (.tuple boundOut) arms)))
      for (o, proj) in bindOut.zip (projections bindOut.length) do
        emit (.have_ o (.atom s!"{t}{proj}"))

end

/-- Compile premises then a result expression into a `do` term. -/
def compileBody (prems : List prem) (result : List exp) : CgM Term := do
  let ((), stmts) ← subBlock do
    for p in prems do compilePrem p
  let (res, stmts2) ← subBlock (result.mapM compileExp)
  pure (doOfWith (← read).env.mode (stmts ++ stmts2) (.tuple res))

end P4SpecTec.Codegen.Exp
