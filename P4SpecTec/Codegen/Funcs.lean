import P4SpecTec.Codegen.Exp

/-!
Functions: `FuncDecD` to a `def` returning `Option`, whose body tries the
clauses in order (`invoke_defined_func`, sequential mode) and the `else`
clause last; `BuiltinDecD` to a wrapper around the prelude's port;
`TableDecD` to a function by cases over the rows. Every function takes a
fuel argument first; a recursive group consumes one unit per call
(design section 5.3, "explicit fuel").
-/

namespace P4SpecTec.Codegen.Funcs

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.IL
open P4SpecTec.AL
open P4SpecTec.Codegen.Types
open P4SpecTec.Codegen.Exp

/-- The parameter names of a generated function. -/
def paramNames (n : Nat) : List String := (List.range n).map fun i => s!"p{i}"

/-- The binders of a generated function: type parameters, the `Externs`
instance when needed, the fuel and the parameters. -/
def binders (env : Env) (tparams : List String) (params : List typ') (externs : Bool) : Format :=
  let tps := if tparams.isEmpty then Format.nil
    else Format.text (" {" ++ " ".intercalate (tparams.map Names.tparamName) ++ " : Type}") ++
      Format.text (String.join (tparams.map fun p =>
        s!" [ToValue {Names.tparamName p}] [BEq {Names.tparamName p}]"))
  let ext := if externs then Format.text " [Externs]" else Format.nil
  let ps := (paramNames params.length).zip params
  let binder (n : String) (t : typ') : Format :=
    Format.line ++ Format.paren (Format.text (n ++ " : ") ++ (typTerm env [] t).fmt)
  Format.group (Format.nest 4 (tps ++ ext ++ Format.line ++ "(fuel : Nat)" ++
    Format.join (ps.map fun (n, t) => binder n t)))

/-- Wrap a body in the fuel match when the group is recursive. -/
def withFuel (recursive : Bool) (body : Term) : Format :=
  if recursive then
    Format.nest 2 (Format.text "match fuel with" ++ Format.line ++ "| 0 => none" ++ Format.line ++
      "| fuel + 1 =>" ++ Format.nest 2 (Format.line ++ body.fmt))
  else body.fmt

/-- The parameter types of a function. -/
def paramTypes (params : List param') : List typ' :=
  params.map fun
    | .ExpP t => t.it
    | .DefP _ _ ps t =>
      .FuncT [] (ps.map fun p => match p.it with | .ExpP t => t | .DefP _ _ _ t => t) t

/-- A clause as an alternative: bind the arguments, run the premises,
produce the result. -/
def clauseTerm (c : clause) : CgM Term := do
  let (args, out, prems) := c.it
  let ((), stmts) ← subBlock do
    for (a, n) in args.zip (paramNames args.length) do
      match a.it with
      | .ExpA pat => assign pat (.atom n)
      | .DefA d => emit (Format.text s!"let {Names.funcName d.it} := {n}")
    for p in prems do compilePrem p
  let (res, stmts2) ← subBlock (compileExp out)
  pure (doOf (stmts ++ stmts2) res)

/-- A defined function. -/
def funcDecl (ctx : Ctx) (recursive externs : Bool) (id : String) (tparams : List String)
    (params : List param') (ret : typ') (clauses : List clause) (elseclause : Option clause) :
    Except String Format := do
  let alts ← Exp.run ctx do
    let cs ← clauses.mapM clauseTerm
    let es ← match elseclause with
      | some c => do pure [← clauseTerm c]
      | none => pure []
    pure (alternatives (cs ++ es))
  let header := Format.text s!"def {Names.funcName id}" ++
    binders ctx.env tparams (paramTypes params) externs ++ " : Option " ++
    (typTerm ctx.env [] ret).arg ++ " :="
  pure (header ++ Format.nest 2 (Format.line ++ withFuel recursive alts))

/-- A table function: rows as clauses. -/
def tableDecl (ctx : Ctx) (recursive externs : Bool) (id : String) (params : List param')
    (ret : typ') (rows : List AL.tablerow) : Except String Format := do
  let alts ← Exp.run ctx do
    let rs ← rows.mapM fun r => do
      let (_, args, out, prems) := r.it
      clauseTerm { r with it := (args, out, prems) }
    pure (alternatives rs)
  let header := Format.text s!"def {Names.funcName id}" ++
    binders ctx.env [] (paramTypes params) externs ++ " : Option " ++
    (typTerm ctx.env [] ret).arg ++ " :="
  pure (header ++ Format.nest 2 (Format.line ++ withFuel recursive alts))

/-! ## Builtins

Each wrapper adapts the spec's signature to the prelude's port: sets and
maps are unwrapped to the element lists of the `set` and `pair` cases,
naturals are widened to integers where the port takes `Int`, and a port
returning `Option` is the result directly. -/

/-- The single constructor of the stdlib's `set` and `pair`, by shape,
qualified. -/
def stdCtor (env : Env) (tid : String) : Option String :=
  match env.variantCases tid [] with
  | some [c] => some (env.q (Names.typeName tid) ++ "." ++ Names.ctorName c.nottyp.it)
  | _ => none

/-- The dotted form of a constructor, for patterns. -/
def dotted (c : String) : String := "." ++ (c.splitOn ".").getLast!

/-- Unwrap a `set K` to its element list. -/
def setElems (env : Env) (x : Term) : Option Term := do
  let c ← stdCtor env "set"
  pure (.paren (.matchOn x [(Format.text s!"{dotted c} l", .atom "l")]))

/-- Wrap an element list as a `set K`. -/
def setMk (env : Env) (x : Term) : Option Term := do
  let c ← stdCtor env "set"
  pure (.call c [x])

/-- Unwrap a `map K V` to its list of key-value pairs. -/
def mapElems (env : Env) (x : Term) : Option Term := do
  let s ← stdCtor env "set"
  let p ← stdCtor env "pair"
  pure (.paren (.matchOn x [(Format.text s!"{dotted s} l",
    .call "List.map" [.paren (.raw (Format.text s!"fun | {dotted p} k v => (k, v)")), .atom "l"])]))

/-- Wrap a list of key-value pairs as a `map K V`. -/
def mapMk (env : Env) (x : Term) : Option Term := do
  let s ← stdCtor env "set"
  let p ← stdCtor env "pair"
  pure (.call s [.call "List.map" [.paren (.raw (Format.text s!"fun (k, v) => {p} k v")), x]])

/-- Widen a parameter to `Int` when the spec declares it `nat`. -/
def toInt (t : typ') (x : Term) : Term :=
  match t with
  | .NumT .NatT => .call "Int.ofNat" [x]
  | _ => x

/-- The body of a builtin wrapper: an `Option` term over the parameters. -/
def builtinBody (env : Env) (id : String) (params : List typ') : Except String Term := do
  let ps := (paramNames params.length).map Term.atom
  let p (i : Nat) : Term := ps.getD i (.atom "_")
  let pt (i : Nat) : typ' := params.getD i .TextT
  let pureOf (t : Term) : Term := .call "pure" [t]
  let need {α : Type} (what : String) : Option α → Except String α
    | some a => pure a
    | none => throw s!"builtin {id} needs the stdlib type {what}"
  match id with
  | "print_" => pure (pureOf (.call "Value.print" [.call toValueRef [p 0]]))
  | "text_to_int" => pure (.call "Builtins.Texts.text_to_int" [p 0])
  | "int_to_text" => pure (pureOf (.call "Builtins.Texts.int_to_text" [p 0]))
  | "split_text" => pure (.call "Builtins.Texts.split_text" [p 0, p 1])
  | "strip_prefix" => pure (.call "Builtins.Texts.strip_prefix" [p 0, p 1])
  | "strip_suffix" => pure (.call "Builtins.Texts.strip_suffix" [p 0, p 1])
  | "strip_all_whitespace" => pure (pureOf (.call "Builtins.Texts.strip_all_whitespace" [p 0]))
  | "rev_" => pure (pureOf (.call "Builtins.Lists.rev_" [p 0]))
  | "concat_" => pure (pureOf (.call "Builtins.Lists.concat_" [p 0]))
  | "distinct_" => pure (pureOf (.call "Builtins.Lists.distinct_" [p 0]))
  | "partition_" => pure (pureOf (.call "Builtins.Lists.partition_" [p 0, p 1]))
  | "assoc_" => pure (pureOf (.call "Builtins.Lists.assoc_" [p 0, p 1]))
  | "sort_" => pure (pureOf (.call "Builtins.Lists.sort_" [p 0]))
  | "transpose_" => pure (.call "Builtins.Lists.transpose_" [p 0])
  | "intersect_set" | "union_set" | "diff_set" =>
    let a ← need "set" (setElems env (p 0))
    let b ← need "set" (setElems env (p 1))
    let r ← need "set" (setMk env (.call s!"Builtins.Sets.{id}" [a, b]))
    pure (pureOf r)
  | "unions_set" =>
    let e ← need "set" (setElems env (.atom "s"))
    let inner := Term.call "Builtins.Sets.unions_set" [.call "List.map" [.lam ["s"] e, p 0]]
    let r ← need "set" (setMk env inner)
    pure (pureOf r)
  | "sub_set" | "eq_set" =>
    let a ← need "set" (setElems env (p 0))
    let b ← need "set" (setElems env (p 1))
    pure (pureOf (.call s!"Builtins.Sets.{id}" [a, b]))
  | "find_map" =>
    let m ← need "map" (mapElems env (p 0))
    pure (pureOf (.call "Builtins.Maps.find_map" [m, p 1]))
  | "find_maps" =>
    let e ← need "map" (mapElems env (.atom "m"))
    pure (pureOf (.call "Builtins.Maps.find_maps" [.call "List.map" [.lam ["m"] e, p 0], p 1]))
  | "add_map" | "update_map" =>
    let m ← need "map" (mapElems env (p 0))
    let r ← need "map" (mapMk env (.call s!"Builtins.Maps.{id}" [m, p 1, p 2]))
    pure (pureOf r)
  | "adds_map" =>
    let m ← need "map" (mapElems env (p 0))
    let r ← need "map" (mapMk env (.atom "r"))
    let call := Term.call "Builtins.Maps.adds_map" [m, p 1, p 2]
    pure (.paren (.doBlock [Format.text "let r ← " ++ call.fmt, Format.text "pure " ++ r.arg]))
  | "sum_nat" => pure (pureOf (.call "Builtins.Nats.sum_nat" [p 0]))
  | "max_nat" => pure (.call "Builtins.Nats.max_nat" [p 0])
  | "min_nat" => pure (.call "Builtins.Nats.min_nat" [p 0])
  | "sum_int" => pure (pureOf (.call "Builtins.Ints.sum_int" [p 0]))
  | "max_int" => pure (pureOf (.call "Builtins.Ints.max_int" [p 0]))
  | "min_int" => pure (pureOf (.call "Builtins.Ints.min_int" [p 0]))
  | "shl" | "shr" =>
    pure (.call s!"Builtins.Numerics.{id}" [toInt (pt 0) (p 0), toInt (pt 1) (p 1)])
  | "shr_arith" =>
    pure (.call "Builtins.Numerics.shr_arith"
      [toInt (pt 0) (p 0), toInt (pt 1) (p 1), toInt (pt 2) (p 2)])
  | "pow2" => pure (pureOf (.call "Builtins.Numerics.pow2" [toInt (pt 0) (p 0)]))
  | "bitstr_to_int" | "int_to_bitstr" =>
    pure (.call s!"Builtins.Numerics.{id}" [toInt (pt 0) (p 0), toInt (pt 1) (p 1)])
  | "bits_to_int_unsigned" => pure (pureOf (.call "Builtins.Numerics.bits_to_int_unsigned" [p 0]))
  | "bits_to_int_signed" => pure (.call "Builtins.Numerics.bits_to_int_signed" [p 0])
  | "int_to_bits_unsigned" | "int_to_bits_signed" =>
    pure (.call s!"Builtins.Numerics.{id}" [toInt (pt 0) (p 0), toInt (pt 1) (p 1)])
  | "bneg" => pure (pureOf (.call "Builtins.Numerics.bneg" [toInt (pt 0) (p 0)]))
  | "band" | "bxor" | "bor" =>
    pure (pureOf (.call s!"Builtins.Numerics.{id}" [toInt (pt 0) (p 0), toInt (pt 1) (p 1)]))
  | "bitacc" =>
    pure (.call "Builtins.Numerics.bitacc"
      [toInt (pt 0) (p 0), toInt (pt 1) (p 1), toInt (pt 2) (p 2)])
  | "bitacc_replace" =>
    pure (pureOf (.call "Builtins.Numerics.bitacc_replace"
      [toInt (pt 0) (p 0), toInt (pt 1) (p 1), toInt (pt 2) (p 2), toInt (pt 3) (p 3)]))
  | _ => throw s!"builtin {id} has no port in P4SpecTec.Prelude.Builtins"

/-- A builtin wrapper. -/
def builtinDecl (env : Env) (id : String) (tparams : List String) (params : List param')
    (ret : typ') : Except String Format := do
  let pts := paramTypes params
  let body ← builtinBody env id pts
  let header := Format.text s!"def {Names.funcName id}" ++ binders env tparams pts false ++
    " : Option " ++ (typTerm env [] ret).arg ++ " :="
  pure (header ++ Format.nest 2 (Format.line ++ body.fmt))

/-- The `Externs` class: one field per extern function and relation. -/
def externsClass (env : Env) (defs : List AL.def) : Format :=
  let fields := defs.filterMap fun d => match d.it with
    | .ExternDecD i tparams params ret _ =>
      let pts := paramTypes (params.map (·.it))
      let tps := if tparams.isEmpty then Format.nil
        else Format.text (" {" ++ " ".intercalate (tparams.map fun p => Names.tparamName p.it) ++
          " : Type}")
      some (Format.text (Names.funcName i.it) ++ tps ++ " : " ++
        Term.arrows ([Format.text "Nat"] ++ pts.map (fun t => (typTerm env [] t).arg) ++
          [Format.text "Option " ++ (typTerm env [] ret.it).arg]))
    | .ExternRelD i nottyp inputs _ =>
      let args := (Mixfix.args nottyp.it).map (·.it)
      let (ins, outs) := splitArgs (inputs.map (·.toNat)) args
      some (Format.text (Names.relName i.it) ++ " : " ++
        Term.arrows ([Format.text "Nat"] ++ ins.map (fun t => (typTerm env [] t).arg) ++
          [Format.text "Option " ++ (typTerm.prod (outs.map (typTerm env []))).arg]))
    | _ => none
  Format.text "class Externs where" ++ Format.nest 2 (Format.join (fields.map (Term.hardLine ++ ·)))

end P4SpecTec.Codegen.Funcs
