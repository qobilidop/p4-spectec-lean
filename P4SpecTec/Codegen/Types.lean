import P4SpecTec.Codegen.Env
import P4SpecTec.Codegen.Fmt
import P4SpecTec.Codegen.Graph

/-!
Types: `TypD` to `inductive`, `structure` or `abbrev`, recursive groups
to `mutual` blocks, and for every type the `ToValue` instance (its IL
value), the `BEq` instance through it, and the `OfValue` decoder. Also the
injection, projection and check between a subtype and a supertype, which
the expression compiler uses for `UpCastE`, `DownCastE` and `SubE`
(design section 5.4).

Encodings, each documented at its function:

- A type alias inside a recursive group is unfolded in the group's
  constructor arguments and defined as an `abbrev` after the group.
- Variant cases are named by the naming rule; constructor arguments are
  named after their types.
- `toValue` is structural: a helper per nested container type occurrence.
- `ofValue` takes fuel, since it recurses on the untyped value.
-/

namespace P4SpecTec.Codegen.Types

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al

/-- The marker in an `unfold` list standing for every alias. -/
def unfoldAll : String := "*"

/-- Structural equality of types, ignoring regions. -/
partial def typEq : typ' → typ' → Bool
  | .BoolT, .BoolT => true
  | .NumT a, .NumT b => a == b
  | .TextT, .TextT => true
  | .VarT a as, .VarT b bs => a.it == b.it && as.length == bs.length &&
    (as.zip bs).all fun (x, y) => typEq x.it y.it
  | .TupleT as, .TupleT bs =>
    as.length == bs.length && (as.zip bs).all fun (x, y) => typEq x.it y.it
  | .IterT a i, .IterT b j => typEq a.it b.it && i == j
  | .FuncT _ as a, .FuncT _ bs b => as.length == bs.length &&
    (as.zip bs).all (fun (x, y) => typEq x.it y.it) && typEq a.it b.it
  | _, _ => false

/-- The Lean type of a spec type. Names in `unfold` are aliases replaced by
their bodies; `unfoldAll` stands for every alias, which constructor
arguments of a recursive group need, since the kernel's nested-inductive
check does not see through an `abbrev`. -/
partial def typTerm (env : Env) (unfold : List String) : typ' → Term
  | .BoolT => .atom "Bool"
  | .NumT .NatT => .atom "Nat"
  | .NumT .IntT => .atom "Int"
  | .TextT => .atom "String"
  | .VarT i targs =>
    if unfold.contains i.it || (unfold.contains unfoldAll && env.isAlias i.it) then
      match env.instantiate i.it (targs.map (·.it)) with
      | some (.PlainT t) => typTerm env unfold t.it
      | _ => .atom (env.q (Names.typeName i.it))
    else if !env.types.contains i.it then .atom (Names.tparamName i.it)  -- a type parameter
    else .call (env.q (Names.typeName i.it)) (targs.map fun t => typTerm env unfold t.it)
  | .TupleT [] => .atom "Unit"
  | .TupleT ts => prod (ts.map fun t => typTerm env unfold t.it)
  | .IterT t .Opt => .call "Option" [typTerm env unfold t.it]
  | .IterT t .List => .call "List" [typTerm env unfold t.it]
  | .FuncT _ ts t =>
    let args := ts.map fun t => typTerm env unfold t.it
    ⟨Format.group (Format.joinSep ((args ++ [typTerm env unfold t.it]).map (·.arg))
      (" →" ++ Format.line)), false⟩
where
  /-- A right-nested product. -/
  prod : List Term → Term
    | [] => .atom "Unit"
    | [t] => t
    | t :: ts => .binop "×" t (prod ts)

/-- A Lean term for a `typ'` as an IL value note: `Value.varT "id"` without
type arguments, since notes on generated values are dummies. -/
def noteTerm : typ' → Term
  | .BoolT => .atom "Lang.Il.typ'.BoolT"
  | .NumT .NatT => .atom "(Lang.Il.typ'.NumT .NatT)"
  | .NumT .IntT => .atom "(Lang.Il.typ'.NumT .IntT)"
  | .TextT => .atom "Lang.Il.typ'.TextT"
  | .VarT i _ => .call "Prelude.Value.varT" [.strLit i.it]
  | _ => .atom "Lang.Il.typ'.TextT"

/-- A Lean term for an atom. -/
def atomTerm (a : Atom.t) : Term :=
  match a with
  | .Keyword s => .paren (.call ".Keyword" [.strLit s])
  | .Tag s => .paren (.call ".Tag" [.strLit s])
  | .Operator s => .paren (.call ".Operator" [.strLit s])
  | a => .atom ("." ++ Atom.string_of_atom_name a)
where
  /-- The constructor name of a symbol atom. -/
  Atom.string_of_atom_name : Atom.t → String
    | .Sub => "Sub" | .Sup => "Sup" | .Turnstile => "Turnstile" | .Tilesturn => "Tilesturn"
    | .Arrow => "Arrow" | .ArrowSub => "ArrowSub" | .DoubleArrowSub => "DoubleArrowSub"
    | .DoubleArrowLong => "DoubleArrowLong" | .SqArrow => "SqArrow" | .SqArrowStar => "SqArrowStar"
    | .Dot => "Dot" | .Dot2 => "Dot2" | .Dot3 => "Dot3" | .Semicolon => "Semicolon"
    | .Colon => "Colon" | .ColonEq => "ColonEq" | .Tilde2 => "Tilde2" | .Backslash => "Backslash"
    | .LAngle => "LAngle" | .RAngle => "RAngle" | .LParen => "LParen" | .RParen => "RParen"
    | .LBrack => "LBrack" | .RBrack => "RBrack" | .LBrace => "LBrace" | .RBrace => "RBrace"
    | _ => "Keyword"

/-- A Lean term for a mixop, as `Mixfix.t Unit`. -/
partial def mixopTerm : Mixfix.mixop → Term
  | .Arg () => .atom "(.Arg ())"
  | .Atom a => .paren (.call ".Atom" [.call "Prelude.Value.atom" [atomTerm a.it]])
  | .Brack l m r =>
    .paren (.call ".Brack" [.call "Prelude.Value.atom" [atomTerm l.it], mixopTerm m,
      .call "Prelude.Value.atom" [atomTerm r.it]])
  | .Infix l a r =>
    .paren (.call ".Infix" [mixopTerm l, .call "Prelude.Value.atom" [atomTerm a.it], mixopTerm r])
  | .Seq ms => .paren (.call ".Seq" [.list (ms.map mixopTerm)])

/-- A Lean term filling a mixop with argument terms, as `Mixfix.t value`. -/
partial def mixfixTerm (m : Mixfix.mixop) (args : List Term) : Term :=
  (go m args).1
where
  /-- Fill left to right. -/
  go : Mixfix.mixop → List Term → Term × List Term
    | .Arg (), a :: as => (.paren (.call ".Arg" [a]), as)
    | .Arg (), [] => (.atom "(.Arg (panic! \"arity\"))", [])
    | .Atom a, as => (.paren (.call ".Atom" [.call "Prelude.Value.atom" [atomTerm a.it]]), as)
    | .Brack l m r, as =>
      let (m', as) := go m as
      (.paren (.call ".Brack" [.call "Prelude.Value.atom" [atomTerm l.it], m',
        .call "Prelude.Value.atom" [atomTerm r.it]]), as)
    | .Infix l a r, as =>
      let (l', as) := go l as
      let (r', as) := go r as
      (.paren (.call ".Infix" [l', .call "Prelude.Value.atom" [atomTerm a.it], r']), as)
    | .Seq ms, as =>
      let (ms', as) := ms.foldl (init := ([], as)) fun (acc, as) m =>
        let (m', as) := go m as
        (acc ++ [m'], as)
      (.paren (.call ".Seq" [.list ms']), as)

/-- Names for a case's arguments: after the type when it is named, else
`x`, made distinct with numeric suffixes and from the type parameters. -/
def argNames (tparams : List String) (ts : List typ') : List String := Id.run do
  let base := ts.map fun
    | .VarT i _ => if tparams.contains i.it then "x" else i.it
    | .BoolT => "b" | .NumT .NatT => "n" | .NumT .IntT => "i" | .TextT => "s"
    | .IterT (⟨.VarT i _, _, _⟩) _ => if tparams.contains i.it then "x" else i.it
    | _ => "x"
  let mut seen : List String := []
  let mut out : List String := []
  for b in base do
    let n := seen.count b
    let name := if n == 0 && !(base.count b > 1) then b else b ++ "_" ++ toString (n + 1)
    seen := seen ++ [b]
    out := out ++ [Names.escape name]
  pure out

/-- The constructor names of a variant, made distinct. -/
def ctorNames (cases : List typcase) : List String := Id.run do
  let base := cases.map fun c => Names.ctorName c.nottyp.it
  let mut out : List String := []
  for b in base do
    let n := out.count b
    out := out ++ [if n == 0 then b else b ++ "_" ++ toString (n + 1)]
  pure out

/-- The type parameter binders of a type. -/
def tparamBinders (tparams : List String) : Format :=
  if tparams.isEmpty then Format.nil
  else Format.text (" " ++ " ".intercalate (tparams.map fun p => s!"({Names.tparamName p} : Type)"))

/-- The instance binders `[ToValue K]` for type parameters. -/
def tparamInstances (tparams : List String) : Format :=
  if tparams.isEmpty then Format.nil
  else Format.text (" " ++ " ".intercalate (tparams.map fun p =>
    s!"[ToValue {Names.tparamName p}]"))

/-- The implicit binders `{K : Type}` for type parameters. -/
def tparamImplicits (tparams : List String) : Format :=
  if tparams.isEmpty then Format.nil
  else Format.text (" {" ++ " ".intercalate (tparams.map Names.tparamName) ++ " : Type}")

/-- The type applied to its parameters, qualified. -/
def selfType (env : Env) (id : String) (tparams : List String) : Term :=
  .call (env.q (Names.typeName id)) (tparams.map fun p => .atom (Names.tparamName p))

/-- One type declaration. `unfold` lists the aliases of the recursive group. -/
def typeDecl (env : Env) (unfold : List String) (id : String) (tparams : List String)
    (dt : deftyp') : Format :=
  let name := Names.typeName id
  match dt with
  | .PlainT t =>
    Format.text s!"abbrev {name}" ++ tparamBinders tparams ++ " : Type := " ++
      (typTerm env unfold t.it).fmt
  | .StructT fields =>
    let fs := fields.map fun (a, t) =>
      Term.hardLine ++ Format.text (Names.fieldName a.it ++ " : ") ++ (typTerm env unfold t.it).fmt
    Format.text s!"structure {name}" ++ tparamBinders tparams ++ " where" ++
      Format.nest 2 (Format.join fs)
  | .VariantT cases =>
    let names := ctorNames cases
    let cs := (cases.zip names).map fun (c, cname) =>
      let args := Mixfix.args c.nottyp.it
      let anames := argNames tparams (args.map (·.it))
      let binders := (anames.zip args).map fun (a, t) =>
        Format.line ++ Term.binder (Format.text a) (typTerm env unfold t.it).fmt
      Term.hardLine ++
        Format.group (Format.nest 4 (Format.text ("| " ++ cname) ++ Format.join binders))
    Format.text s!"inductive {name}" ++ tparamBinders tparams ++ " where" ++
      Format.nest 2 (Format.join cs)

/-! ## Value encoders

`toValue` is structural. The helpers for nested containers are generated
per group: every argument type that mentions a group member and is not a
member itself gets a helper named `toValue_<n>`, and helpers recurse into
lists, options, tuples and other spec types by unfolding their cases. -/

/-- Whether a type mentions one of the names. -/
def mentions (names : List String) (t : typ') : Bool :=
  (Env.typeRefs t).any names.contains

/-- The state of helper generation for a group. -/
structure HelperState where
  /-- The group's name, prefixed to helper names so groups in one module do
  not clash. -/
  prefix_ : String := ""
  /-- Helpers requested, keyed by the rendered type, with their index. -/
  requested : List (String × Nat × typ') := []
  /-- Helper definitions generated so far. -/
  decls : List Format := []

/-- A match arm `| pat => body` that breaks after the arrow. -/
def arm (pat : Format) (body : Format) : Format :=
  Term.hardLine ++
    Format.group (Format.nest 4 (Format.text "| " ++ pat ++ " =>" ++ Format.line ++ body))

/-- The mutual function name for a member type's `toValue`. -/
def toValueName (id : String) : String := Names.typeName id ++ ".toValue"

/-- Every reference to `toValue` in generated code is qualified, since
`toValue` inside `def T.toValue` would name the function being defined. -/
def toValueRef : String := "ToValue.toValue"

/-- The term converting a value of type `t` to an IL value; requests a
helper when `t` is a container over group members. -/
partial def toValueTerm (env : Env) (members : List String) (t : typ') (x : Term) :
    StateM HelperState Term := do
  match t with
  | .VarT i [] =>
    if members.contains i.it then pure (.call (env.q (toValueName i.it)) [x])
    else pure (.call toValueRef [x])
  | _ =>
    if !mentions members t then pure (.call toValueRef [x])
    else
      let key := render (typTerm env [] t).fmt
      let st ← get
      let idx ← match st.requested.find? (·.1 == key) with
        | some (_, idx, _) => pure idx
        | none =>
          let idx := st.requested.length
          set { st with requested := st.requested ++ [(key, idx, t)] }
          -- generate the helper body now, recursively
          let body ← helperBody idx t
          modify fun st => { st with decls := st.decls ++ [body] }
          pure idx
      match t with
      | .IterT _ .List =>
        pure (.call "Runtime.Value.Make.list" [noteTerm t, .call s!"{st.prefix_}toValue_{idx}" [x]])
      | .IterT _ .Opt =>
        pure (.call "Runtime.Value.Make.opt" [noteTerm t, .call s!"{st.prefix_}toValue_{idx}" [x]])
      | _ => pure (.call s!"{st.prefix_}toValue_{idx}" [x])
where
  /-- The helper for a container type. -/
  helperBody (idx : Nat) (t : typ') : StateM HelperState Format := do
    let name := s!"{(← get).prefix_}toValue_{idx}"
    let ty := (typTerm env [] t).fmt
    match t with
    | .IterT e .List =>
      let inner ← toValueTerm env members e.it (.atom "x")
      pure <| Format.text s!"def {name} : " ++ ty ++ " → List Lang.Il.value" ++ Format.nest 2 (
        Format.line ++ "| [] => []" ++
        Format.line ++ "| x :: xs => " ++ inner.arg ++ " :: " ++ name ++ " xs")
    | .IterT e .Opt =>
      let inner ← toValueTerm env members e.it (.atom "x")
      pure <| Format.text s!"def {name} : " ++ ty ++ " → Option Lang.Il.value" ++ Format.nest 2 (
        Format.line ++ "| none => none" ++
        Format.line ++ "| some x => some " ++ inner.arg)
    | .TupleT ts =>
      let names := (List.range ts.length).map fun i => s!"x{i}"
      let inners ← (ts.zip names).mapM fun (e, n) => toValueTerm env members e.it (.atom n)
      pure <| Format.text s!"def {name} : " ++ ty ++ " → Lang.Il.value" ++ Format.nest 2 (
        arm (Term.tuple (names.map Term.atom)).fmt
          (Term.call "Runtime.Value.Make.tuple" [noteTerm t, .list inners]).fmt)
    | .VarT i targs =>
      -- a spec type applied to arguments that mention members: unfold its cases
      match env.instantiate i.it (targs.map (·.it)) with
      | some (.PlainT u) =>
        let inner ← toValueTerm env members u.it (.atom "x")
        pure <| Term.defn (Format.text s!"def {name} (x : " ++ ty ++ ") : Lang.Il.value") inner.fmt
      | some (.VariantT cases) =>
        let cnames := ctorNames cases
        let arms ← (cases.zip cnames).mapM fun (c, cname) => do
          let args := Mixfix.args c.nottyp.it
          let anames := (List.range args.length).map fun k => s!"x{k}"
          let inners ← (args.zip anames).mapM fun (a, n) => toValueTerm env members a.it (.atom n)
          pure (arm (Term.patApp ("." ++ cname) anames)
            (Term.call "Runtime.Value.Make.case"
              [noteTerm t, mixfixTerm (Mixfix.to_mixop c.nottyp.it) inners]).fmt)
        pure <| Format.text s!"def {name} : " ++ ty ++ " → Lang.Il.value" ++
          Format.nest 2 (Format.join arms)
      | some (.StructT fields) =>
        let anames := (List.range fields.length).map fun k => s!"x{k}"
        let inners ← (fields.zip anames).mapM fun ((_, ft), n) =>
          toValueTerm env members ft.it (.atom n)
        let pairs := (fields.zip inners).map fun ((a, _), v) =>
          Term.tuple [Term.strLit (Names.atomName a.it), v]
        pure <| Format.text s!"def {name} : " ++ ty ++ " → Lang.Il.value" ++ Format.nest 2 (
          arm (Format.text ("⟨" ++ ", ".intercalate anames ++ "⟩"))
            (Term.call "Runtime.Value.Make.str" [noteTerm t, .list pairs]).fmt)
      | _ => pure (Term.defn (Format.text s!"def {name} (x : " ++ ty ++ ") : Lang.Il.value")
        (Format.text "ToValue.toValue x"))
    | _ => pure (Term.defn (Format.text s!"def {name} (x : " ++ ty ++ ") : Lang.Il.value")
      (Format.text "ToValue.toValue x"))

/-- The `toValue` functions of a group, as one mutual block, followed by the
instances. Alias members convert through their bodies. -/
def toValueDecls (env : Env) (group : List (String × List String × deftyp')) : Format := Id.run do
  let members := group.map (·.1)
  let first := group.head?.map (·.1) |>.getD "t"
  let mut st : HelperState := { prefix_ := Names.typeName first ++ "." }
  let mut fns : List Format := []
  for (tid, tparams, dt) in group do
    let self := selfType env tid tparams
    let name := toValueName tid
    let header := Format.text s!"def {name}" ++ tparamImplicits tparams ++ tparamInstances tparams
    let note := noteTerm (.VarT (mkPhrase tid) [])
    match dt with
    | .PlainT t =>
      let (inner, st') := (toValueTerm env members t.it (.atom "x")).run st
      st := st'
      fns := fns ++ [Term.defn (header ++ " (x : " ++ self.fmt ++ ") : Lang.Il.value") inner.fmt]
    | .StructT fields =>
      let anames := (List.range fields.length).map fun k => s!"x{k}"
      let mut inners : List Term := []
      for ((_, ft), n) in fields.zip anames do
        let (v, st') := (toValueTerm env members ft.it (.atom n)).run st
        st := st'; inners := inners ++ [v]
      let pairs := (fields.zip inners).map fun ((a, _), v) =>
        Term.tuple [Term.strLit (Names.atomName a.it), v]
      fns := fns ++ [header ++ " : " ++ self.fmt ++ " → Lang.Il.value" ++ Format.nest 2 (
        arm (Format.text ("⟨" ++ ", ".intercalate anames ++ "⟩"))
          (Term.call "Runtime.Value.Make.str" [note, .list pairs]).fmt)]
    | .VariantT cases =>
      let cnames := ctorNames cases
      let mut arms : List Format := []
      for (c, cname) in cases.zip cnames do
        let args := Mixfix.args c.nottyp.it
        let anames := (List.range args.length).map fun k => s!"x{k}"
        let mut inners : List Term := []
        for (a, n) in args.zip anames do
          let (v, st') := (toValueTerm env members a.it (.atom n)).run st
          st := st'; inners := inners ++ [v]
        arms := arms ++ [arm (Term.patApp ("." ++ cname) anames)
          (Term.call "Runtime.Value.Make.case"
            [note, mixfixTerm (Mixfix.to_mixop c.nottyp.it) inners]).fmt]
      fns := fns ++ [header ++ " : " ++ self.fmt ++ " → Lang.Il.value" ++
        Format.nest 2 (Format.join arms)]
  let decls := fns ++ st.decls
  let block := if decls.length == 1 then joinDecls decls else mutualBlock decls
  let instances := group.map fun (tid, tparams, _) =>
    Term.defn (Format.text "instance" ++ tparamImplicits tparams ++ tparamInstances tparams ++
      " : ToValue " ++ (selfType env tid tparams).arg)
      (Format.text ("⟨" ++ env.q (toValueName tid) ++ "⟩")) ++ Term.hardLine ++
    Term.defn (Format.text "instance" ++ tparamImplicits tparams ++ tparamInstances tparams ++
      " : BEq " ++ (selfType env tid tparams).arg) (Format.text "⟨valueEq⟩")
  pure (block ++ Format.line ++ Format.line ++ joinDecls instances)

/-! ## Value decoders

`ofValue fuel v` decodes an IL value into the generated type; `none` when
the value has another shape or the fuel runs out. -/

/-- The mutual function name for a member type's decoder. -/
def ofValueName (id : String) : String := Names.typeName id ++ ".ofValue"

/-- The instance binders `[OfValue K]` for type parameters. -/
def ofValueInstances (tparams : List String) : Format :=
  if tparams.isEmpty then Format.nil
  else Format.text (" " ++ " ".intercalate (tparams.map fun p =>
    s!"[OfValue {Names.tparamName p}]"))

/-- The decoder term for a value term `v` at type `t`. -/
partial def ofValueTerm (env : Env) (members : List String) (t : typ') (v : Term) : Term :=
  match t with
  | .VarT i targs =>
    if members.contains i.it then .call (env.q (ofValueName i.it)) [.atom "fuel", v]
    else if mentions members t then
      -- a spec type over members: decode through its instantiated definition
      match env.instantiate i.it (targs.map (·.it)) with
      | some (.PlainT u) => ofValueTerm env members u.it v
      | some (.VariantT cases) =>
        let cnames := ctorNames cases
        let alts := (cases.zip cnames).map fun (c, cname) =>
          let args := Mixfix.args c.nottyp.it
          let anames := (List.range args.length).map fun k => s!"a{k}"
          let decs := (args.zip anames).map fun (a, n) =>
            Term.atomicRaw (Format.text "(← " ++
              (ofValueTerm env members a.it (.atom n)).fmt ++ ")")
          Term.paren (.doBlock [
            Term.letStmt (Format.text "some " ++ (Term.list (anames.map Term.atom)).fmt)
              (.call "Prelude.Value.caseArgs"
                [.atom "c", mixopTerm (Mixfix.to_mixop c.nottyp.it)]) (some "none"),
            Format.text "pure " ++
              (Term.call (env.q (Names.typeName i.it) ++ "." ++ cname) decs).arg])
        .paren (.matchOn (.proj v "it") [
          (Format.text ".CaseV c", alternatives alts),
          (Format.text "_", .atom "none")])
      | _ => .call "OfValue.ofValue" [.atom "fuel", v]
    else .call "OfValue.ofValue" [.atom "fuel", v]
  | .IterT e .List =>
    if mentions members t then
      .paren (.matchOn (.proj v "it") [
        (Format.text ".ListV vs",
          .call "vs.mapM" [.lam ["x"] (ofValueTerm env members e.it (.atom "x"))]),
        (Format.text "_", .atom "none")])
    else .call "OfValue.ofValue" [.atom "fuel", v]
  | .IterT e .Opt =>
    if mentions members t then
      .paren (.matchOn (.proj v "it") [
        (Format.text ".OptV none", .atom "some none"),
        (Format.text ".OptV (some x)",
          .call "Option.map some" [ofValueTerm env members e.it (.atom "x")]),
        (Format.text "_", .atom "none")])
    else .call "OfValue.ofValue" [.atom "fuel", v]
  | .TupleT ts =>
    if mentions members t then
      let names := (List.range ts.length).map fun i => s!"x{i}"
      let decs := (ts.zip names).map fun (e, n) =>
        Format.text "(← " ++ (ofValueTerm env members e.it (.atom n)).fmt ++ ")"
      .paren (.matchOn (.proj v "it") [
        (Format.text ".TupleV " ++ (Term.list (names.map Term.atom)).fmt,
          .paren (.doBlock [Format.text "pure " ++ (Term.tuple (decs.map Term.raw)).fmt])),
        (Format.text "_", .atom "none")])
    else .call "OfValue.ofValue" [.atom "fuel", v]
  | _ => .call "OfValue.ofValue" [.atom "fuel", v]
where
  /-- `a <|> b <|> ...`. -/
  alternatives : List Term → Term
    | [] => .atom "none"
    | [t] => t
    | t :: ts => .binop "<|>" t (alternatives ts)

/-- The `ofValue` functions of a group, one mutual block, then instances. -/
def ofValueDecls (env : Env) (group : List (String × List String × deftyp')) : Format := Id.run do
  let members := group.map (·.1)
  let mut fns : List Format := []
  for (tid, tparams, dt) in group do
    let self := selfType env tid tparams
    let name := ofValueName tid
    let insts := ofValueInstances tparams
    let header := Format.group (Format.nest 4 (Format.text s!"def {name}" ++
      tparamImplicits tparams ++ insts ++ " :" ++ Format.line ++ "Nat → Lang.Il.value → Option " ++
      self.arg))
    let body := match dt with
      | .PlainT t =>
        Format.text "| fuel + 1, v => " ++ (ofValueTerm env members t.it (.atom "v")).fmt
      | .StructT fields =>
        let anames := (List.range fields.length).map fun k => s!"f{k}"
        let pats := Term.list (anames.map fun n => Term.raw (Format.text ("(_, " ++ n ++ ")")))
        let decs := (fields.zip anames).map fun ((_, ft), n) =>
          Format.text "(← " ++ (ofValueTerm env members ft.it (.atom n)).fmt ++ ")"
        Format.text "| fuel + 1, v => " ++ (Term.matchOn (.atom "v.it") [
          (Format.text ".StructV " ++ pats.fmt,
            .paren (.doBlock [Format.text "pure ⟨" ++ Format.joinSep decs ", " ++ "⟩"])),
          (Format.text "_", .atom "none")]).fmt
      | .VariantT cases =>
        let cnames := ctorNames cases
        let alts := (cases.zip cnames).map fun (c, cname) =>
          let args := Mixfix.args c.nottyp.it
          let anames := (List.range args.length).map fun k => s!"a{k}"
          let decs := (args.zip anames).map fun (a, n) =>
            Term.atomicRaw (Format.text "(← " ++
              (ofValueTerm env members a.it (.atom n)).fmt ++ ")")
          Term.paren (.doBlock [
            Term.letStmt (Format.text "some " ++ (Term.list (anames.map Term.atom)).fmt)
              (.call "Prelude.Value.caseArgs"
                [.atom "c", mixopTerm (Mixfix.to_mixop c.nottyp.it)]) (some "none"),
            Format.text "pure " ++
              (Term.call (env.q (Names.typeName tid) ++ "." ++ cname) decs).arg])
        Format.text "| fuel + 1, v => " ++ (Term.matchOn (.atom "v.it") [
          (Format.text ".CaseV c", ofValueTerm.alternatives alts),
          (Format.text "_", .atom "none")]).fmt
    fns := fns ++ [header ++ Format.nest 2 (Format.line ++ "| 0, _ => none" ++ Format.line ++ body)]
  let block := if fns.length == 1 then joinDecls fns else mutualBlock fns
  let instances := group.map fun (tid, tparams, _) =>
    let insts := ofValueInstances tparams
    Term.defn (Format.text "instance" ++ tparamImplicits tparams ++ insts ++ " : OfValue " ++
      (selfType env tid tparams).arg) (Format.text ("⟨" ++ env.q (ofValueName tid) ++ "⟩"))
  pure (block ++ Format.line ++ Format.line ++ joinDecls instances)

/-! ## Subtypes -/

/-- The name of the injection from `s` into `t`. -/
def upName (s t : String) : String := Names.typeName s ++ ".to_" ++ Names.escape t

/-- The name of the projection from `t` to `s`. -/
def downName (s t : String) : String := Names.typeName t ++ ".of_" ++ Names.escape s

/-- The name of the check that a `t` is an `s`. -/
def isName (s t : String) : String := Names.typeName t ++ ".is_" ++ Names.escape s

/-- The injection, projection and check between variant `s` and variant
`t`, by matching cases with equal mixops. -/
def subtypeDecls (env : Env) (s t : String) : Except String Format := do
  let sCases := (env.variantCases s []).getD []
  let tCases := (env.variantCases t []).getD []
  let sNames := ctorNames sCases
  let tNames := ctorNames tCases
  let mut ups : List Format := []
  let mut downs : List Format := []
  let mut checks : List Format := []
  for (sc, sn) in sCases.zip sNames do
    match (tCases.zip tNames).find? fun (tc, _) => Mixfix.eq_mixop sc.nottyp.it tc.nottyp.it with
    | some (tc, tn) =>
      -- the bridge maps a case to the case with the same mixop; the AL's
      -- `RecurseSC` would also check the arguments' values against the
      -- subtype's argument types, which is only needed when those differ
      let sArgs := (Mixfix.args sc.nottyp.it).map (·.it)
      let tArgs := (Mixfix.args tc.nottyp.it).map (·.it)
      if sArgs.length != tArgs.length || !((sArgs.zip tArgs).all fun (a, b) => typEq a b) then
        throw s!"subtype {s} of {t}: case {Mixfix.to_string sc.nottyp.it} has different \
          argument types in the two (design 5.4: not supported)"
      let n := sArgs.length
      let xs := (List.range n).map fun k => s!"x{k}"
      let arm (l : Format) (r : Format) : Format :=
        Format.group (Format.nest 2 (Format.text "| " ++ l ++ " =>" ++ Format.line ++ r))
      ups := ups ++ [arm (Term.patApp ("." ++ sn) xs) (Term.patApp ("." ++ tn) xs)]
      downs := downs ++ [arm (Term.patApp ("." ++ tn) xs)
        (Format.text "some " ++ Format.paren (Term.patApp ("." ++ sn) xs))]
      checks := checks ++ [arm (Term.patApp ("." ++ tn) (xs.map fun _ => "_")) (Format.text "true")]
    | none => pure ()
  let sT := env.q (Names.typeName s)
  let tT := env.q (Names.typeName t)
  let arms (l : List Format) := Format.nest 2 (Format.join (l.map (Term.hardLine ++ ·)))
  let sig (name : String) (ts : List String) : Format :=
    Format.group (Format.nest 4 (Format.text s!"def {name} :" ++ Format.line ++
      Term.arrows (ts.map Format.text)))
  let up := sig (upName s t) [sT, tT] ++ arms ups
  let partial_ := downs.length < tCases.length
  let down := sig (downName s t) [tT, s!"Option {sT}"] ++
    arms (downs ++ (if partial_ then [Format.text "| _ => none"] else []))
  let chk := sig (isName s t) [tT, "Bool"] ++
    arms (checks ++ (if partial_ then [Format.text "| _ => false"] else []))
  pure (joinDecls [up, down, chk])

end P4SpecTec.Codegen.Types
