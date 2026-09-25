import P4SpecTec.Util.Yojson
import P4SpecTec.Lang.Il.Ast

/-!
Not a mirror: this module is ours, placed beside the module whose values it
decodes.

Not a mirror: this module is our own, placed beside the module it decodes.

JSON decoders for the IL, one per type of `P4SpecTec.Lang.Il.Ast`, following
the `[@@deriving yojson]` encoding of `p4spec/lib/lang/il/ast.ml` and the
hand-written `Mixfix.mixop_to_yojson`. The decoders are `partial` because
they recurse through `Lean.Json`, which is not a structural argument; they
are not part of the generated code or of any proof.
-/

namespace P4SpecTec.Lang.Il.Json

open Lean (Json)
open P4SpecTec.Util.Source
open P4SpecTec.Util.Yojson
open P4SpecTec.Lang.Xl
open P4SpecTec.Domain

/-- Decode `Num.t`. -/
def num : D Num.t := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "Nat", #[n] => do
    let i ← bigint n
    if i < 0 then throw "negative nat" else pure (.Nat i.toNat)
  | "Int", #[i] => .Int <$> bigint i
  | _, _ => fail "expected Num.t" j

/-- Decode `Num.typ`. -/
def numtyp : D Num.typ := fun j => do
  match ← variant j with
  | ("NatT", _) => pure .NatT
  | ("IntT", _) => pure .IntT
  | _ => fail "expected Num.typ" j

/-- Decode `id`. -/
def id : D id := phrase str

/-- Decode `Atom.t`. -/
def atom' : D Atom.t := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "Keyword", #[s] => .Keyword <$> str s
  | "Tag", #[s] => .Tag <$> str s
  | "Operator", #[s] => .Operator <$> str s
  | "Sub", _ => pure .Sub | "Sup", _ => pure .Sup
  | "Turnstile", _ => pure .Turnstile | "Tilesturn", _ => pure .Tilesturn
  | "Arrow", _ => pure .Arrow | "ArrowSub", _ => pure .ArrowSub
  | "DoubleArrowSub", _ => pure .DoubleArrowSub | "DoubleArrowLong", _ => pure .DoubleArrowLong
  | "SqArrow", _ => pure .SqArrow | "SqArrowStar", _ => pure .SqArrowStar
  | "Dot", _ => pure .Dot | "Dot2", _ => pure .Dot2 | "Dot3", _ => pure .Dot3
  | "Semicolon", _ => pure .Semicolon | "Colon", _ => pure .Colon | "ColonEq", _ => pure .ColonEq
  | "Tilde2", _ => pure .Tilde2 | "Backslash", _ => pure .Backslash
  | "LAngle", _ => pure .LAngle | "RAngle", _ => pure .RAngle
  | "LParen", _ => pure .LParen | "RParen", _ => pure .RParen
  | "LBrack", _ => pure .LBrack | "RBrack", _ => pure .RBrack
  | "LBrace", _ => pure .LBrace | "RBrace", _ => pure .RBrace
  | _, _ => fail "expected atom" j

/-- Decode `atom`. -/
def atom : D atom := phrase atom'

/-- Decode a mixfix given a decoder for the holes. -/
partial def mixfix {α : Type} (d : D α) : D (Mixfix.t α) := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "Arg", #[x] => .Arg <$> d x
  | "Atom", #[x] => .Atom <$> atom x
  | "Brack", #[l, m, r] => do pure (.Brack (← atom l) (← mixfix d m) (← atom r))
  | "Infix", #[l, x, r] => do pure (.Infix (← mixfix d l) (← atom x) (← mixfix d r))
  | "Seq", #[ms] => .Seq <$> list (mixfix d) ms
  | _, _ => fail "expected mixfix" j

/-- Decode `mixop`. -/
def mixop : D mixop := mixfix unit

/-- Decode `iter`. -/
def iter : D iter := fun j => do
  match ← variant j with
  | ("Opt", _) => pure .Opt
  | ("List", _) => pure .List
  | _ => fail "expected iter" j

/-- Decode `hint`: kept as JSON. -/
def hint : D hint := pure

/-- Decode `Hints.Input.t`. -/
def inputs : D Hints.Input.t := list int

/-- Decode `numop`. -/
def numop : D numop := fun j => do
  match ← variant j with
  | ("DecOp", _) => pure .DecOp
  | ("HexOp", _) => pure .HexOp
  | _ => fail "expected numop" j

/-- Decode `unop`. -/
def unop : D unop := fun j => do
  match ← variant j with
  | ("NotOp", _) => pure .NotOp
  | ("PlusOp", _) => pure .PlusOp
  | ("MinusOp", _) => pure .MinusOp
  | _ => fail "expected unop" j

/-- Decode `binop`. -/
def binop : D binop := fun j => do
  match ← variant j with
  | ("AndOp", _) => pure .AndOp | ("OrOp", _) => pure .OrOp
  | ("ImplOp", _) => pure .ImplOp | ("EquivOp", _) => pure .EquivOp
  | ("AddOp", _) => pure .AddOp | ("SubOp", _) => pure .SubOp
  | ("MulOp", _) => pure .MulOp | ("DivOp", _) => pure .DivOp
  | ("ModOp", _) => pure .ModOp | ("PowOp", _) => pure .PowOp
  | _ => fail "expected binop" j

/-- Decode `cmpop`. -/
def cmpop : D cmpop := fun j => do
  match ← variant j with
  | ("EqOp", _) => pure .EqOp | ("NeOp", _) => pure .NeOp
  | ("LtOp", _) => pure .LtOp | ("GtOp", _) => pure .GtOp
  | ("LeOp", _) => pure .LeOp | ("GeOp", _) => pure .GeOp
  | _ => fail "expected cmpop" j

/-- Decode `optyp`. -/
def optyp : D optyp := fun j => do
  match ← variant j with
  | ("BoolT", _) => pure .BoolT
  | ("NatT", _) => pure .NatT
  | ("IntT", _) => pure .IntT
  | _ => fail "expected optyp" j

/-- Decode `pattern`. -/
def pattern : D pattern := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "CaseP", #[m] => .CaseP <$> mixop m
  | "ListP", #[p] => do
    let (pc, pa) ← variant p
    match pc, pa with
    | "Cons", _ => pure (.ListP .Cons)
    | "Fixed", #[n] => (.ListP ∘ .Fixed) <$> int n
    | "Nil", _ => pure (.ListP .Nil)
    | _, _ => fail "expected list pattern" p
  | "OptP", #[p] => do
    match ← variant p with
    | ("Some", _) => pure (.OptP .Some)
    | ("None", _) => pure (.OptP .None)
    | _ => fail "expected option pattern" p
  | _, _ => fail "expected pattern" j

mutual

/-- Decode `typ'`. -/
partial def typ' : D typ' := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "BoolT", _ => pure .BoolT
  | "NumT", #[t] => .NumT <$> numtyp t
  | "TextT", _ => pure .TextT
  | "VarT", #[i, ts] => do pure (.VarT (← id i) (← list targ ts))
  | "TupleT", #[ts] => .TupleT <$> list typ ts
  | "IterT", #[t, i] => do pure (.IterT (← typ t) (← iter i))
  | "FuncT", #[tps, ts, t] => do pure (.FuncT (← list id tps) (← list typ ts) (← typ t))
  | _, _ => fail "expected typ'" j

/-- Decode `typ`. -/
partial def typ : D typ := phrase typ'

/-- Decode `targ`. -/
partial def targ : D targ := phrase typ'

end

/-- Decode `nottyp`. -/
def nottyp : D nottyp := phrase (mixfix typ)

/-- Decode `typorigin`. -/
def typorigin : D typorigin := phrase fun j => do
  let (i, ts) ← pair id (list targ) j
  pure (.mk i ts)

/-- Decode `typcase`. -/
def typcase : D typcase := fun j => do
  let (n, o, h) ← triple nottyp typorigin (list hint) j
  pure (.mk n o h)

/-- Decode `typfield`. -/
def typfield : D typfield := pair atom typ

/-- Decode `deftyp'`. -/
def deftyp' : D deftyp' := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "PlainT", #[t] => .PlainT <$> typ t
  | "StructT", #[fs] => .StructT <$> list typfield fs
  | "VariantT", #[cs] => .VariantT <$> list typcase cs
  | _, _ => fail "expected deftyp'" j

/-- Decode `deftyp`. -/
def deftyp : D deftyp := phrase deftyp'

/-- Decode `vnote`. -/
def vnote : D vnote := fun j => do
  pure (.mk (← int (← field j "vid")) (← typ' (← field j "typ")) (← int (← field j "vhash")))

mutual

/-- Decode `value'`. -/
partial def value' : D value' := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "BoolV", #[b] => .BoolV <$> bool b
  | "NumV", #[n] => .NumV <$> num n
  | "TextV", #[s] => .TextV <$> str s
  | "StructV", #[fs] => .StructV <$> list (pair atom value) fs
  | "CaseV", #[m] => .CaseV <$> mixfix value m
  | "TupleV", #[vs] => .TupleV <$> list value vs
  | "OptV", #[v] => .OptV <$> opt value v
  | "ListV", #[vs] => .ListV <$> list value vs
  | "FuncV", #[i] => .FuncV <$> id i
  | "ExternV", #[x] => pure (.ExternV x)
  | _, _ => fail "expected value'" j

/-- Decode `value`. -/
partial def value : D value := note_phrase value' vnote

end

/-- Decode `subcheck`. -/
partial def subcheck : D subcheck := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "SkipSC", _ => pure .SkipSC
  | "MixopSC", #[ms] => .MixopSC <$> list mixop ms
  | "TupleSC", #[scs] => .TupleSC <$> list subcheck scs
  | "IterSC", #[i, sc] => do pure (.IterSC (← iter i) (← subcheck sc))
  | "RecurseSC", #[t] => .RecurseSC <$> typ t
  | _, _ => fail "expected subcheck" j

/-- Decode `var`. -/
def var : D var := fun j => do
  let (i, t, is) ← triple id typ (list iter) j
  pure (.mk i t is)

/-- Decode `iterexp`. -/
def iterexp : D iterexp := fun j => do
  let (i, vs) ← pair iter (list var) j
  pure (.mk i vs)

mutual

/-- Decode `exp'`. -/
partial def exp' : D exp' := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "BoolE", #[b] => .BoolE <$> bool b
  | "NumE", #[n] => .NumE <$> num n
  | "TextE", #[s] => .TextE <$> str s
  | "VarE", #[i] => .VarE <$> id i
  | "UnE", #[o, t, e] => do pure (.UnE (← unop o) (← optyp t) (← exp e))
  | "BinE", #[o, t, l, r] => do pure (.BinE (← binop o) (← optyp t) (← exp l) (← exp r))
  | "CmpE", #[o, t, l, r] => do pure (.CmpE (← cmpop o) (← optyp t) (← exp l) (← exp r))
  | "UpCastE", #[t, e] => do pure (.UpCastE (← typ t) (← exp e))
  | "DownCastE", #[t, e] => do pure (.DownCastE (← typ t) (← exp e))
  | "SubE", #[e, t, sc] => do pure (.SubE (← exp e) (← typ t) (← subcheck sc))
  | "MatchE", #[e, p] => do pure (.MatchE (← exp e) (← pattern p))
  | "TupleE", #[es] => .TupleE <$> list exp es
  | "CaseE", #[n] => .CaseE <$> mixfix exp n
  | "StrE", #[fs] => .StrE <$> list (pair atom exp) fs
  | "OptE", #[e] => .OptE <$> opt exp e
  | "ListE", #[es] => .ListE <$> list exp es
  | "ConsE", #[h, t] => do pure (.ConsE (← exp h) (← exp t))
  | "CatE", #[l, r] => do pure (.CatE (← exp l) (← exp r))
  | "MemE", #[e, s] => do pure (.MemE (← exp e) (← exp s))
  | "LenE", #[e] => .LenE <$> exp e
  | "DotE", #[e, a] => do pure (.DotE (← exp e) (← atom a))
  | "IdxE", #[b, i] => do pure (.IdxE (← exp b) (← exp i))
  | "SliceE", #[b, l, h] => do pure (.SliceE (← exp b) (← exp l) (← exp h))
  | "UpdE", #[b, p, f] => do pure (.UpdE (← exp b) (← path p) (← exp f))
  | "CallE", #[i, ts, as] => do pure (.CallE (← id i) (← list targ ts) (← list arg as))
  | "IterE", #[e, ie] => do pure (.IterE (← exp e) (← iterexp ie))
  | _, _ => fail "expected exp'" j

/-- Decode `exp`. -/
partial def exp : D exp := note_phrase exp' typ'

/-- Decode `path'`. -/
partial def path' : D path' := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "RootP", _ => pure .RootP
  | "IdxP", #[p, i] => do pure (.IdxP (← path p) (← exp i))
  | "SliceP", #[p, l, h] => do pure (.SliceP (← path p) (← exp l) (← exp h))
  | "DotP", #[p, a] => do pure (.DotP (← path p) (← atom a))
  | _, _ => fail "expected path'" j

/-- Decode `path`. -/
partial def path : D path := note_phrase path' typ'

/-- Decode `arg'`. -/
partial def arg' : D arg' := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "ExpA", #[e] => .ExpA <$> exp e
  | "DefA", #[i] => .DefA <$> id i
  | _, _ => fail "expected arg'" j

/-- Decode `arg`. -/
partial def arg : D arg := phrase arg'

end

/-- Decode `param'`. -/
partial def param' : D param' := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "ExpP", #[t] => .ExpP <$> typ t
  | "DefP", #[i, tps, ps, t] => do
    pure (.DefP (← id i) (← list id tps) (← list (phrase param') ps) (← typ t))
  | _, _ => fail "expected param'" j

/-- Decode `param`. -/
def param : D param := phrase param'

/-- Decode `tparam`. -/
def tparam : D tparam := phrase str

/-- Decode `iterprem`. -/
def iterprem : D iterprem := fun j => do
  let (i, vb, vd) ← triple iter (list var) (list var) j
  pure (.mk i vb vd)

/-- Decode `prem'`. -/
partial def prem' : D prem' := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "RulePr", #[i, n, ins] => do pure (.RulePr (← id i) (← mixfix exp n) (← inputs ins))
  | "IfPr", #[e] => .IfPr <$> exp e
  | "IfHoldPr", #[i, n] => do pure (.IfHoldPr (← id i) (← mixfix exp n))
  | "IfNotHoldPr", #[i, n] => do pure (.IfNotHoldPr (← id i) (← mixfix exp n))
  | "LetPr", #[l, r] => do pure (.LetPr (← exp l) (← exp r))
  | "IterPr", #[p, ip] => do pure (.IterPr (← phrase prem' p) (← iterprem ip))
  | "DebugPr", #[e] => .DebugPr <$> exp e
  | _, _ => fail "expected prem'" j

/-- Decode `prem`. -/
def prem : D prem := phrase prem'

/-- Decode `clause`. -/
def clause : D clause := phrase (triple (list arg) exp (list prem))

/-- Decode `rule`. -/
def rule : D rule := phrase (triple id (mixfix exp) (list prem))

/-- Decode `rulegroup`. -/
def rulegroup : D rulegroup := phrase (pair id (list rule))

/-- Decode `elsegroup`. -/
def elsegroup : D elsegroup := phrase (pair id rule)

/-- Decode `tablerow`. -/
def tablerow : D tablerow := phrase (pair (list arg) exp)

/-- Decode `def'`. -/
def def' : D def' := fun j => do
  let (c, a) ← variant j
  match c, a with
  | "ExternTypD", #[i, hs] => do pure (.ExternTypD (← id i) (← list hint hs))
  | "TypD", #[i, tps, dt, hs] => do
    pure (.TypD (← id i) (← list tparam tps) (← deftyp dt) (← list hint hs))
  | "VarD", #[i, t, hs] => do pure (.VarD (← id i) (← typ t) (← list hint hs))
  | "ExternRelD", #[i, n, ins, hs] => do
    pure (.ExternRelD (← id i) (← nottyp n) (← inputs ins) (← list hint hs))
  | "RelD", #[i, n, ins, rgs, eg, hs] => do
    pure (.RelD (← id i) (← nottyp n) (← inputs ins) (← list rulegroup rgs)
      (← opt elsegroup eg) (← list hint hs))
  | "ExternDecD", #[i, tps, ps, t, hs] => do
    pure (.ExternDecD (← id i) (← list tparam tps) (← list param ps) (← typ t) (← list hint hs))
  | "BuiltinDecD", #[i, tps, ps, t, hs] => do
    pure (.BuiltinDecD (← id i) (← list tparam tps) (← list param ps) (← typ t) (← list hint hs))
  | "TableDecD", #[i, ps, t, rows, hs] => do
    pure (.TableDecD (← id i) (← list param ps) (← typ t) (← list tablerow rows) (← list hint hs))
  | "FuncDecD", #[i, tps, ps, t, cs, ec, hs] => do
    pure (.FuncDecD (← id i) (← list tparam tps) (← list param ps) (← typ t) (← list clause cs)
      (← opt clause ec) (← list hint hs))
  | _, _ => fail "expected def'" j

/-- Decode `def`. -/
def «def» : D «def» := phrase def'

/-- Decode `spec`. -/
def spec : D spec := list «def»

end P4SpecTec.Lang.Il.Json
