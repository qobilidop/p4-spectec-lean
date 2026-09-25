import Lean.Data.Json.Basic
import P4SpecTec.Util.Source
import P4SpecTec.Lang.Xl.Num
import P4SpecTec.Lang.Xl.Bool
import P4SpecTec.Domain.Atom
import P4SpecTec.Domain.Mixfix

/-!
The IL (internal language) abstract syntax. Mirrors
`p4spec/lib/lang/il/ast.ml` of P4-SpecTec at the pinned commit: same type
names, constructor names, constructor order, field order and comments.
Where the OCaml defines `foo = foo' phrase` inside a recursive group, the
Lean spells the phrase out as `info foo' Unit region` in constructor
arguments and defines the abbreviation after the group: an abbreviation
cannot sit inside a `mutual` block, and the kernel's nested-inductive check
does not unfold one in a constructor argument.

Deviations forced by Lean are in the named list of `docs/design.md`
section 5.3; this file has four: EL hints are kept as raw JSON, the
polymorphic-variant unions (`unop`, `binop`, `cmpop`, `optyp`, `numop`) are
flattened into one inductive each, `Bigint.t` is `Nat` or `Int`, and
`iterexp`, `iterprem` and `typorigin'` are named inductives rather than
tuples.
-/

namespace P4SpecTec.Lang.Il

open P4SpecTec.Util.Source
open P4SpecTec.Lang.Xl
open P4SpecTec.Domain

/- Numbers -/

/-- Mirrors `num`. -/
abbrev num := Num.t

/- Texts -/

/-- Mirrors `text`. -/
abbrev text := String

/- Identifiers -/

/-- Mirrors `id'`. -/
abbrev id' := String

/-- Mirrors `id`. -/
abbrev id := phrase id'

/- Atoms -/

/-- Mirrors `atom'`. -/
abbrev atom' := Atom.t

/-- Mirrors `atom`. -/
abbrev atom := phrase atom'

/- Mixfix operators -/

/-- Mirrors `mixop`. -/
abbrev mixop := Mixfix.mixop

/- Iterators -/

/-- Mirrors `iter`. -/
inductive iter where
  /-- `?` -/
  | Opt
  /-- `*` -/
  | List
  deriving BEq, Repr, Inhabited

/- Hints -/

/-- Mirrors `hint = El.hint`. The EL expression language is not mirrored
(deviation): a hint is kept as the JSON upstream printed, since the compiler
reads no hint but the input hint, which the IL carries separately. -/
abbrev hint := Lean.Json

/- Input hints for relations -/

/-- Mirrors `Hints.Input.t` (`p4spec/lib/lang/hints/input.ml`): the
positions of a relation's inputs among its arguments. -/
abbrev Hints.Input.t := List Int

/- Operators -/

/-- Mirrors `numop`. -/
inductive numop where
  /-- `` `DecOp `` -/
  | DecOp
  /-- `` `HexOp `` -/
  | HexOp
  deriving BEq, Repr, Inhabited

/-- Mirrors `unop = [ Bool.unop | Num.unop ]`, flattened. -/
inductive unop where
  /-- `Bool.unop` -/
  | NotOp
  /-- `Num.unop` -/
  | PlusOp
  /-- `Num.unop` -/
  | MinusOp
  deriving BEq, Repr, Inhabited

/-- Mirrors `binop = [ Bool.binop | Num.binop ]`, flattened. -/
inductive binop where
  /-- `Bool.binop` -/
  | AndOp
  /-- `Bool.binop` -/
  | OrOp
  /-- `Bool.binop` -/
  | ImplOp
  /-- `Bool.binop` -/
  | EquivOp
  /-- `Num.binop` -/
  | AddOp
  /-- `Num.binop` -/
  | SubOp
  /-- `Num.binop` -/
  | MulOp
  /-- `Num.binop` -/
  | DivOp
  /-- `Num.binop` -/
  | ModOp
  /-- `Num.binop` -/
  | PowOp
  deriving BEq, Repr, Inhabited

/-- Mirrors `cmpop = [ Bool.cmpop | Num.cmpop ]`, flattened. -/
inductive cmpop where
  /-- `Bool.cmpop` -/
  | EqOp
  /-- `Bool.cmpop` -/
  | NeOp
  /-- `Num.cmpop` -/
  | LtOp
  /-- `Num.cmpop` -/
  | GtOp
  /-- `Num.cmpop` -/
  | LeOp
  /-- `Num.cmpop` -/
  | GeOp
  deriving BEq, Repr, Inhabited

/-- Mirrors `optyp = [ Bool.typ | Num.typ ]`, flattened. -/
inductive optyp where
  /-- `Bool.typ` -/
  | BoolT
  /-- `Num.typ` -/
  | NatT
  /-- `Num.typ` -/
  | IntT
  deriving BEq, Repr, Inhabited

/- Patterns -/

/-- Mirrors the list pattern of `pattern`'s `ListP`. -/
inductive listpattern where
  /-- `` `Cons `` -/
  | Cons
  /-- `` `Fixed of int `` -/
  | Fixed (n : Int)
  /-- `` `Nil `` -/
  | Nil
  deriving BEq, Repr, Inhabited

/-- Mirrors the option pattern of `pattern`'s `OptP`. -/
inductive optpattern where
  /-- `` `Some `` -/
  | Some
  /-- `` `None `` -/
  | None
  deriving BEq, Repr, Inhabited

/-- Mirrors `pattern`. -/
inductive pattern where
  /-- `CaseP of mixop` -/
  | CaseP (m : mixop)
  /-- `` ListP of [ `Cons | `Fixed of int | `Nil ] `` -/
  | ListP (p : listpattern)
  /-- `` OptP of [ `Some | `None ] `` -/
  | OptP (p : optpattern)
  deriving Repr, Inhabited

/- Values: the note -/

/-- Mirrors `vid`. -/
abbrev vid := Int

mutual

/- Types -/

/-- Mirrors `typ'`. -/
inductive typ' where
  /-- `bool` -/
  | BoolT
  /-- numtyp -/
  | NumT (t : Num.typ)
  /-- `text` -/
  | TextT
  /-- id (`<` list(targ, `,`) `>`)? -/
  | VarT (id : phrase id') (targs : List (info typ' Unit region))
  /-- `(` list(typ, `,`) `)` -/
  | TupleT (typs : List (info typ' Unit region))
  /-- typ iter -/
  | IterT (typ : info typ' Unit region) (iter : iter)
  /-- `<` list(tparam, `,`) `>` `(` list(typ, `,`) `)` `:` typ -/
  | FuncT (tparams : List (phrase id')) (typs : List (info typ' Unit region))
      (typ : info typ' Unit region)

/- Defined types -/

/-- Mirrors `deftyp'`. -/
inductive deftyp' where
  /-- `PlainT of typ` -/
  | PlainT (typ : info typ' Unit region)
  /-- `StructT of typfield list` -/
  | StructT (fields : List (atom × info typ' Unit region))
  /-- `VariantT of typcase list` -/
  | VariantT (cases : List typcase)

/-- Mirrors `typorigin' = id * targ list`. A named type rather than a pair,
because the kernel rejects a pair holding a list of a type being declared. -/
inductive typorigin' where
  /-- The originating type and its type arguments. -/
  | mk (id : phrase id') (targs : List (info typ' Unit region))

/-- Mirrors `typcase = nottyp * typorigin * hint list`. -/
inductive typcase where
  /-- The case, its origin and its hints. -/
  | mk (nottyp : info (Mixfix.t (info typ' Unit region)) Unit region)
      (typorigin : info typorigin' Unit region) (hints : List hint)

/- Values -/

/-- Mirrors `vnote`. -/
inductive vnote where
  /-- The unique id, the type and the structural hash. -/
  | mk (vid : vid) (typ : typ') (vhash : Int)

/-- Mirrors `value'`. -/
inductive value' where
  /-- `BoolV of bool` -/
  | BoolV (b : Bool)
  /-- `NumV of Num.t` -/
  | NumV (n : Num.t)
  /-- `TextV of string` -/
  | TextV (s : String)
  /-- `StructV of valuefield list` -/
  | StructV (fields : List (atom × info value' vnote region))
  /-- `CaseV of valuecase` -/
  | CaseV (c : Mixfix.t (info value' vnote region))
  /-- `TupleV of value list` -/
  | TupleV (vs : List (info value' vnote region))
  /-- `OptV of value option` -/
  | OptV (v : Option (info value' vnote region))
  /-- `ListV of value list` -/
  | ListV (vs : List (info value' vnote region))
  /-- `FuncV of id` -/
  | FuncV (id : phrase id')
  /-- `ExternV of Yojson.Safe.t` -/
  | ExternV (json : Lean.Json)

/- Subtype checks -/

/-- Mirrors `subcheck`. -/
inductive subcheck where
  /-- `SkipSC` -/
  | SkipSC
  /-- `MixopSC of mixop list` -/
  | MixopSC (mixops : List mixop)
  /-- `TupleSC of subcheck list` -/
  | TupleSC (scs : List subcheck)
  /-- `IterSC of iter * subcheck` -/
  | IterSC (iter : iter) (sc : subcheck)
  /-- `RecurseSC of typ` -/
  | RecurseSC (typ : info typ' Unit region)

/- Expressions -/

/-- Mirrors `exp'`. -/
inductive exp' where
  /-- bool -/
  | BoolE (b : Bool)
  /-- num -/
  | NumE (n : num)
  /-- text -/
  | TextE (s : text)
  /-- varid -/
  | VarE (id : phrase id')
  /-- unop exp -/
  | UnE (op : unop) (optyp : optyp) (e : info exp' typ' region)
  /-- exp binop exp -/
  | BinE (op : binop) (optyp : optyp) (l : info exp' typ' region) (r : info exp' typ' region)
  /-- exp cmpop exp -/
  | CmpE (op : cmpop) (optyp : optyp) (l : info exp' typ' region) (r : info exp' typ' region)
  /-- exp as typ -/
  | UpCastE (typ : info typ' Unit region) (e : info exp' typ' region)
  /-- exp as typ -/
  | DownCastE (typ : info typ' Unit region) (e : info exp' typ' region)
  /-- exp `<:` typ -/
  | SubE (e : info exp' typ' region) (typ : info typ' Unit region) (sc : subcheck)
  /-- exp `matches` pattern -/
  | MatchE (e : info exp' typ' region) (p : pattern)
  /-- `(` exp* `)` -/
  | TupleE (es : List (info exp' typ' region))
  /-- notexp -/
  | CaseE (notexp : Mixfix.t (info exp' typ' region))
  /-- { expfield* } -/
  | StrE (fields : List (atom × info exp' typ' region))
  /-- exp? -/
  | OptE (e : Option (info exp' typ' region))
  /-- `[` exp* `]` -/
  | ListE (es : List (info exp' typ' region))
  /-- exp `::` exp -/
  | ConsE (h : info exp' typ' region) (t : info exp' typ' region)
  /-- exp `++` exp -/
  | CatE (l : info exp' typ' region) (r : info exp' typ' region)
  /-- exp `<-` exp -/
  | MemE (e : info exp' typ' region) (s : info exp' typ' region)
  /-- `|` exp `|` -/
  | LenE (e : info exp' typ' region)
  /-- exp.atom -/
  | DotE (e : info exp' typ' region) (atom : atom)
  /-- exp `[` exp `]` -/
  | IdxE (b : info exp' typ' region) (i : info exp' typ' region)
  /-- exp `[` exp `:` exp `]` -/
  | SliceE (b : info exp' typ' region) (l : info exp' typ' region) (h : info exp' typ' region)
  /-- exp `[` path `=` exp `]` -/
  | UpdE (b : info exp' typ' region) (p : info path' typ' region) (f : info exp' typ' region)
  /-- $id`<` targ* `>``(` arg* `)` -/
  | CallE (id : phrase id') (targs : List (info typ' Unit region))
      (args : List (info arg' Unit region))
  /-- exp iterexp -/
  | IterE (e : info exp' typ' region) (iterexp : iterexp)

/-- Mirrors `var = id * typ * iter list`. -/
inductive var where
  /-- The variable, its type and its iteration dimensions. -/
  | mk (id : phrase id') (typ : info typ' Unit region) (iters : List iter)

/-- Mirrors `iterexp = iter * var list`. A named type rather than a pair,
because the kernel rejects a pair holding a list of a type being declared. -/
inductive iterexp where
  /-- The iterator and the variables it ranges over. -/
  | mk (iter : iter) (vars : List var)

/-- Mirrors `iterprem = iter * var list * var list`, named for the same
reason as `iterexp`. -/
inductive iterprem where
  /-- The iterator, the bound variables and the binding variables. -/
  | mk (iter : iter) (vars_bound : List var) (vars_bind : List var)

/- Path -/

/-- Mirrors `path'`. -/
inductive path' where
  /-- (empty) -/
  | RootP
  /-- path `[` exp `]` -/
  | IdxP (p : info path' typ' region) (i : info exp' typ' region)
  /-- path `[` exp `:` exp `]` -/
  | SliceP (p : info path' typ' region) (l : info exp' typ' region) (h : info exp' typ' region)
  /-- path `.` atom -/
  | DotP (p : info path' typ' region) (atom : atom)

/- Parameters -/

/-- Mirrors `param'`. -/
inductive param' where
  /-- typ -/
  | ExpP (typ : info typ' Unit region)
  /-- `def` `$`id ` (`<` list(tparam, `,`) `>`)? (`(` list(param, `,`) `)`)? `:` typ -/
  | DefP (id : phrase id') (tparams : List (phrase id')) (params : List (info param' Unit region))
      (typ : info typ' Unit region)

/- Arguments -/

/-- Mirrors `arg'`. -/
inductive arg' where
  /-- exp -/
  | ExpA (e : info exp' typ' region)
  /-- `$`id -/
  | DefA (id : phrase id')

/- Premises -/

/-- Mirrors `prem'`. -/
inductive prem' where
  /-- id `:` notexp -/
  | RulePr (id : phrase id') (notexp : Mixfix.t (info exp' typ' region)) (inputs : Hints.Input.t)
  /-- `if` exp -/
  | IfPr (e : info exp' typ' region)
  /-- `if` id `:` notexp `holds` -/
  | IfHoldPr (id : phrase id') (notexp : Mixfix.t (info exp' typ' region))
  /-- `if` id `:` notexp `does not hold` -/
  | IfNotHoldPr (id : phrase id') (notexp : Mixfix.t (info exp' typ' region))
  /-- `let` exp `=` exp -/
  | LetPr (l : info exp' typ' region) (r : info exp' typ' region)
  /-- prem iterprem -/
  | IterPr (p : info prem' Unit region) (iterprem : iterprem)
  /-- `debug` exp -/
  | DebugPr (e : info exp' typ' region)

end

/- Types -/

/-- Mirrors `typ`. -/
abbrev typ := phrase typ'

/-- Mirrors `nottyp'`. -/
abbrev nottyp' := Mixfix.t typ

/-- Mirrors `nottyp`. -/
abbrev nottyp := phrase nottyp'

/-- Mirrors `deftyp`. -/
abbrev deftyp := phrase deftyp'

/-- Mirrors `typfield`. -/
abbrev typfield := atom × typ

/-- Mirrors `typorigin`. -/
abbrev typorigin := phrase typorigin'

/- Values -/

/-- Mirrors `value`. -/
abbrev value := note_phrase value' vnote

/-- Mirrors `valuefield`. -/
abbrev valuefield := atom × value

/-- Mirrors `valuecase`. -/
abbrev valuecase := Mixfix.t value

/- Expressions -/

/-- Mirrors `exp`. -/
abbrev exp := note_phrase exp' typ'

/-- Mirrors `notexp`. -/
abbrev notexp := Mixfix.t exp

/- Path -/

/-- Mirrors `path`. -/
abbrev path := note_phrase path' typ'

/- Parameters -/

/-- Mirrors `param`. -/
abbrev param := phrase param'

/- Type parameters -/

/-- Mirrors `tparam'`. -/
abbrev tparam' := id'

/-- Mirrors `tparam`. -/
abbrev tparam := phrase tparam'

/- Arguments -/

/-- Mirrors `arg`. -/
abbrev arg := phrase arg'

/- Type arguments -/

/-- Mirrors `targ'`. -/
abbrev targ' := typ'

/-- Mirrors `targ`. -/
abbrev targ := phrase targ'

/- Premises -/

/-- Mirrors `prem`. -/
abbrev prem := phrase prem'

/- Rules -/

/-- Mirrors `rule'`. -/
abbrev rule' := id × notexp × List prem

/-- Mirrors `rule`. -/
abbrev rule := phrase rule'

/-- Mirrors `rulegroup'`. -/
abbrev rulegroup' := id × List rule

/-- Mirrors `rulegroup`. -/
abbrev rulegroup := phrase rulegroup'

/-- Mirrors `elsegroup'`. -/
abbrev elsegroup' := id × rule

/-- Mirrors `elsegroup`. -/
abbrev elsegroup := phrase elsegroup'

/- Clauses -/

/-- Mirrors `clause'`. -/
abbrev clause' := List arg × exp × List prem

/-- Mirrors `clause`. -/
abbrev clause := phrase clause'

/-- Mirrors `elseclause`. -/
abbrev elseclause := clause

/-- Mirrors `elseclause'`. -/
abbrev elseclause' := clause'

/- Table rows -/

/-- Mirrors `tablerow'`. -/
abbrev tablerow' := List arg × exp

/-- Mirrors `tablerow`. -/
abbrev tablerow := phrase tablerow'

/- Definitions -/

/-- Mirrors `def'`. -/
inductive def' where
  /-- `extern` `syntax` id hint* -/
  | ExternTypD (id : id) (hints : List hint)
  /-- `syntax` id `<` list(tparam, `,`) `>` hint* `=` deftyp -/
  | TypD (id : id) (tparams : List tparam) (deftyp : deftyp) (hints : List hint)
  /-- `var` id `:` typ hint* -/
  | VarD (id : id) (typ : typ) (hints : List hint)
  /-- `extern` `relation` id `:` nottyp `hint(input` `%`int* `)` hint* -/
  | ExternRelD (id : id) (nottyp : nottyp) (inputs : Hints.Input.t) (hints : List hint)
  /-- `relation` id `:` nottyp `hint(input` `%`int* `)` rulegroup* hint* -/
  | RelD (id : id) (nottyp : nottyp) (inputs : Hints.Input.t) (rulegroups : List rulegroup)
      (elsegroup : Option elsegroup) (hints : List hint)
  /-- `extern` `dec` id `<` list(tparam, `,`) `>` list(param, `,`) `:` typ hint* -/
  | ExternDecD (id : id) (tparams : List tparam) (params : List param) (typ : typ)
      (hints : List hint)
  /-- `builtin` `dec` id `<` list(tparam, `,`) `>` list(param, `,`) `:` typ hint* -/
  | BuiltinDecD (id : id) (tparams : List tparam) (params : List param) (typ : typ)
      (hints : List hint)
  /-- `table` `dec` id list(param, `,`) `:` typ hint* -/
  | TableDecD (id : id) (params : List param) (typ : typ) (rows : List tablerow)
      (hints : List hint)
  /-- `dec` id `<` list(tparam, `,`) `>` list(param, `,`) `:` typ clause* hint* -/
  | FuncDecD (id : id) (tparams : List tparam) (params : List param) (typ : typ)
      (clauses : List clause) (elseclause : Option elseclause) (hints : List hint)

/-- Mirrors `def`. -/
abbrev «def» := phrase def'

/- Spec -/

/-- Mirrors `spec`. -/
abbrev spec := List «def»

/-! Accessors named as upstream's `Util.Source` projections. -/

/-- The `vid` of a value note. -/
def vnote.vid : Lang.Il.vnote → Lang.Il.vid | .mk v _ _ => v

/-- The `typ` of a value note. -/
def vnote.typ : Lang.Il.vnote → Lang.Il.typ' | .mk _ t _ => t

/-- The `vhash` of a value note. -/
def vnote.vhash : Lang.Il.vnote → Int | .mk _ _ h => h

/-- The `nottyp` of a type case. -/
def typcase.nottyp : Lang.Il.typcase → Lang.Il.nottyp | .mk n _ _ => n

/-- The `typorigin` of a type case. -/
def typcase.typorigin : Lang.Il.typcase → Lang.Il.typorigin | .mk _ o _ => o

/-- The `id` of a type origin. -/
def typorigin'.id : Lang.Il.typorigin' → Lang.Il.id | .mk i _ => i

/-- The `targs` of a type origin. -/
def typorigin'.targs : Lang.Il.typorigin' → List Lang.Il.targ | .mk _ ts => ts

/-- The `id` of a variable. -/
def var.id : Lang.Il.var → Lang.Il.id | .mk i _ _ => i

/-- The `typ` of a variable. -/
def var.typ : Lang.Il.var → Lang.Il.typ | .mk _ t _ => t

/-- The `iters` of a variable. -/
def var.iters : Lang.Il.var → List Lang.Il.iter | .mk _ _ is => is

/-- The `iter` of an iterated expression. -/
def iterexp.iter : Lang.Il.iterexp → Lang.Il.iter | .mk i _ => i

/-- The `vars` of an iterated expression. -/
def iterexp.vars : Lang.Il.iterexp → List Lang.Il.var | .mk _ vs => vs

/-- The `iter` of an iterated premise. -/
def iterprem.iter : Lang.Il.iterprem → Lang.Il.iter | .mk i _ _ => i

/-- The bound variables of an iterated premise. -/
def iterprem.vars_bound : Lang.Il.iterprem → List Lang.Il.var | .mk _ vs _ => vs

/-- The binding variables of an iterated premise. -/
def iterprem.vars_bind : Lang.Il.iterprem → List Lang.Il.var | .mk _ _ vs => vs

end P4SpecTec.Lang.Il
