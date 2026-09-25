import P4SpecTec.Codegen.Types

/-!
Reification: an AL definition as Lean data, `⌜d⌝` (design section 5,
rung 3), printed through the smart constructors of `Refine/Quote.lean`
with regions erased and hints dropped. Every generated definition `d` of
a relation or function gets `d.al : Lang.Al.def` beside it, the term the
refinement theorems run the interpreter on.
-/

namespace P4SpecTec.Codegen.Reify

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types

/-- A string literal term. -/
def str (s : String) : Term := .strLit s

/-- A list term. -/
def lst (ts : List Term) : Term := .list ts

/-- An optional term. -/
def opt : Option Term → Term
  | some t => .call "some" [t]
  | none => .atom "none"

/-- A natural literal. -/
def nat (n : Nat) : Term := .natLit n

/-- An integer literal. -/
def int (i : Int) : Term := .intLit i

/-- A `Num.t`. -/
def num : Num.t → Term
  | .Nat n => .call ".Nat" [nat n]
  | .Int i => .call ".Int" [int i]

/-- An `iter`. -/
def iter : Lang.Il.iter → Term
  | .Opt => .atom ".Opt"
  | .List => .atom ".List"

/-- An atom, through `Q.a`. -/
def atom (x : Lang.Il.atom) : Term := .call "Q.a" [atomTerm x.it]

/-- A mixfix filled with argument terms, atoms through `Q.a`. -/
partial def mixfix {α : Type} (m : Mixfix.t α) (arg : α → Term) : Term :=
  match m with
  | .Arg x => .call ".Arg" [arg x]
  | .Atom x => .call ".Atom" [atom x]
  | .Brack l m r => .call ".Brack" [atom l, mixfix m arg, atom r]
  | .Infix l x r => .call ".Infix" [mixfix l arg, atom x, mixfix r arg]
  | .Seq ms => .call ".Seq" [lst (ms.map fun m => mixfix m arg)]

/-- A mixop (`Mixfix.t Unit`). -/
def mixop (m : Mixfix.mixop) : Term := mixfix m fun _ => .atom "()"

mutual

/-- A `typ'`. -/
partial def typ' : Lang.Il.typ' → Term
  | .BoolT => .atom ".BoolT"
  | .NumT .NatT => .atom "(.NumT .NatT)"
  | .NumT .IntT => .atom "(.NumT .IntT)"
  | .TextT => .atom ".TextT"
  | .VarT i targs => .call "Q.varT" [str i.it, lst (targs.map typ)]
  | .TupleT ts => .call ".TupleT" [lst (ts.map typ)]
  | .IterT t it => .call ".IterT" [typ t, iter it]
  | .FuncT tparams ts t => .call ".FuncT" [lst (tparams.map fun p => .call "Q.i" [str p.it]),
      lst (ts.map typ), typ t]

/-- A `typ`. -/
partial def typ (t : Lang.Il.typ) : Term := .call "Q.t" [typ' t.it]

end

/-- A `nottyp`. -/
def nottyp (n : Lang.Il.nottyp) : Term := .call "Q.nt" [mixfix n.it typ]

/-- A `deftyp`. -/
def deftyp (d : Lang.Il.deftyp) : Term :=
  .call "Q.dt" [match d.it with
    | .PlainT t => .call ".PlainT" [typ t]
    | .StructT fields => .call ".StructT" [lst (fields.map fun (a, t) => .tuple [atom a, typ t])]
    | .VariantT cases => .call ".VariantT" [lst (cases.map fun c =>
        let (o, targs) := match c.typorigin.it with | .mk o targs => (o, targs)
        .call "Q.tc" [mixfix c.nottyp.it typ, str o.it, lst (targs.map typ)])]]

/-- A `pattern`. -/
def pattern : Lang.Il.pattern → Term
  | .CaseP m => .call ".CaseP" [mixop m]
  | .ListP .Cons => .atom "(.ListP .Cons)"
  | .ListP (.Fixed n) => .call ".ListP" [.call ".Fixed" [int n]]
  | .ListP .Nil => .atom "(.ListP .Nil)"
  | .OptP .Some => .atom "(.OptP .Some)"
  | .OptP .None => .atom "(.OptP .None)"

/-- A `subcheck`. -/
partial def subcheck : Lang.Il.subcheck → Term
  | .SkipSC => .atom ".SkipSC"
  | .MixopSC ms => .call ".MixopSC" [lst (ms.map mixop)]
  | .TupleSC scs => .call ".TupleSC" [lst (scs.map subcheck)]
  | .IterSC it sc => .call ".IterSC" [iter it, subcheck sc]
  | .RecurseSC t => .call ".RecurseSC" [typ t]

/-- A `var`. -/
def var (w : Lang.Il.var) : Term :=
  .call "Q.v" [str w.id.it, typ' w.typ.it, lst (w.iters.map iter)]

/-- An operator constructor, dotted: the last component of its `repr`. -/
def op {α : Type} [Repr α] (x : α) : Term :=
  .atom ("." ++ ((toString (repr x)).splitOn ".").getLast!)

mutual

/-- An `exp`, with its type note. -/
partial def exp (e : Lang.Il.exp) : Term := .call "Q.e" [exp' e.it, typ' e.note]

/-- An `exp'`. -/
partial def exp' : Lang.Il.exp' → Term
  | .BoolE b => .call ".BoolE" [.atom (toString b)]
  | .NumE n => .call ".NumE" [num n]
  | .TextE s => .call ".TextE" [str s]
  | .VarE i => .call ".VarE" [.call "Q.i" [str i.it]]
  | .UnE o ot a => .call ".UnE" [op o, op ot, exp a]
  | .BinE o ot a b => .call ".BinE" [op o, op ot, exp a, exp b]
  | .CmpE o ot a b => .call ".CmpE" [op o, op ot, exp a, exp b]
  | .UpCastE t a => .call ".UpCastE" [typ t, exp a]
  | .DownCastE t a => .call ".DownCastE" [typ t, exp a]
  | .SubE a t sc => .call ".SubE" [exp a, typ t, subcheck sc]
  | .MatchE a p => .call ".MatchE" [exp a, pattern p]
  | .TupleE es => .call ".TupleE" [lst (es.map exp)]
  | .CaseE n => .call ".CaseE" [mixfix n exp]
  | .StrE fields => .call ".StrE" [lst (fields.map fun (a, f) => .tuple [atom a, exp f])]
  | .OptE a => .call ".OptE" [opt (a.map exp)]
  | .ListE es => .call ".ListE" [lst (es.map exp)]
  | .ConsE h t => .call ".ConsE" [exp h, exp t]
  | .CatE a b => .call ".CatE" [exp a, exp b]
  | .MemE a b => .call ".MemE" [exp a, exp b]
  | .LenE a => .call ".LenE" [exp a]
  | .DotE a x => .call ".DotE" [exp a, atom x]
  | .IdxE a b => .call ".IdxE" [exp a, exp b]
  | .SliceE a b c => .call ".SliceE" [exp a, exp b, exp c]
  | .UpdE a p f => .call ".UpdE" [exp a, path p, exp f]
  | .CallE i targs args => .call ".CallE" [.call "Q.i" [str i.it], lst (targs.map typ),
      lst (args.map arg)]
  | .IterE a ie => .call ".IterE" [exp a, iterexp ie]

/-- An `iterexp`. -/
partial def iterexp : Lang.Il.iterexp → Term
  | .mk it vars => .call ".mk" [iter it, lst (vars.map var)]

/-- A `path`. -/
partial def path (p : Lang.Il.path) : Term := .call "Q.pa" [path' p.it, typ' p.note]

/-- A `path'`. -/
partial def path' : Lang.Il.path' → Term
  | .RootP => .atom ".RootP"
  | .IdxP p a => .call ".IdxP" [path p, exp a]
  | .SliceP p a b => .call ".SliceP" [path p, exp a, exp b]
  | .DotP p x => .call ".DotP" [path p, atom x]

/-- An `arg`. -/
partial def arg (a : Lang.Il.arg) : Term :=
  .call "Q.ar" [match a.it with
    | .ExpA e => .call ".ExpA" [exp e]
    | .DefA i => .call ".DefA" [.call "Q.i" [str i.it]]]

end

mutual

/-- A `prem`. -/
partial def prem (p : Lang.Il.prem) : Term := .call "Q.pr" [prem' p.it]

/-- A `prem'`. -/
partial def prem' : Lang.Il.prem' → Term
  | .RulePr i n inputs => .call ".RulePr" [.call "Q.i" [str i.it], mixfix n exp,
      lst (inputs.map int)]
  | .IfPr e => .call ".IfPr" [exp e]
  | .IfHoldPr i n => .call ".IfHoldPr" [.call "Q.i" [str i.it], mixfix n exp]
  | .IfNotHoldPr i n => .call ".IfNotHoldPr" [.call "Q.i" [str i.it], mixfix n exp]
  | .LetPr l r => .call ".LetPr" [exp l, exp r]
  | .IterPr q ip => .call ".IterPr" [prem q, iterprem ip]
  | .DebugPr e => .call ".DebugPr" [exp e]

/-- An `iterprem`. -/
partial def iterprem : Lang.Il.iterprem → Term
  | .mk it bound bind => .call ".mk" [iter it, lst (bound.map var), lst (bind.map var)]

end

/-- A `param`. -/
partial def param (p : Lang.Il.param) : Term :=
  .call "Q.pm" [match p.it with
    | .ExpP t => .call ".ExpP" [typ t]
    | .DefP i tparams params t => .call ".DefP" [.call "Q.i" [str i.it],
        lst (tparams.map fun p => .call "Q.i" [str p.it]), lst (params.map param), typ t]]

/-- A `rulematch`. -/
def rulematch (m : Lang.Al.rulematch) : Term :=
  let (sig, ins, prems) := m
  .tuple [lst (sig.map exp), lst (ins.map exp), lst (prems.map prem)]

/-- A `rulepath`. -/
def rulepath (p : Lang.Al.rulepath) : Term :=
  let (pid, prems, outs) := p
  .call "Q.rp" [str pid.it, lst (prems.map prem), lst (outs.map exp)]

/-- A `rulegroup`. -/
def rulegroup (g : Lang.Al.rulegroup) : Term :=
  let (gid, m, paths) := g.it
  .call "Q.rg" [str gid.it, rulematch m, lst (paths.map rulepath)]

/-- An `elsegroup`. -/
def elsegroup (g : Lang.Al.elsegroup) : Term :=
  let (gid, m, path) := g.it
  .call "Q.eg" [str gid.it, rulematch m, rulepath path]

/-- A `clause`. -/
def clause (c : Lang.Il.clause) : Term :=
  let (args, out, prems) := c.it
  .call "Q.cl" [lst (args.map arg), exp out, lst (prems.map prem)]

/-- A `tablerow`. -/
def tablerow (r : Lang.Al.tablerow) : Term :=
  let (pats, args, out, prems) := r.it
  .call "Q.tr" [lst (pats.map exp), lst (args.map arg), exp out, lst (prems.map prem)]

/-- A definition, hints dropped. -/
def def' (d : Lang.Al.def) : Term :=
  .call "Q.d" [match d.it with
    | .ExternTypD i _ => .call ".ExternTypD" [.call "Q.i" [str i.it], lst []]
    | .TypD i tparams dt _ => .call ".TypD" [.call "Q.i" [str i.it],
        lst (tparams.map fun p => .call "Q.i" [str p.it]), deftyp dt, lst []]
    | .VarD i t _ => .call ".VarD" [.call "Q.i" [str i.it], typ t, lst []]
    | .ExternRelD i n inputs _ => .call ".ExternRelD" [.call "Q.i" [str i.it], nottyp n,
        lst (inputs.map int), lst []]
    | .RelD i n inputs groups eg _ => .call ".RelD" [.call "Q.i" [str i.it], nottyp n,
        lst (inputs.map int), lst (groups.map rulegroup), opt (eg.map elsegroup), lst []]
    | .ExternDecD i tparams params t _ => .call ".ExternDecD" [.call "Q.i" [str i.it],
        lst (tparams.map fun p => .call "Q.i" [str p.it]), lst (params.map param), typ t, lst []]
    | .BuiltinDecD i tparams params t _ => .call ".BuiltinDecD" [.call "Q.i" [str i.it],
        lst (tparams.map fun p => .call "Q.i" [str p.it]), lst (params.map param), typ t, lst []]
    | .TableDecD i params t rows _ => .call ".TableDecD" [.call "Q.i" [str i.it],
        lst (params.map param), typ t, lst (rows.map tablerow), lst []]
    | .FuncDecD i tparams params t clauses ec _ => .call ".FuncDecD" [.call "Q.i" [str i.it],
        lst (tparams.map fun p => .call "Q.i" [str p.it]), lst (params.map param), typ t,
        lst (clauses.map clause), opt (ec.map clause), lst []]]

/-- The quoted definition `name.al`. -/
def quoted (name : String) (d : Lang.Al.def) : Format :=
  Term.defn (Format.text s!"def {name}.al : Lang.Al.def") (def' d).fmt

end P4SpecTec.Codegen.Reify
