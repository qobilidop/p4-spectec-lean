import P4SpecTec.Codegen.Types

/-!
AL expression, premise and definition traversal for subtype bridges and dependencies.
-/

namespace P4SpecTec.Codegen.Exp

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types

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

/-- The premises of a callable body, shared ones first. -/
def premsOfDef (d : Lang.Al.def) : List prem :=
  match d.it with
  | .RelD _ _ _ gs eg _ =>
    gs.flatMap (fun g => g.it.2.1.2.2 ++ g.it.2.2.flatMap (·.2.1)) ++
      (eg.toList.flatMap fun g => g.it.2.1.2.2 ++ g.it.2.2.2.1)
  | .FuncDecD _ _ _ _ cs ec _ => (cs ++ ec.toList).flatMap (·.it.2.2)
  | .TableDecD _ _ _ rs _ => rs.flatMap (·.it.2.2.2)
  | _ => []

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

/-- Global calls and function arguments, excluding lexically bound callbacks. -/
partial def callsOfExpBound (locals : List String) (e : exp) : List String :=
  let global (s : String) := if locals.contains s then [] else [s]
  (match e.it with
    | .CallE i _ args => global i.it ++ args.flatMap (fun a => match a.it with
        | .DefA d => global d.it
        | _ => [])
    | _ => []) ++ (pairsOfExp.children e).flatMap (callsOfExpBound locals)

/-- Global dependencies of an expression with no local callbacks. -/
def callsOfExp (e : exp) : List String := callsOfExpBound [] e

/-- Dependencies of a premise, respecting locally bound callable arguments. -/
partial def callsOfPremBound (locals : List String) (p : prem) : List String :=
  (match p.it with
    | .RulePr i _ _ | .IfHoldPr i _ | .IfNotHoldPr i _ => [i.it]
    | _ => []) ++ (expsOfPrem p).flatMap (callsOfExpBound locals) ++
    (match p.it with | .IterPr q _ => callsOfPremBound locals q | _ => [])

/-- Global dependencies of a premise with no local callbacks. -/
def callsOfPrem (p : prem) : List String := callsOfPremBound [] p

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
      let (args, out, prems) := c.it
      let locals := args.filterMap fun a => match a.it with
        | .DefA d => some d.it
        | _ => none
      callsOfExpBound locals out ++ prems.flatMap (callsOfPremBound locals)
    clauses.flatMap ofClause ++ (match ec with | some c => ofClause c | none => [])
  | .TableDecD _ _ _ rows _ =>
    rows.flatMap fun r =>
      let (_, args, out, prems) := r.it
      let locals := args.filterMap fun a => match a.it with
        | .DefA d => some d.it
        | _ => none
      callsOfExpBound locals out ++ prems.flatMap (callsOfPremBound locals)
  | _ => []

end P4SpecTec.Codegen.Exp
