import P4SpecTec.Codegen.Exp
import P4SpecTec.Interface.P4.Unparse

/-!
Not a mirror: validate that generated values preserve hint-driven printing
despite erasing runtime type-note provenance. Policies stay keyed by their
type family and constructor. Inherited cases and subtype bridges may change
the named family only when both names select the same optional policy.
-/

namespace P4SpecTec.Codegen.PrintHints

open Std (Format)
open P4SpecTec.Util.Source P4SpecTec.Domain P4SpecTec.Lang.Il
open P4SpecTec.Lang.Hints

/-- Compare optional policies without treating an absent hint as an explicit one. -/
def policyEq : Option Alter.t → Option Alter.t → Bool
  | none, none => true
  | some a, some b => Alter.policyEq a b
  | _, _ => false

/-- Whether an exported hint has the `print` identifier. The strict hint
decoder validates the record and expression before this invariant runs. -/
def isPrintHint (h : hint) : Bool :=
  match h.getObjVal? "it" >>= (·.getObjVal? "hintid") >>= (·.getObjVal? "it") with
  | .ok (.str "print") => true
  | _ => false

/-- Hints attached to a definition itself, rather than a variant case. -/
def definitionHints (d : Lang.Al.def) : List hint :=
  match d.it with
  | .ExternTypD _ hs | .TypD _ _ _ hs | .VarD _ _ hs => hs
  | .ExternRelD _ _ _ hs | .RelD _ _ _ _ _ hs => hs
  | .ExternDecD _ _ _ _ hs | .BuiltinDecD _ _ _ _ hs => hs
  | .TableDecD _ _ _ _ hs | .FuncDecD _ _ _ _ _ _ hs => hs

/-- Reject a policy change across a named case's origin or a subtype bridge. -/
def checkPolicy (henv : P4.Unparse.HEnv) (source target : String)
    (m : Mixfix.mixop) (location : String) : Except String Unit := do
  unless policyEq (P4.Unparse.find_hint henv source m) (P4.Unparse.find_hint henv target m) do
    throw s!"print policy mismatch: {source} -> {target}, constructor \
      {Mixfix.to_string m} ({location})"

/-- Constructors must carry the actual variant family as their source note.
An alias or anonymous note would lose the runtime hint lookup key when encoded. -/
partial def validateExp (env : Env) (e : exp) : Except String Unit := do
  if let .CaseE n := e.it then
    let location := string_of_region e.at
    let m := Mixfix.to_mixop n
    let .VarT i ts := e.note
      | throw s!"print policy constructor note: {Mixfix.to_string m} ({location}): \
          expected a named variant"
    let some cases := env.variantCases i.it (ts.map (·.it))
      | throw s!"print policy constructor note: {i.it}, constructor \
          {Mixfix.to_string m} ({location}): note is not a defined variant"
    unless cases.any (fun c => Mixfix.eq_mixop c.nottyp.it m) do
      throw s!"print policy constructor note: {i.it}, constructor \
        {Mixfix.to_string m} ({location}): variant lacks constructor"
  for child in Exp.pairsOfExp.children e do validateExp env child

/-- Check every raw variant-case origin and every shared bridge case.
Unrelated families may assign different policies to the same constructor.
With no policies, provenance cannot affect printing and need not be restricted. -/
def validate (env : Env) (spec : Lang.Al.spec) (henv : P4.Unparse.HEnv) :
    Except String Unit := do
  for d in spec do
    if (definitionHints d).any isPrintHint then
      throw s!"definition-level print hint is unsupported: {d.it.id.it} \
        ({string_of_region d.at})"
  if henv.isEmpty then return ()
  for d in spec do
    for e in Exp.expsOfDef d do validateExp env e
    if let .TypD owner _ dt _ := d.it then
      if let .VariantT cases := dt.it then
        for c in cases do
          let origin := c.typorigin.it.id.it
          let m := Mixfix.to_mixop c.nottyp.it
          let location := string_of_region d.at
          let some originCases := env.variantCases origin (c.typorigin.it.targs.map (·.it))
            | throw s!"print policy origin: {origin} -> {owner.it}, constructor \
                {Mixfix.to_string m} ({location}): origin is not a defined variant"
          unless originCases.any (fun oc => Mixfix.eq_mixop oc.nottyp.it m) do
            throw s!"print policy origin: {origin} -> {owner.it}, constructor \
              {Mixfix.to_string m} ({location}): origin lacks constructor"
          checkPolicy henv origin owner.it m location
  for (s, t) in Exp.pairsOfSpec env spec do
    let sCases ← Types.bridgeCases env s
    let tCases ← Types.bridgeCases env t
    let source := Types.typeHead s
    let target := Types.typeHead t
    let location := (env.types.get? source).map (·.file) |>.getD "<unknown source>"
    for c in sCases do
      let m := Mixfix.to_mixop c.nottyp.it
      if tCases.any (fun tc => Mixfix.eq_mixop tc.nottyp.it m) then
        checkPolicy henv source target m location

/-- Quote a supported alteration policy as literal Lean data, erasing regions. -/
partial def hintTerm : Alter.t → Except String Term
  | .TextH text => pure (.call ".TextH" [.strLit text])
  | .AtomH a => pure (.call ".AtomH" [atomPhrase a.it])
  | .SeqH hs => do pure (.call ".SeqH" [.list (← hs.mapM hintTerm)])
  | .BrackH l h r => do
    pure (.call ".BrackH" [atomPhrase l.it, ← hintTerm h, atomPhrase r.it])
  | .HoleH h =>
    let hole := match h.it with
      | .Next => Term.atom ".Next"
      | .Num n => Term.call ".Num" [.intLit n]
    pure (.call ".HoleH" [.call "P4SpecTec.Util.Source.mkPhrase" [hole]])
  | .FuseH l r => do pure (.call ".FuseH" [← hintTerm l, ← hintTerm r])
  | .OtherH _ => .error "cannot quote unsupported print alteration OtherH"
where
  /-- Quote an atom phrase without carrying source regions into generated code. -/
  atomPhrase (a : Atom.t) : Term :=
    .call "P4SpecTec.Util.Source.mkPhrase" [Types.atomTerm a]

/-- Emit the builtin's policy table as ordinary literal data, with no parsing
or opaque evaluation in generated code. -/
def tableDecl (henv : P4.Unparse.HEnv) : Except String Format := do
  let entries ← henv.mapM fun (tid, mixop, policy) => do
    match Alter.validate policy (Mixfix.arity mixop) with
    | .error _ => throw s!"invalid print policy for {tid}, constructor {Mixfix.to_string mixop}"
    | .ok () => pure ()
    pure (Term.tuple [.strLit tid, Types.mixopTerm mixop, ← hintTerm policy])
  pure (Term.defn (Format.text "def «$print_».hints : P4SpecTec.P4.Unparse.HEnv")
    (Term.list entries).fmt)

end P4SpecTec.Codegen.PrintHints
