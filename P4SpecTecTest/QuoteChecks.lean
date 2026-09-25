import P4SpecTecTest.Quote
import P4SpecTec.Codegen.Emit

/-! Sensitivity tests for the independent quotation check and namespace regression. -/

namespace P4SpecTecTest.QuoteChecks

open P4SpecTec P4SpecTec.Util.Source P4SpecTec.Lang.Il
open P4SpecTecTest.Quote

def located {α : Type} (x : α) : phrase α :=
  mkPhrase x { left := ⟨"source.watsup", 7, 2⟩, right := ⟨"source.watsup", 7, 9⟩ }

def boolExp (b : Bool) : exp := ⟨.BoolE b, .BoolT, no_region⟩

def function (out : exp) (hints : List hint := []) : Lang.Al.def :=
  mkPhrase (.FuncDecD (mkPhrase "f") [] [] (mkPhrase .BoolT)
    [mkPhrase ([], out, [])] none hints)

def relation (inputs : List Int) : Lang.Al.def :=
  mkPhrase (.RelD (mkPhrase "R") (mkPhrase (.Arg (mkPhrase .BoolT))) inputs [] none [])

def variant (origin : String) (hints : List hint := []) : Lang.Al.def :=
  mkPhrase (.TypD (mkPhrase "T") [] (mkPhrase (.VariantT [
    .mk (mkPhrase (.Atom (mkPhrase (.Tag "C"))))
      (mkPhrase (.mk (mkPhrase origin) [])) hints])) [])

-- Regions and hints are the only permitted erasures, including nested ones.
#guard sameDef (function (boolExp true) [.str "ignored"]) (function (boolExp true))
#guard sameDef (variant "T" [.str "ignored"]) (variant "T")
#guard sameDef (located (function (boolExp true)).it) (function (boolExp true))
#guard sameDef
  (mkPhrase (.ExternTypD (located "T") []))
  (mkPhrase (.ExternTypD (mkPhrase "T") []))

-- A changed payload, type note, type origin or input position must fail.
#guard !sameDef (function (boolExp true)) (function (boolExp false))
#guard !sameDef (function (boolExp true))
  (function { boolExp true with note := .TextT })
#guard !sameDef (variant "T") (variant "U")
#guard !sameDef (relation [0]) (relation [])

-- Preserve nested path notes and operator constructors.
def update (note : typ') : Lang.Al.def :=
  function ⟨.UpdE (boolExp true) ⟨.RootP, note, no_region⟩ (boolExp false), .BoolT, no_region⟩

#guard !sameDef (update .BoolT) (update .TextT)
#guard !sameDef (function ⟨.UnE .NotOp .BoolT (boolExp true), .BoolT, no_region⟩)
  (function ⟨.UnE .PlusOp .BoolT (boolExp true), .BoolT, no_region⟩)

-- List comparison detects missing, duplicated, reordered and extra entries;
-- only source VarD entries are omitted from the quoted domain.
def a := function (boolExp true)
def b := relation [0]
def metavariable : Lang.Al.def := mkPhrase (.VarD (mkPhrase "x") (mkPhrase .BoolT) [])

#guard (compareSpecs [a, metavariable, b] [a, b]).isOk
#guard !(compareSpecs [a, b] [a]).isOk
#guard !(compareSpecs [a, b] [a, a]).isOk
#guard !(compareSpecs [a, b] [b, a]).isOk
#guard !(compareSpecs [a] [a, b]).isOk
#guard !(compareSpecs [a] [a, metavariable]).isOk

-- Regression: type `f`, function `$f` and metavariable `f` are distinct.
-- Type quotation and module placement must use the type's own definition.
def typeF : Lang.Al.def := mkPhrase
  (.TypD (mkPhrase "f") [] (mkPhrase (.PlainT (mkPhrase .BoolT))) [])
  { left := ⟨"0-types.watsup", 1, 0⟩, right := ⟨"0-types.watsup", 1, 1⟩ }

def functionF : Lang.Al.def :=
  { a with «at» := {
    left := ⟨"1-funcs.watsup", 1, 0⟩,
    right := ⟨"1-funcs.watsup", 1, 1⟩ } }

def namespacesStaySeparate : Bool :=
  let varDef := mkPhrase (.VarD (mkPhrase "f") (mkPhrase .BoolT) [])
  let spec := [typeF, functionF, varDef]
  match Codegen.Emit.plan (Codegen.Env.ofSpec "Test" spec) spec with
  | .error _ => false
  | .ok (units, _, _) => units.any fun u =>
      u.id == "T:f" && u.file == 0 && (Codegen.render u.decls).contains ".TypD"

#guard namespacesStaySeparate

end P4SpecTecTest.QuoteChecks
