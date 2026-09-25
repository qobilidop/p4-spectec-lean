import Lean.Elab.Command
import P4SpecTec.Codegen.Emit

/-!
Parameterized subtype bridge regressions. The small AL fixture is rendered
by the production type and bridge emitters; `run_cmd` then asks Lean to parse
and elaborate those exact declarations and executable checks.
-/

namespace P4SpecTecTest.Subtypes

open P4SpecTec P4SpecTec.Util.Source P4SpecTec.Lang.Il P4SpecTec.Domain
open P4SpecTec.Codegen

def varT (id : String) (args : List typ' := []) : typ' :=
  .VarT (mkPhrase id) (args.map mkPhrase)

def caseOf (tag : String) (payload : Option typ') : typcase :=
  let atom := Mixfix.t.Atom (mkPhrase (Atom.t.Tag tag))
  let caseShape := match payload with
    | some t => Mixfix.t.Seq [atom, .Arg (mkPhrase t)]
    | none => atom
  .mk (mkPhrase caseShape) (mkPhrase (.mk (mkPhrase "fixture") [])) []

def variant (id : String) (params : List String) (cases : List typcase) : Lang.Al.def :=
  mkPhrase (.TypD (mkPhrase id) (params.map mkPhrase)
    (mkPhrase (.VariantT cases)) [])

def alias (id : String) (t : typ') : Lang.Al.def :=
  mkPhrase (.TypD (mkPhrase id) [] (mkPhrase (.PlainT (mkPhrase t))) [])

def spec : Lang.Al.spec := [
  variant "Box" ["X"] [caseOf "C" (some (varT "X"))],
  variant "Sum" ["X"] [caseOf "C" (some (varT "X")), caseOf "D" none],
  variant "Wrong" ["X"] [caseOf "C" (some .TextT), caseOf "D" none],
  variant "Missing" ["X"] [caseOf "D" none],
  alias "NatAlias" (.NumT .NatT)]

def env : Env := Env.ofSpec "P4SpecTecTest.Subtypes" spec

def boxNat : typ' := varT "Box" [.NumT .NatT]
def sumNat : typ' := varT "Sum" [.NumT .NatT]
def boxText : typ' := varT "Box" [.TextT]
def sumText : typ' := varT "Sum" [.TextT]

#guard (Types.subtypeDecls env boxNat sumNat).isOk
#guard (Types.subtypeDecls env boxText sumText).isOk
#guard (Types.subtypeDecls env (varT "Box" [varT "NatAlias"]) sumNat).isOk
#guard !(Types.subtypeDecls env boxNat (varT "Wrong" [.NumT .NatT])).isOk
#guard !(Types.subtypeDecls env boxNat (varT "Missing" [.NumT .NatT])).isOk
#guard !(Types.subtypeDecls env (varT "Box" [.NumT .NatT, .TextT]) sumNat).isOk
#guard !(Types.subtypeDecls env (varT "Ghost") sumNat).isOk
#guard !(Types.subtypeDecls env (varT "Box" [varT "Free"]) sumNat).isOk
#guard !(Types.subtypeDecls env boxNat boxText).isOk

#guard Types.upName (varT "Small") (varT "Wide") == "Small.to_Wide"
#guard Types.downName (varT "Small") (varT "Wide") == "Wide.of_Small"
#guard Types.isName (varT "Small") (varT "Wide") == "Wide.is_Small"
#guard Types.upName boxNat sumNat != Types.upName boxText sumText
#guard Types.downName boxNat sumNat != Types.downName boxText sumText
#guard Types.isName boxNat sumNat != Types.isName boxText sumText
#guard !Types.typEq boxNat boxText

-- Repeated construction with different source regions yields the same bridge.
def locatedNat : typ' := .VarT (mkPhrase "Box" {
  left := ⟨"fixture", 1, 1⟩, right := ⟨"fixture", 1, 4⟩ })
  [mkPhrase (.NumT .NatT) {
    left := ⟨"fixture", 1, 5⟩, right := ⟨"fixture", 1, 8⟩ }]

#guard Types.typEq boxNat locatedNat
#guard Types.upName boxNat sumNat == Types.upName locatedNat sumNat

def source (t : typ') : exp := ⟨.VarE (mkPhrase "x"), t, no_region⟩

def cast (sub sup : typ') : exp :=
  ⟨.UpCastE (mkPhrase sup) (source sub), sup, no_region⟩

def nestedSub : typ' := .TupleT [mkPhrase boxNat,
  mkPhrase (.IterT (mkPhrase boxText) .List),
  mkPhrase (.IterT (mkPhrase boxNat) .Opt)]

def nestedSup : typ' := .TupleT [mkPhrase sumNat,
  mkPhrase (.IterT (mkPhrase sumText) .List),
  mkPhrase (.IterT (mkPhrase sumNat) .Opt)]

def hasPair (pairs : List (typ' × typ')) (s t : typ') : Bool :=
  pairs.any fun (a, b) => Types.typEq a s && Types.typEq b t

-- The cast collector reaches tuple positions and both iteration forms.
#guard (Exp.pairsOfExp env (cast nestedSub nestedSup)).length == 3
#guard hasPair (Exp.pairsOfExp env (cast nestedSub nestedSup)) boxNat sumNat
#guard hasPair (Exp.pairsOfExp env (cast nestedSub nestedSup)) boxText sumText

def castFunction (sub sup : typ') : Lang.Al.def :=
  mkPhrase (.FuncDecD (mkPhrase "f") [] [mkPhrase (.ExpP (mkPhrase sub))]
    (mkPhrase sup) [mkPhrase ([mkPhrase (.ExpA (source sub))], cast sub sup, [])] none [])

-- The spec collector deduplicates the repeated Nat pair, retaining Text.
#guard (Exp.pairsOfSpec env (spec ++ [castFunction nestedSub nestedSup])).length == 2
#guard hasPair (Exp.pairsOfExp env (cast boxNat boxText)) boxNat boxText
#guard (Exp.pairsOfExp env (cast boxNat boxText)).length == 1

def atFile (file : String) (d : Lang.Al.def) : Lang.Al.def :=
  { d with «at» := {
    left := ⟨file, 1, 0⟩, right := ⟨file, 1, 1⟩ } }

def placementSpec : Lang.Al.spec := [
  atFile "0-box.watsup" (variant "Box" ["X"] [caseOf "C" (some (varT "X"))]),
  atFile "1-sum.watsup" (variant "Sum" ["X"]
    [caseOf "C" (some (varT "X")), caseOf "D" none]),
  atFile "2-alias.watsup" (alias "NatAlias" (.NumT .NatT)),
  atFile "3-function.watsup" (castFunction
    (varT "Box" [varT "NatAlias"]) sumNat)]

-- A bridge waits for a type used only as a later specialization argument.
def bridgeAfterArgument : Bool :=
  let e := Env.ofSpec "Placement" placementSpec
  match Emit.plan e placementSpec with
  | .error _ => false
  | .ok (units, _, _) => units.any fun u =>
      u.id == "S:" ++ Types.upName (varT "Box" [varT "NatAlias"]) sumNat &&
        u.file == 2

#guard bridgeAfterArgument

open Lean Elab Command in
run_cmd do
  let render := Codegen.render
  let typeSources := [
    Types.typeDecl env [] "Box" ["X"]
      (.VariantT [caseOf "C" (some (varT "X"))]),
    Types.typeDecl env [] "Sum" ["X"]
      (.VariantT [caseOf "C" (some (varT "X")), caseOf "D" none]),
    Types.typeDecl env [] "NatAlias" [] (.PlainT (mkPhrase (.NumT .NatT)))]
  let pairs := [(boxNat, sumNat), (boxText, sumText),
    (varT "Box" [varT "NatAlias"], sumNat)]
  let mut sources := typeSources.map render
  for (s, t) in pairs do
    match Types.subtypeDecls env s t with
    | .error err => throwError "bridge emission failed: {err}"
    | .ok fmt => sources := sources ++ ((render fmt).splitOn "\n\n")
  let castText (m : Exp.CgM Codegen.Term) : CommandElabM String := do
    match Exp.run { env } m with
    | .error err => throwError "cast emission failed: {err}"
    | .ok term => pure (render term.fmt)
  let callUp ← castText <| Exp.castUp boxNat sumNat
    (.atom "(Box._C 7)")
  let callDown ← castText <| Exp.castDown boxNat sumNat
    (.atom "(Sum._C 7)")
  let callIs ← castText <| Exp.isSub boxNat sumNat
    (.atom "Sum._D")
  let listBox : typ' := .IterT (mkPhrase boxNat) .List
  let listSum : typ' := .IterT (mkPhrase sumNat) .List
  let callList ← castText <| Exp.castUp listBox listSum
    (.atom "[Box._C 1, Box._C 2]")
  let q := "P4SpecTecTest.Subtypes."
  let textX := "(P4SpecTec.ByteText.ofString \"x\")"
  let checks := [
    s!"#guard (match {q}{Types.upName boxNat sumNat} (Box._C 7) with " ++
      "| Sum._C n => n == 7 | _ => false)",
    s!"#guard (match {q}{Types.downName boxNat sumNat} (Sum._C 7) with " ++
      "| some (Box._C n) => n == 7 | _ => false)",
    s!"#guard (match {q}{Types.downName boxNat sumNat} Sum._D with " ++
      "| none => true | _ => false)",
    s!"#guard {q}{Types.isName boxNat sumNat} (Sum._C 7)",
    s!"#guard !{q}{Types.isName boxNat sumNat} Sum._D",
    s!"#guard (match {q}{Types.upName boxText sumText} (Box._C {textX}) with " ++
      s!"| Sum._C s => s == {textX} | _ => false)",
    s!"#guard (match {q}{Types.downName boxText sumText} (Sum._C {textX}) with " ++
      s!"| some (Box._C s) => s == {textX} | _ => false)",
    s!"#guard {q}{Types.isName boxText sumText} (Sum._C {textX})",
    s!"#guard (match {q}{Types.upName (varT "Box" [varT "NatAlias"]) sumNat} " ++
      "(Box._C 7) with | Sum._C n => n == 7 | _ => false)",
    s!"#guard (match {callUp} with | Sum._C n => n == 7 | _ => false)",
    s!"#guard (match {callDown} with | some (Box._C n) => n == 7 | _ => false)",
    s!"#guard !{callIs}",
    s!"#guard (match {callList} with " ++
      "| [Sum._C a, Sum._C b] => a == 1 && b == 2 | _ => false)"]
  for source in sources ++ checks do
    let stx ← match Lean.Parser.runParserCategory (← getEnv) `command source with
      | .ok stx => pure stx
      | .error err => throwError "generated command did not parse:\n{source}\n{err}"
    Lean.Elab.Command.elabCommand stx

end P4SpecTecTest.Subtypes
