import Lean.Elab.Command
import P4SpecTec.Codegen.Types
import P4SpecTec.Prelude.Extern
import P4SpecTec.Refine.Quote

/-! Source-named codec dictionaries, including nested parameters and hostile ambient instances. -/

namespace P4SpecTecTest.Codegen.Types
open P4SpecTec P4SpecTec.Refine P4SpecTec.Prelude P4SpecTec.Codegen
-- Three cases with the same atoms, told apart only by their argument.
private def wrappedCases : List Lang.Il.typ' := [.BoolT, .NumT .NatT, .TextT]
private def declarations : Lang.Al.spec := [
  Q.d (.ExternTypD (Q.i "opaque") []),
  Q.d (.TypD (Q.i "state") [] (Q.dt (.PlainT (Q.t (Q.varT "opaque" [])))) []),
  Q.d (.TypD (Q.i "states") [] (Q.dt (.PlainT
    (Q.t (.IterT (Q.t (Q.varT "opaque" [])) .List)))) []),
  Q.d (.TypD (Q.i "K") [] (Q.dt (.PlainT (Q.t .BoolT))) []),
  Q.d (.TypD (Q.i "base") [] (Q.dt (.PlainT (Q.t .TextT))) []),
  Q.d (.TypD (Q.i "unrelated") [] (Q.dt (.PlainT (Q.t .TextT))) []),
  Q.d (.TypD (Q.i "alias") [] (Q.dt (.PlainT (Q.t (Q.varT "base" [])))) []),
  Q.d (.TypD (Q.i "box") [Q.i "K"] (Q.dt (.VariantT
    [Q.tc (.Brack (Q.a .LParen) (.Arg (Q.t (Q.varT "K" []))) (Q.a .RParen))
      "box" [Q.t (Q.varT "K" [])]])) []),
  Q.d (.TypD (Q.i "boxed") [] (Q.dt (.PlainT
    (Q.t (Q.varT "box" [Q.t (Q.varT "base" [])])))) []),
  Q.d (.TypD (Q.i "listed") [] (Q.dt (.PlainT
    (Q.t (.IterT (Q.t (Q.varT "base" [])) .List)))) []),
  Q.d (.TypD (Q.i "pair") [] (Q.dt (.PlainT
    (Q.t (.TupleT [Q.t (Q.varT "base" []), Q.t .BoolT])))) []),
  Q.d (.TypD (Q.i "triple") [] (Q.dt (.PlainT
    (Q.t (.TupleT [Q.t .BoolT, Q.t (Q.varT "base" []), Q.t (.NumT .NatT)])))) []),
  Q.d (.TypD (Q.i "wrapped") [] (Q.dt (.VariantT (wrappedCases.map fun t =>
    Q.tc (.Brack (Q.a .LParen) (.Arg (Q.t t)) (Q.a .RParen)) "wrapped"))) [])]
-- An unrelated local dictionary must not alter declared closed field decoders.
local instance : OfValue ByteText := ⟨fun _ _ => none⟩
local instance : ToValue ByteText := ⟨fun _ => Runtime.Value.Make.bool false⟩
local instance : OfValue ExternValue := ⟨fun _ _ => none⟩
local instance : ToValue ExternValue := ⟨fun _ => Runtime.Value.Make.bool false⟩
private def bytes := ByteText.ofString "hello"
open Lean Elab Command in
run_cmd do
  let env := Env.ofSpec "P4SpecTecTest.Codegen.Types" declarations
  for d in declarations do
    let formats ← match d.it with
      | .ExternTypD name _ =>
        pure [Std.Format.text s!"abbrev {Names.typeName name.it} := ExternValue"]
      | .TypD name params body _ =>
        let ps := params.map (·.it)
        let group := [(name.it, ps, body.it)]
        pure [Types.typeDecl env [] name.it ps body.it,
          Types.toValueDecls env group, Types.ofValueDecls env group]
      | _ => throwError "expected type"
    for f in formats do
      for text in ((render f).replace "\ninstance" "\n\ninstance").splitOn "\n\n" do
        let command ← match Parser.runParserCategory (← getEnv) `command text with
          | .ok command => pure command
          | .error message => throwError "{text}\n{message}"
        elabCommand command
-- Local box<K> still binds K independently of the global Boolean alias.
#guard K.ofValue 1 (Runtime.Value.Make.bool true) == some true
#guard base.ofValue 1 (Runtime.Value.Make.text bytes) == some bytes
#guard unrelated.ofValue 1 (Runtime.Value.Make.text bytes) == some bytes
#guard alias.ofValue 1 (Runtime.Value.Make.text bytes) == none
#guard alias.ofValue 2 (Runtime.Value.Make.text bytes) == some bytes
#guard listed.ofValue 2 (Runtime.Value.Make.list .TextT [Runtime.Value.Make.text bytes]) ==
  some [bytes]
#guard boxed.ofValue 3 (toValue (box.lparen_rparen bytes)) ==
  some (box.lparen_rparen bytes)
-- Primitive, nominal, nested list and parameter dictionaries follow the source declaration.
#guard match base.toValue bytes |>.it with | .TextV text => text == bytes | _ => false
#guard match alias.toValue bytes |>.it with | .TextV text => text == bytes | _ => false
#guard match listed.toValue [bytes] |>.it with
  | .ListV [v] => match v.it with | .TextV text => text == bytes | _ => false
  | _ => false
#guard boxed.ofValue 3 (boxed.toValue (box.lparen_rparen bytes)) ==
  some (box.lparen_rparen bytes)
-- A tuple outside any recursive group decodes by arity and component: there is no product
-- instance, and the nominal component keeps its declared decoder.
private def tupleValue (vs : List Lang.Il.value) := Runtime.Value.Make.tuple .TextT vs
private def text := Runtime.Value.Make.text bytes
private def yes := Runtime.Value.Make.bool true
#guard match pair.ofValue 2 (tupleValue [text, yes]) with
  | some (b, flag) => b == bytes && flag
  | none => false
#guard (pair.ofValue 2 (tupleValue [text, yes, yes])).isNone
#guard (pair.ofValue 2 (tupleValue [text])).isNone
#guard (pair.ofValue 2 (tupleValue [yes, text])).isNone
#guard match triple.ofValue 2 (tupleValue [yes, text, Runtime.Value.Make.nat 3]) with
  | some (flag, b, n) => flag && b == bytes && n == 3
  | none => false
#guard (triple.ofValue 2 (tupleValue [yes, text])).isNone
-- Every case with repeated atoms has its own constructor, counted from the second.
#guard Types.ctorNames (wrappedCases.map fun t =>
    Q.tc (.Brack (Q.a .LParen) (.Arg (Q.t t)) (Q.a .RParen)) "wrapped") ==
  ["lparen_rparen", "lparen_rparen_2", "lparen_rparen_3"]
#guard match wrapped.ofValue 2 (wrapped.toValue (.lparen_rparen_3 bytes)) with
  | some (.lparen_rparen_3 b) => b == bytes
  | _ => false
#guard match wrapped.ofValue 2 (wrapped.toValue (.lparen_rparen_2 3)) with
  | some (.lparen_rparen_2 n) => n == 3
  | _ => false
-- Declared externs keep the JSON dictionaries even under hostile ambient instances.
private def externalValue := Runtime.Value.Make.extern (Q.varT "opaque" []) (.str "payload")
#guard state.ofValue 1 externalValue == some (ExternValue.mk (.str "payload"))
#guard states.ofValue 1 (Runtime.Value.Make.list (Q.varT "opaque" []) [externalValue]) ==
  some [ExternValue.mk (.str "payload")]
#guard match state.toValue (ExternValue.mk (.str "payload")) |>.it with
  | .ExternV json => json.compress == "\"payload\""
  | _ => false
end P4SpecTecTest.Codegen.Types
