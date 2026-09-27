import Lean.Elab.Command
import P4SpecTec.Codegen.Types
import P4SpecTec.Prelude.Value
import P4SpecTec.Refine.Quote

/-! Source-named decoder selection, including nested legal parameter instances. -/

namespace P4SpecTecTest.Codegen.Types
open P4SpecTec P4SpecTec.Refine P4SpecTec.Prelude P4SpecTec.Codegen
private def declarations : Lang.Al.spec := [
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
    (Q.t (.IterT (Q.t (Q.varT "base" [])) .List)))) [])]
-- An unrelated local dictionary must not alter declared closed field decoders.
local instance : OfValue ByteText := ⟨fun _ _ => none⟩
private def bytes := ByteText.ofString "hello"
open Lean Elab Command in
run_cmd do
  let env := Env.ofSpec "P4SpecTecTest.Codegen.Types" declarations
  for d in declarations do
    let .TypD id params body _ := d.it | throwError "expected type"
    let ps := params.map (·.it)
    let group := [(id.it, ps, body.it)]
    for f in [Types.typeDecl env [] id.it ps body.it,
        Types.toValueDecls env group, Types.ofValueDecls env group] do
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
end P4SpecTecTest.Codegen.Types
