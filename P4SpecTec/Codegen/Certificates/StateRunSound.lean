import P4SpecTec.Codegen.StateProps
import P4SpecTec.Codegen.Certificates.RunSound

/-! Emit exact-state relation run-soundness certificates. -/

namespace P4SpecTec.Codegen.StateProps

open Std
open P4SpecTec.Codegen
open P4SpecTec.Codegen.Term
open P4SpecTec.Codegen.Funcs

/-- The exact state-indexed successful result contract of a nonrecursive relation. -/
def runSound (externs : Bool) (m : Props.Member) : Except String Format := do
  if !m.isRel then throw "state run-soundness requires a relation"
  let ps := paramNames m.params.length
  let ext := if externs then Format.text " [Externs]" else Format.nil
  let outArg := if m.nOuts == 0 then "()" else "o"
  let obs := if m.nOuts == 0 then Format.nil
    else Format.line ++ Format.text "(o : " ++ m.ret.fmt ++ ")"
  let states := Format.line ++ "(«@s0» «@sf» : FreshState)"
  let call := (Term.call m.defName (ps.map Term.atom ++ [.atom "«@s0»"])).fmt
  let stmt := Props.eqn call (someOk (.atom outArg) "«@sf»") ++ " →" ++ Format.line ++
    m.conclusion ++ " «@s0» «@sf»"
  pure (Format.group (Format.nest 4 (Format.text ("theorem " ++ m.localName ++ "_sound") ++
    ext ++ Props.paramBinders m.params ++ obs ++ states ++ " :" ++ Format.line ++ stmt ++
    " :=")) ++ Format.nest 2 (Format.line ++ "by state_run_sound"))

end P4SpecTec.Codegen.StateProps
