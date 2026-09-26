import Lean.Elab.Command
import P4SpecTec.Codegen.StateValidate
import P4SpecTec.Tactic.StateRefine
import P4SpecTec.Tactic.Audit

/-! Exact-state refinement of functions emitted from their actual AL definitions. -/

namespace P4SpecTecTest.StateValidate

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Codegen
open P4SpecTec.Lang.Il P4SpecTec.Lang.Al

def «$fresh_typeId».al : Lang.Al.def :=
  Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] (Q.t .TextT) [])

def «$allocate».al : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i "allocate") [] [] (Q.t .TextT)
    [Q.cl [] (Q.e (.CallE (Q.i "fresh_typeId") [] []) .TextT) []] none [])

def «$retry».al : Lang.Al.def :=
  let fresh := Q.e (.CallE (Q.i "allocate") [] []) .TextT
  let x := Q.e (.VarE (Q.i "x")) .TextT
  Q.d (.FuncDecD (Q.i "retry") [] [] (Q.t .TextT)
    [Q.cl [] x [Q.pr (.LetPr x fresh), Q.pr (.IfPr (Q.e (.BoolE false) .BoolT))]]
    (some (Q.cl [] fresh [])) [])

def «$choose».al : Lang.Al.def :=
  let b := Q.e (.VarE (Q.i "b")) .BoolT
  Q.d (.FuncDecD (Q.i "choose") [] [Q.pm (.ExpP (Q.t .BoolT))] (Q.t .TextT)
    [Q.cl [Q.ar (.ExpA b)] (Q.e (.CallE (Q.i "retry") [] []) .TextT) [Q.pr (.IfPr b)]]
    (some (Q.cl [Q.ar (.ExpA b)] (Q.e (.CallE (Q.i "allocate") [] []) .TextT) [])) [])

def «$hardError».al : Lang.Al.def :=
  let fresh := Q.e (.CallE (Q.i "allocate") [] []) .TextT
  let natT := Q.t (.NumT .NatT)
  let quotient := Q.e (.BinE .DivOp .NatT
    (Q.e (.NumE (.Nat 1)) natT.it) (Q.e (.NumE (.Nat 0)) natT.it)) natT.it
  Q.d (.FuncDecD (Q.i "hardError") [] [] natT
    [Q.cl [] quotient [Q.pr (.DebugPr fresh)]]
    (some (Q.cl [] (Q.e (.NumE (.Nat 99)) natT.it) [])) [])

def «$echo».al : Lang.Al.def :=
  let n := Q.e (.VarE (Q.i "n")) (.NumT .NatT)
  let alias := Q.e (.VarE (Q.i "alias")) (.NumT .NatT)
  Q.d (.FuncDecD (Q.i "echo") [] [Q.pm (.ExpP (Q.t (.NumT .NatT)))] (Q.t (.NumT .NatT))
    [Q.cl [Q.ar (.ExpA n)] alias
      [Q.pr (.LetPr alias n), Q.pr (.DebugPr (Q.e (.CallE (Q.i "choose") []
        [Q.ar (.ExpA (Q.e (.BoolE true) .BoolT))]) .TextT))]] none [])

def «$mismatch».al : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i "mismatch") [] [] (Q.t .TextT)
    [Q.cl [] (Q.e (.TextE (ByteText.ofString "")) .TextT)
      [Q.pr (.DebugPr (Q.e (.CallE (Q.i "allocate") [] []) .TextT)),
        Q.pr (.IfPr (Q.e (.BoolE false) .BoolT))]] none [])

def spec : Lang.Al.spec := [«$fresh_typeId».al, «$allocate».al, «$retry».al, «$choose».al,
  «$hardError».al, «$echo».al, «$mismatch».al]

run_cmd do
  let env := Env.ofSpec "P4SpecTecTest.StateValidate" spec
  for d in spec do
    let result : Except String Std.Format := match d.it with
      | .BuiltinDecD i ts ps t _ =>
        Funcs.builtinDecl env i.it (ts.map (·.it)) (ps.map (·.it)) t.it
      | .FuncDecD i ts ps t cs ec _ =>
        Funcs.funcDecl { env } false false i.it (ts.map (·.it)) (ps.map (·.it)) t.it cs ec
      | _ => .error "unexpected fixture definition"
    let f ← match result with | .ok f => pure f | .error e => throwError e
    let source := Codegen.render f
    let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `command source with
      | .ok stx => pure stx
      | .error e => throwError "{source}\n{e}"
    Lean.Elab.Command.elabCommand stx

run_cmd do
  let env := Env.ofSpec "P4SpecTecTest.StateValidate" spec
  for d in spec do
    if let some reason := Codegen.StateValidate.unsupported env [] d then
      throwError "unexpected exclusion: {reason}"
    let member ← match Props.memberOf { env } d with
      | .ok m => pure m | .error e => throwError e
    for f in Codegen.StateValidate.groupTheorems "P4SpecTecTest.StateValidate" false [member] [] do
      let source := Codegen.render f
      let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `command source with
        | .ok stx => pure stx
        | .error e => throwError "{source}\n{e}"
      Lean.Elab.Command.elabCommand stx

#guard match «$retry» 3 with
  | some (.ok text, state) => text == ByteText.ofString "FRESH__4" && state == 5
  | _ => false

#guard match «$hardError» 3 with
  | some (.error .err, state) => state == 4
  | _ => false

#guard match «$echo» 17 3 with
  | some (.ok n, state) => n == 17 && state == 5
  | _ => false

#guard match «$mismatch» 3 with
  | some (.error .unmatch, state) => state == 4
  | _ => false

#guard (Codegen.StateValidate.unsupported (Env.ofSpec "Probe" spec) []
  (Q.d (.RelD (Q.i "unsupported") (Q.nt (.Seq [])) [] [] none []))).isSome

#guard (Codegen.StateValidate.unsupported (Env.ofSpec "Probe" spec) []
  (Q.d (.BuiltinDecD (Q.i "other") [] [] (Q.t .TextT) []))).isSome

#guard (Codegen.StateValidate.groupTheorems "Probe" true [] [("f", "recursive")]).length == 1

end P4SpecTecTest.StateValidate
