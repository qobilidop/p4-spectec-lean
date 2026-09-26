import Lean.Elab.Command
import P4SpecTec.Codegen.Rels
import P4SpecTec.Codegen.Emit
import P4SpecTec.Refine.Quote
import P4SpecTec.Prelude
import P4SpecTec.Prelude.StateEval
import P4SpecTec.Tactic.Monotonicity

/-! Parse, elaborate and execute production-emitted stateful callable definitions. -/

namespace P4SpecTecTest.StateCodegen

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Codegen
open P4SpecTec.Lang.Il P4SpecTec.Lang.Al

private def textT := Q.t .TextT
private def natT : typ' := .NumT .NatT
private def listT : typ' := .IterT (Q.t natT) .List
private def varE (s : String) (t : typ' := .TextT) := Q.e (.VarE (Q.i s)) t
private def call (s : String) (args : List arg := []) (t : typ' := .TextT) :=
  Q.e (.CallE (Q.i s) [] args) t
private def fresh := call "fresh_typeId"
private def no : prem := Q.pr (.IfPr (Q.e (.BoolE false) .BoolT))
private def save : prem := Q.pr (.LetPr (varE "x") fresh)
private def debug (e : exp) := Q.pr (.DebugPr e)
private def iterInput := Q.e (.IterE (varE "n" natT) (.mk .List [Q.v "n" natT])) listT
private def optInput (name : String) :=
  Q.e (.IterE (varE name natT) (.mk .Opt [Q.v name natT])) (.IterT (Q.t natT) .Opt)
private def optionalExpr : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i "optionalExpr") []
    [Q.pm (.ExpP (Q.t (.IterT (Q.t natT) .Opt))),
     Q.pm (.ExpP (Q.t (.IterT (Q.t natT) .Opt)))] (Q.t (.IterT (Q.t natT) .Opt))
    [Q.cl [Q.ar (.ExpA (optInput "n")), Q.ar (.ExpA (optInput "m"))]
      (Q.e (.IterE (Q.e (.NumE (.Nat 3)) natT)
        (.mk .Opt [Q.v "n" natT, Q.v "m" natT])) (.IterT (Q.t natT) .Opt)) []] none [])
private def fn (s : String) (prems : List prem) (out : exp := fresh) : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i s) [] [] textT [Q.cl [] out prems] none [])
private def callback (s head : String) : Lang.Al.def :=
  let args := if head == "f" then [] else [Q.ar (.DefA (Q.i "f"))]
  Q.d (.FuncDecD (Q.i s) [] [Q.pm (.DefP (Q.i "f") [] [] textT)] textT
    [Q.cl [Q.ar (.DefA (Q.i "f"))] (call head args) []] none [])
private def relation (name : String) (prems : List prem) : Lang.Al.def :=
  Q.d (.RelD (Q.i name) (Q.nt (.Seq [])) []
    [Q.rg "g" ([], [], []) [Q.rp "p" prems []]] none [])
private def negative (name target : String) : Lang.Al.def :=
  let tagged (tag : String) :=
    Q.e (.CatE (Q.e (.TextE (ByteText.ofString tag)) .TextT) fresh) .TextT
  Q.d (.FuncDecD (Q.i name) [] [] textT
    [Q.cl [] (tagged "first:") [Q.pr (.IfNotHoldPr (Q.i target) (.Seq []))],
     Q.cl [] (tagged "fallback:") []] none [])
private def spec : Lang.Al.spec := [
  Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] textT []), optionalExpr,
  Q.d (.BuiltinDecD (Q.i "text_to_int") [] [Q.pm (.ExpP textT)] (Q.t (.NumT .IntT)) []),
  Q.d (.ExternDecD (Q.i "external") [] [] textT []),
  Q.d (.ExternRelD (Q.i "externalRel") (Q.nt (.Arg textT)) [] []),
  fn "allocate" [],
  fn "externalRelation" [Q.pr (.RulePr (Q.i "externalRel") (.Arg (varE "x")) [])]
    (varE "x"),
  fn "f" [] (Q.e (.TextE (ByteText.ofString "global-shadow")) .TextT),
  fn "debugFresh" [debug fresh],
  fn "debugError" [debug (call "text_to_int"
    [Q.ar (.ExpA (Q.e (.TextE (ByteText.ofString "bad")) .TextT))] (.NumT .IntT))],
  callback "through" "f", callback "forward" "through",
  Q.d (.FuncDecD (Q.i "nested") []
    [Q.pm (.DefP (Q.i "g") [] [Q.pm (.DefP (Q.i "h") [] [] textT)] textT),
     Q.pm (.DefP (Q.i "f") [] [] textT)] textT
    [Q.cl [Q.ar (.DefA (Q.i "g")), Q.ar (.DefA (Q.i "f"))]
      (call "g" [Q.ar (.DefA (Q.i "f"))]) []] none []),
  fn "namedNested" [] (call "nested"
    [Q.ar (.DefA (Q.i "through")), Q.ar (.DefA (Q.i "allocate"))]),
  Q.d (.FuncDecD (Q.i "shadowExtern") []
    [Q.pm (.DefP (Q.i "external") [] [] textT)] textT
    [Q.cl [Q.ar (.DefA (Q.i "external"))] (call "external") []] none []),
  fn "named" [] (call "forward" [Q.ar (.DefA (Q.i "allocate"))]),
  Q.d (.FuncDecD (Q.i "externRetry") [] [] textT
    [Q.cl [] fresh [debug (call "external")], Q.cl [] fresh []] none []),
  relation "fails" [save, no], relation "holds" [save],
  negative "negative" "fails", negative "negativeSuccess" "holds",
  Q.d (.RelD (Q.i "shared") (Q.nt (.Arg textT)) []
    [Q.rg "g" ([], [], [save])
      [Q.rp "reject" [no] [varE "x"], Q.rp "accept" [] [varE "x"]]] none []),
  Q.d (.FuncDecD (Q.i "drain") [] [Q.pm (.ExpP (Q.t listT))] textT
    [Q.cl [Q.ar (.ExpA (varE "xs" listT))] fresh
       [Q.pr (.IfPr (Q.e (.CmpE .EqOp .NatT
         (Q.e (.LenE (varE "xs" listT)) natT) (Q.e (.NumE (.Nat 0)) natT)) .BoolT))],
     Q.cl [Q.ar (.ExpA (Q.e (.ConsE (varE "h" natT) (varE "t" listT)) listT))]
       (call "drain" [Q.ar (.ExpA (varE "t" listT))]) [debug fresh]] none []),
  Q.d (.FuncDecD (Q.i "ordered") [] [Q.pm (.ExpP (Q.t listT))]
    (Q.t (.IterT textT .List))
    [Q.cl [Q.ar (.ExpA iterInput)]
      (Q.e (.IterE fresh (.mk .List [Q.v "n" natT])) (.IterT textT .List)) []] none []),
  Q.d (.FuncDecD (Q.i "orderedPrem") [] [Q.pm (.ExpP (Q.t listT))] textT
    [Q.cl [Q.ar (.ExpA iterInput)] fresh
      [Q.pr (.IterPr (debug fresh) (.mk .List [Q.v "n" natT] []))]] none []),
  Q.d (.FuncDecD (Q.i "optionalOnce") [] [] (Q.t (.IterT textT .Opt))
    [Q.cl [] (Q.e (.IterE fresh (.mk .Opt [])) (.IterT textT .Opt)) []] none []),
  Q.d (.FuncDecD (Q.i "optionalBound") [] [Q.pm (.ExpP (Q.t (.IterT (Q.t natT) .Opt)))]
    (Q.t (.IterT textT .Opt))
    [Q.cl [Q.ar (.ExpA (Q.e (.IterE (varE "n" natT) (.mk .Opt [Q.v "n" natT]))
      (.IterT (Q.t natT) .Opt)))]
      (Q.e (.IterE fresh (.mk .Opt [Q.v "n" natT])) (.IterT textT .Opt)) []] none []),
  Q.d (.TableDecD (Q.i "tableRetry") [] textT
    [Q.tr [] [] fresh [debug fresh, no], Q.tr [] [] fresh []] []),
  Q.d (.FuncDecD (Q.i "optionalPrem") []
    [Q.pm (.ExpP (Q.t (.IterT (Q.t natT) .Opt)))] textT
    [Q.cl [Q.ar (.ExpA (optInput "n"))] fresh
      [Q.pr (.IterPr (debug fresh) (.mk .Opt [Q.v "n" natT] []))]] none []),
  Q.d (.FuncDecD (Q.i "optionalMixed") []
    [Q.pm (.ExpP (Q.t (.IterT (Q.t natT) .Opt))),
     Q.pm (.ExpP (Q.t (.IterT (Q.t natT) .Opt)))] textT
    [Q.cl [Q.ar (.ExpA (optInput "n")), Q.ar (.ExpA (optInput "m"))] fresh
      [Q.pr (.IterPr (debug fresh) (.mk .Opt [Q.v "n" natT, Q.v "m" natT] []))]] none [])]

private def env := Env.ofSpec "P4SpecTecTest.StateCodegen" spec
#guard env.mode == .freshState
#guard (Env.ofSpec "P4Spec" []).mode == .pure
#guard (Env.ofSpec "P4Spec" [fn "fresh_typeId" []]).mode == .pure
#guard Exp.callsOfDef (callback "forward" "through") == ["through"]
#guard Exp.callsOfDef (callback "through" "f") == []
#guard Exp.callsOfDef (fn "named" [] (call "through" [Q.ar (.DefA (Q.i "allocate"))])) ==
  ["through", "allocate"]
#guard !(Funcs.builtinDecl env "fresh_typeId" [] [.ExpP textT] .TextT).isOk
#guard !(Funcs.builtinDecl env "fresh_typeId" ["T"] [] .TextT).isOk
#guard !(Funcs.builtinDecl env "fresh_typeId" [] [] .BoolT).isOk
#guard !(Funcs.validateCallableType (.FuncT [Q.i "T"] [] textT)).isOk
#guard !(Funcs.validateSignatures (Env.ofSpec "BadExtern"
  [Q.d (.ExternDecD (Q.i "bad") []
    [Q.pm (.DefP (Q.i "g") [] [Q.pm (.DefP (Q.i "f") [Q.i "T"] [] textT)] textT)]
    textT [])])).isOk
#guard !(Funcs.validateSignatures (Env.ofSpec "HiddenPoly"
  [Q.d (.TypD (Q.i "Callback") []
    (Q.dt (.PlainT (Q.t (.FuncT [Q.i "T"] [] (Q.t (Q.varT "T")))))) [])])).isOk
#guard !(Funcs.validateSignatures (Env.ofSpec "FunctionData"
  [Q.d (.TypD (Q.i "Callbacks") []
    (Q.dt (.PlainT (Q.t (.IterT (Q.t (.FuncT [] [] textT)) .List)))) [])])).isOk
private def callableT := Q.t (.FuncT [] [] textT)
#guard !(Funcs.validateSignatures (Env.ofSpec "ExpressionFunction"
  [Q.d (.ExternDecD (Q.i "bad") [] [Q.pm (.ExpP callableT)] textT [])])).isOk
#guard !(Funcs.validateSignatures (Env.ofSpec "FunctionResult"
  [Q.d (.ExternDecD (Q.i "bad") [] [] callableT [])])).isOk
#guard !(Funcs.validateSignatures (Env.ofSpec "CallbackResult"
  [Q.d (.ExternDecD (Q.i "bad") [] [Q.pm (.DefP (Q.i "f") [] [] callableT)]
    textT [])])).isOk
#guard !(Funcs.validateSignatures (Env.ofSpec "RelationFunction"
  [Q.d (.ExternRelD (Q.i "bad") (Q.nt (.Arg callableT)) [] [])])).isOk
#guard match Funcs.funcDecl { env } false false "bad" [] [.ExpP callableT] .TextT
    [] none with | .error _ => true | _ => false
private def callbackTable : Lang.Al.def :=
  Q.d (.TableDecD (Q.i "callbackTable") [Q.pm (.DefP (Q.i "f") [] [] textT)] textT
    [Q.tr [] [Q.ar (.DefA (Q.i "f"))] (call "f") []] [])
#guard Validate.unsupported (Env.ofSpec "CallbackTable" [callbackTable]) [] callbackTable ==
  some "function-typed parameter"
#guard !(Exp.run { env } (Exp.compileExp
  (call "through" [Q.ar (.DefA (Q.i "fresh_typeId"))]))).isOk
#guard !(Exp.run { env } (Exp.compileExp
  (call "through" [Q.ar (.DefA (Q.i "external"))]))).isOk
#guard Exp.callsOfDef (fn "externArg" [] (call "through" [Q.ar (.DefA (Q.i "external"))])) ==
  ["through", "external"]

-- Production planning sees a dependency carried only by a function argument,
-- and propagates the extern requirement from that argument.
private def depSpec : Lang.Al.spec := [
  Q.d (.ExternDecD (Q.i "external") [] [] textT []),
  callback "through" "f",
  fn "source" [] (call "through" [Q.ar (.DefA (Q.i "later"))]),
  fn "later" [] (call "through" [Q.ar (.DefA (Q.i "source"))]),
  fn "externalWrapper" [] (call "external"),
  fn "externArg" [] (call "through" [Q.ar (.DefA (Q.i "externalWrapper"))])]
private def depEnv := Env.ofSpec "DependencyTest" depSpec
#guard match Emit.plan depEnv depSpec with
  | .ok (units, _, _) =>
    (units.any fun u => u.externs && (Codegen.render u.decls).contains "«$externArg»") &&
    (units.any fun u =>
      let text := Codegen.render u.decls
      text.contains "mutual" && text.contains "«$source»" && text.contains "«$later»")
  | .error _ => false
#guard !(Emit.plan env spec).isOk
#guard match Emit.generate "DependencyTest" "fixture.al.json" depSpec with
  | .ok outputs => outputs.any fun o =>
    o.text.contains "import P4SpecTec.Tactic.Monotonicity\n" &&
      o.text.contains "codegen_monotonicity"
  | .error _ => false

-- The SCC's only inter-member edges are DefA arguments. `walk` is itself
-- recursive, so exposing only its equation (instead of its fixpoint) is insufficient.
private def cycleSpec (stateful : Bool) : Lang.Al.spec := Id.run do
  let xs := Q.ar (.ExpA (varE "xs" listT))
  let tail := Q.ar (.ExpA (varE "tail" listT))
  let cons := Q.ar (.ExpA
    (Q.e (.ConsE (varE "head" natT) (varE "tail" listT)) listT))
  let empty := Q.pr (.IfPr (Q.e (.CmpE .EqOp .NatT
    (Q.e (.LenE (varE "xs" listT)) natT) (Q.e (.NumE (.Nat 0)) natT)) .BoolT))
  let ps := [Q.pm (.DefP (Q.i "f") [] [Q.pm (.ExpP (Q.t listT))] textT),
    Q.pm (.ExpP (Q.t listT))]
  let f := Q.ar (.DefA (Q.i "f"))
  let through := Q.d (.FuncDecD (Q.i "through") [] ps textT
    [Q.cl [f, xs] (call "f" [xs]) []] none [])
  let walk := Q.d (.FuncDecD (Q.i "walk") [] ps textT
    [Q.cl [f, xs] (call "f" [xs]) [empty],
     Q.cl [f, cons] (call "walk" [f, tail]) []] none [])
  let member (name consumer target : String) :=
    let result := if stateful then fresh else Q.e (.TextE (ByteText.ofString "done")) .TextT
    Q.d (.FuncDecD (Q.i name) [] [Q.pm (.ExpP (Q.t listT))] textT
      [Q.cl [xs] result [empty],
       Q.cl [cons] (call consumer [Q.ar (.DefA (Q.i target)), tail])
         (if stateful then [debug fresh] else [])] none [])
  return (if stateful then [Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] textT [])] else []) ++
    [through, walk, member "source" "through" "later", member "later" "walk" "source"]

open Lean Elab Command in
private def emitCycle (lib : String) (stateful : Bool) : CommandElabM Unit := do
  let fixture := cycleSpec stateful
  let ctx : Exp.Ctx := { env := Env.ofSpec lib fixture }
  let emit (source : String) : CommandElabM Unit := do
    let stx ← match Lean.Parser.runParserCategory (← getEnv) `command source with
      | .ok stx => pure stx
      | .error e => throwError "callback cycle parse:\n{source}\n{e}"
    elabCommand stx
  let mut members : List Std.Format := []
  for d in fixture do
    let source ← match d.it with
      | .BuiltinDecD i tps ps t _ =>
        pure (Funcs.builtinDecl ctx.env i.it (tps.map (·.it)) (ps.map (·.it)) t.it)
      | .FuncDecD i tps ps t cs ec _ =>
        pure (Funcs.funcDecl ctx (i.it != "through") false i.it
          (tps.map (·.it)) (ps.map (·.it)) t.it cs ec)
      | _ => throwError "unexpected cycle fixture"
    let source ← match source with
      | .ok f => pure f
      | .error e => throwError "callback cycle emission: {e}"
    match d.it with
    | .FuncDecD i .. =>
      if i.it == "source" || i.it == "later" then members := members ++ [source]
      else emit (Codegen.render source)
    | _ => emit (Codegen.render source)
  emit (Codegen.render (mutualBlock members))

namespace PureCycle
run_cmd emitCycle "P4SpecTecTest.StateCodegen.PureCycle" false
#guard match «$source» [1, 2, 3] with
  | some (.ok s) => s == ByteText.ofString "done" | _ => false
/-- info: 'P4SpecTecTest.StateCodegen.PureCycle.«$source»' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms «$source»
end PureCycle

namespace StateCycle
run_cmd emitCycle "P4SpecTecTest.StateCodegen.StateCycle" true
#guard match «$source» [1, 2, 3] 5 with
  | some (.ok s, state) => s == ByteText.ofString "FRESH__7" && state.counter == 8
  | _ => false
/-- info: 'P4SpecTecTest.StateCodegen.StateCycle.«$source»' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms «$source»
end StateCycle

open Lean Elab Command in
run_cmd do
  let emitCommand (source : String) : CommandElabM Unit := do
    let stx ← match Lean.Parser.runParserCategory (← getEnv) `command source with
      | .ok s => pure s
      | .error e => throwError "generated state source did not parse:\n{source}\n{e}"
    elabCommand stx
  emitCommand (Codegen.render (Funcs.externsClass env spec))
  emitCommand ("instance : Externs where\n" ++
    "  «$external» := fun s => some (.error .unmatch, s.next)\n" ++
    "  externalRel := fun s => some (.ok (ByteText.ofString \"extern\"), s.next)")
  for d in spec do
    let ctx : Exp.Ctx := { env, externs := ["external", "externalRel"] }
    let source ← match d.it with
      | .BuiltinDecD i tps ps t _ =>
        pure (Funcs.builtinDecl env i.it (tps.map (·.it)) (ps.map (·.it)) t.it)
      | .FuncDecD i tps ps t cs ec _ =>
        pure (Funcs.funcDecl ctx (i.it == "drain")
          (["externRetry", "externalRelation"].contains i.it) i.it
          (tps.map (·.it)) (ps.map (·.it)) t.it cs ec)
      | .RelD i nt ins gs eg _ =>
        pure (Rels.relDecl ctx false false i.it nt (ins.map (·.toNat)) gs eg)
      | .TableDecD i ps t rows _ =>
        pure (Funcs.tableDecl ctx false false i.it (ps.map (·.it)) t.it rows)
      | _ => continue
    match source with
    | .error err => throwError "state callable emission failed: {err}"
    | .ok f => emitCommand (Codegen.render f)

private def textResult (r : Option (Except Fail ByteText × FreshState))
    (text : String) (counter : Int) : Bool :=
  match r with
  | some (.ok v, s) => v == ByteText.ofString text && s.counter == counter
  | _ => false

#guard textResult («$allocate» 0) "FRESH__0" 1
#guard textResult («$externalRelation» 0) "extern" 1
#guard textResult («$allocate» (FreshState.ofInt 4611686018427387903))
  "FRESH__4611686018427387903" (-4611686018427387904)
#guard textResult («$debugFresh» 0) "FRESH__1" 2
#guard match «$debugError» 0 with | some (.error .err, s) => s.counter == 0 | _ => false
#guard textResult («$named» 0) "FRESH__0" 1
#guard textResult («$namedNested» 0) "FRESH__0" 1
#guard textResult («$shadowExtern» «$allocate» 0) "FRESH__0" 1
#guard textResult («$externRetry» 0) "FRESH__1" 2
#guard textResult («$negative» 0) "first:FRESH__1" 2
#guard textResult («$negativeSuccess» 0) "fallback:FRESH__1" 2
#guard textResult («shared».run 0) "FRESH__1" 2
#guard textResult («$drain» [1, 2] 0) "FRESH__2" 3
#guard match «$ordered» [1, 2, 3] 5 with
  | some (.ok xs, s) => xs == ["FRESH__5", "FRESH__6", "FRESH__7"].map ByteText.ofString &&
      s.counter == 8
  | _ => false
#guard textResult («$orderedPrem» [1, 2, 3] 5) "FRESH__8" 9
#guard match «$optionalOnce» 5 with
  | some (.ok (some x), s) => x == ByteText.ofString "FRESH__5" && s.counter == 6
  | _ => false
#guard textResult («$tableRetry» 0) "FRESH__1" 2
#guard match «$optionalBound» (some 7) 5 with
  | some (.ok (some x), s) => x == ByteText.ofString "FRESH__5" && s.counter == 6
  | _ => false
#guard match «$optionalBound» none 5 with
  | some (.ok none, s) => s.counter == 5
  | _ => false
#guard textResult («$optionalPrem» (some 7) 5) "FRESH__6" 7
#guard textResult («$optionalPrem» none 5) "FRESH__5" 6
#guard match «$optionalMixed» (some 7) none 5 with
  | some (.error .err, s) => s.counter == 5
  | _ => false
#guard textResult («$optionalMixed» (some 7) (some 8) 5) "FRESH__6" 7
#guard textResult («$optionalMixed» none none 5) "FRESH__5" 6
#guard match «$optionalExpr» (some 7) none 5 with
  | some (.error .err, s) => s.counter == 5 | _ => false
#guard match «$optionalExpr» none (some 7) 5 with
  | some (.error .err, s) => s.counter == 5 | _ => false
#guard match «$optionalExpr» (some 7) (some 8) 5 with
  | some (.ok (some 3), s) => s.counter == 5 | _ => false
#guard match «$optionalExpr» none none 5 with
  | some (.ok none, s) => s.counter == 5 | _ => false

namespace Pure

open Lean Elab Command in
run_cmd do
  let pureSpec := [optionalExpr,
    fn "allocate" [] (Q.e (.TextE (ByteText.ofString "pure")) .TextT),
    callback "through" "f", callback "forward" "through",
    fn "named" [] (call "forward" [Q.ar (.DefA (Q.i "allocate"))])]
  let pureEnv := Env.ofSpec "P4SpecTecTest.StateCodegen.Pure" pureSpec
  for d in pureSpec do
    let .FuncDecD i tps ps t cs ec _ := d.it | throwError "unexpected pure fixture"
    let source ← match Funcs.funcDecl { env := pureEnv } false false i.it
        (tps.map (·.it)) (ps.map (·.it)) t.it cs ec with
      | .ok f => pure (Codegen.render f)
      | .error err => throwError "pure callback emission: {err}"
    let stx ← match Lean.Parser.runParserCategory (← getEnv) `command source with
      | .ok s => pure s
      | .error err => throwError "pure callback parsing: {err}"
    elabCommand stx

#guard match «$named» with
  | some (.ok t) => t == ByteText.ofString "pure"
  | _ => false
#guard match «$optionalExpr» (some 7) none with | some (.error .err) => true | _ => false
#guard match «$optionalExpr» none (some 7) with | some (.error .err) => true | _ => false
#guard match «$optionalExpr» (some 7) (some 8) with | some (.ok (some 3)) => true | _ => false
#guard match «$optionalExpr» none none with | some (.ok none) => true | _ => false

end Pure

end P4SpecTecTest.StateCodegen
