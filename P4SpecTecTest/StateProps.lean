import Lean.Elab.Command
import P4SpecTec.Codegen.StateProps
import P4SpecTec.Tactic.StateRunSound
import P4SpecTec.Tactic.Audit
import P4SpecTec.Refine.Quote
import P4SpecTec.Prelude

/-! Elaborate actual state Prop emission and prove its exact run-soundness contracts. -/

namespace P4SpecTecTest.StateProps

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Codegen
open P4SpecTec.Lang.Il P4SpecTec.Lang.Al

private def textT := Q.t .TextT
private def fresh := Q.e (.CallE (Q.i "fresh_typeId") [] []) .TextT
private def x := Q.e (.VarE (Q.i "x")) .TextT
private def save := Q.pr (.LetPr x fresh)
private def no := Q.pr (.IfPr (Q.e (.BoolE false) .BoolT))
private def natT := Q.t (.NumT .NatT)
private def optNatT := Q.t (.IterT natT .Opt)
private def n := Q.e (.VarE (Q.i "n")) natT.it
private def m := Q.e (.VarE (Q.i "m")) natT.it
private def tag := Q.e (.VarE (Q.i "tag")) natT.it
private def listNatT := Q.t (.IterT natT .List)
private def listTextT := Q.t (.IterT textT .List)
private def ns := Q.e (.IterE n (.mk .List [Q.v "n" natT.it])) listNatT.it
private def xs := Q.e (.IterE x (.mk .List [Q.v "x" .TextT])) listTextT.it
private def ms := Q.e (.IterE m (.mk .List [Q.v "m" natT.it])) listNatT.it
private def y := Q.e (.VarE (Q.i "y")) natT.it
private def ys := Q.e (.IterE y (.mk .List [Q.v "y" natT.it])) listNatT.it
private def matrixNatT := Q.t (.IterT listNatT .List)
private def matrixTextT := Q.t (.IterT listTextT .List)
private def nss := Q.e (.IterE ns (.mk .List [Q.v "n" natT.it [.List]])) matrixNatT.it
private def xss := Q.e (.IterE xs (.mk .List [Q.v "x" .TextT [.List]])) matrixTextT.it
private def optTextT := Q.t (.IterT textT .Opt)
private def optN := Q.e (.IterE n (.mk .Opt [Q.v "n" natT.it])) optNatT.it
private def optM := Q.e (.IterE m (.mk .Opt [Q.v "m" natT.it])) optNatT.it
private def optX := Q.e (.IterE x (.mk .Opt [Q.v "x" .TextT])) optTextT.it
private def spec : Lang.Al.spec := [
  Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] textT []),
  Q.d (.FuncDecD (Q.i "optional") [] [] optNatT
    [Q.cl [] (Q.e (.OptE (some (Q.e (.NumE (.Nat 3)) natT.it))) optNatT.it) []] none []),
  -- Both attempts start their temporary numbering at tmp_0, at different types.
  -- The selected some-pattern must never rewrite the earlier fresh call's binder.
  Q.d (.RelD (Q.i "capture") (Q.nt (.Arg natT)) []
    [Q.rg "first" ([], [], [])
      [Q.rp "reject" [save, no] [Q.e (.NumE (.Nat 0)) natT.it]],
     Q.rg "second" ([], [], [])
      [Q.rp "accept" [Q.pr (.LetPr (Q.e (.OptE (some n)) optNatT.it)
        (Q.e (.CallE (Q.i "optional") [] []) optNatT.it))] [n]]] none []),
  -- Different input aliases in the selected path must remain outside the earlier
  -- attempt's lexical scope, even when its local names are the same in reverse.
  Q.d (.RelD (Q.i "scopedInputs") (Q.nt (.Seq [.Arg natT, .Arg natT, .Arg natT])) [0, 1]
    [Q.rg "first" ([], [n, m], [])
      [Q.rp "p" [Q.pr (.DebugPr fresh),
        Q.pr (.IfPr (Q.e (.CmpE .LtOp .NatT n m) .BoolT))] [n]],
     Q.rg "second" ([], [m, n], []) [Q.rp "p" [] [n]]] none []),
  Q.d (.RelD (Q.i "simple") (Q.nt (.Arg textT)) []
    [Q.rg "g" ([], [], []) [Q.rp "p" [] [fresh]]] none []),
  Q.d (.RelD (Q.i "retry") (Q.nt (.Arg textT)) []
    [Q.rg "g" ([], [], [save]) [Q.rp "reject" [no] [x], Q.rp "accept" [] [x]]] none []),
  Q.d (.RelD (Q.i "calls") (Q.nt (.Arg textT)) []
    [Q.rg "g" ([], [], [])
      [Q.rp "p" [Q.pr (.RulePr (Q.i "simple") (.Arg x) [])] [x]]] none []),
  Q.d (.RelD (Q.i "empty") (Q.nt (.Seq [])) []
    [Q.rg "g" ([], [], []) [Q.rp "p" [save, no] []]] none []),
  Q.d (.RelD (Q.i "negative") (Q.nt (.Arg textT)) []
    [Q.rg "g" ([], [], [])
      [Q.rp "p" [Q.pr (.IfNotHoldPr (Q.i "empty") (.Seq []))] [fresh]]] none []),
  Q.d (.RelD (Q.i "tagged") (Q.nt (.Seq [.Arg natT, .Arg textT])) [0]
    [Q.rg "g" ([], [tag], []) [Q.rp "p" [] [fresh]]] none []),
  Q.d (.RelD (Q.i "paired") (Q.nt (.Seq [.Arg natT, .Arg textT, .Arg natT])) [0]
    [Q.rg "g" ([], [tag], []) [Q.rp "p" [] [fresh, tag]]] none []),
  -- The computed capture uses pattern-bound n while the inner iterator shadows n.
  -- Two input lists and two collected outputs exercise the zip/projection path.
  Q.d (.RelD (Q.i "jointCaptured")
    (Q.nt (.Seq [.Arg optNatT, .Arg listNatT, .Arg listNatT,
      .Arg listTextT, .Arg listNatT])) [0, 1, 2]
    [Q.rg "g" ([], [Q.e (.OptE (some n)) optNatT.it, ns, ms], [Q.pr (.LetPr tag
      (Q.e (.BinE .AddOp .NatT n (Q.e (.NumE (.Nat 1)) natT.it)) natT.it))])
      [Q.rp "p" [Q.pr (.IterPr
        (Q.pr (.RulePr (Q.i "paired") (.Seq [.Arg tag, .Arg x, .Arg y]) [0]))
        (.mk .List [Q.v "n" natT.it, Q.v "m" natT.it]
          [Q.v "x" .TextT, Q.v "y" natT.it]))] [xs, ys]]] none []),
  Q.d (.RelD (Q.i "nestedMapped")
    (Q.nt (.Seq [.Arg natT, .Arg matrixNatT, .Arg matrixTextT])) [0, 1]
    [Q.rg "g" ([], [tag, nss], []) [Q.rp "p" [Q.pr (.IterPr
      (Q.pr (.IterPr
        (Q.pr (.RulePr (Q.i "tagged") (.Seq [.Arg tag, .Arg x]) [0]))
        (.mk .List [Q.v "n" natT.it] [Q.v "x" .TextT])))
      (.mk .List [Q.v "n" natT.it [.List]] [Q.v "x" .TextT [.List]]))] [xss]]] none []),
  Q.d (.RelD (Q.i "mapped")
    (Q.nt (.Seq [.Arg natT, .Arg listNatT, .Arg listTextT])) [0, 1]
    [Q.rg "g" ([], [tag, ns], [])
      [Q.rp "p" [Q.pr (.IterPr
        (Q.pr (.RulePr (Q.i "tagged") (.Seq [.Arg tag, .Arg x]) [0]))
        (.mk .List [Q.v "n" natT.it] [Q.v "x" .TextT]))] [xs]]] none []),
  Q.d (.RelD (Q.i "optionalCalls")
    (Q.nt (.Seq [.Arg natT, .Arg optNatT, .Arg optNatT, .Arg optTextT])) [0, 1, 2]
    [Q.rg "g" ([], [tag, optN, optM], [Q.pr (.DebugPr fresh)])
      [Q.rp "p" [Q.pr (.IterPr
        (Q.pr (.RulePr (Q.i "tagged") (.Seq [.Arg tag, .Arg x]) [0]))
        (.mk .Opt [Q.v "n" natT.it, Q.v "m" natT.it] [Q.v "x" .TextT]))]
        [optX]]] none [])]

run_cmd do
  let env := Env.ofSpec "P4SpecTecTest.StateProps" spec
  let ctx : Exp.Ctx := { env }
  let emit (f : Std.Format) : Lean.Elab.Command.CommandElabM Unit := do
    let source := Codegen.render f
    let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `command source with
      | .ok stx => pure stx
      | .error e => throwError "state proof source did not parse:\n{source}\n{e}"
    Lean.Elab.Command.elabCommand stx
  for d in spec do
    match d.it with
    | .BuiltinDecD i ts ps t _ =>
      match Funcs.builtinDecl env i.it (ts.map (·.it)) (ps.map (·.it)) t.it with
      | .ok f => emit f
      | .error e => throwError e
    | .FuncDecD i ts ps t cs ec _ =>
      match Funcs.funcDecl ctx false false i.it (ts.map (·.it)) (ps.map (·.it)) t.it cs ec with
      | .ok f => emit f
      | .error e => throwError e
    | .RelD i nt ins gs eg _ =>
      let formats : Except String (List Std.Format) := do
        let executable ← Rels.relDecl ctx false false i.it nt (ins.map (·.toNat)) gs eg
        let structural ← Codegen.StateProps.relInductives ctx false i.it nt
          (ins.map (·.toNat)) gs eg
        let sound ← Codegen.StateProps.runSound false (← Props.memberOf ctx d)
        let audit := Props.audit (env.q (Names.relName i.it ++ ".run_sound"))
        pure [executable, mutualBlock structural, sound, audit]
      match formats with
      | .error e => throwError e
      | .ok fs => for f in fs do emit f
    | _ => pure ()

private def textResult (r : Option (Except Fail ByteText × FreshState))
    (text : String) (counter : Int) : Bool :=
  match r with
  | some (.ok v, s) => v == ByteText.ofString text && s.counter == counter
  | _ => false

#guard textResult (simple.run 0) "FRESH__0" 1
#guard textResult (retry.run 0) "FRESH__1" 2
#guard textResult (calls.run 7) "FRESH__7" 8
#guard match empty.run 3 with
  | some (.error .unmatch, s) => s == 4
  | _ => false
#guard textResult (negative.run 3) "FRESH__4" 5

-- A caller supplies the next session state; the relation never resets it.
#guard textResult (retry.run 19) "FRESH__20" 21
#guard match capture.run 5 with
  | some (.ok x, s) => x == 3 && s == 6
  | _ => false
#guard match scopedInputs.run 5 3 7 with
  | some (.ok x, s) => x == 3 && s == 8
  | _ => false
#guard match scopedInputs.run 2 3 7 with
  | some (.ok x, s) => x == 2 && s == 8
  | _ => false
#guard match mapped.run 99 [] 6 with
  | some (.ok xs, s) => xs.isEmpty && s == 6
  | _ => false
#guard match mapped.run 99 [3, 5] 6 with
  | some (.ok xs, s) => xs == ["FRESH__6", "FRESH__7"].map ByteText.ofString && s == 8
  | _ => false
#guard match optionalCalls.run 99 none none 4 with
  | some (.ok none, s) => s == 5
  | _ => false
#guard match optionalCalls.run 99 (some 2) (some 3) 4 with
  | some (.ok (some x), s) => x == ByteText.ofString "FRESH__5" && s == 6
  | _ => false
#guard match optionalCalls.run 99 (some 2) none 4 with
  | some (.error .err, s) => s == 5
  | _ => false
#guard match jointCaptured.run (some 10) [2, 3] [7, 8] 4 with
  | some (.ok (xs, ys), s) =>
    xs == ["FRESH__4", "FRESH__5"].map ByteText.ofString && ys == [11, 11] && s == 6
  | _ => false
#guard match nestedMapped.run 99 [[2, 3], [], [7]] 4 with
  | some (.ok xss, s) =>
    xss == [["FRESH__4", "FRESH__5"], [], ["FRESH__6"]].map
      (List.map ByteText.ofString) && s == 7
  | _ => false

-- The extension's false/unfinished/throwing paths must all restore assignments
-- and goal lists before the standard constructor search resumes.
theorem extensionRollback : True ∧ True := by
  run_tac do
    let before ← Lean.Elab.Tactic.getGoals
    let untouched : Lean.Elab.Tactic.TacticM Unit := do
      unless (← Lean.Elab.Tactic.getGoals) == before do
        throwError "extension changed goals after rollback"
      for g in before do
        if ← g.isAssigned then throwError "extension retained a rolled-back assignment"
    for kind in [0, 1, 2] do
      let closed ← P4SpecTec.Tactic.tryCloseExtension do
        Lean.Elab.Tactic.evalTactic (← `(tactic| constructor))
        if kind == 2 then throwError "deliberate extension failure"
        pure (kind == 1)
      if closed then throwError "unfinished extension counted as success"
      untouched
  constructor <;> trivial

/-- info: 'P4SpecTecTest.StateProps.extensionRollback' does not depend on any axioms -/
#guard_msgs in #print axioms extensionRollback

-- The emitted positive premise is structural, not just a callee run equation.
example (x : ByteText) (s t : FreshState) (h : simple x s t) : calls x s t :=
  calls.«g/p» (.nil _) h

end P4SpecTecTest.StateProps
