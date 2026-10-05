import Lean.Elab.Command
import P4SpecTec.Codegen.Certificates.StateRunSound
import P4SpecTec.Codegen.Coverage.Check
import P4SpecTec.Tactic.StateRunSound
import P4SpecTec.Tactic.StateGroupSound
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
private def flag := Q.e (.VarE (Q.i "flag")) .BoolT
private def o := Q.e (.VarE (Q.i "o")) optNatT.it
private def optionalCall := Q.e (.CallE (Q.i "optional") [] []) optNatT.it
private def spec : Lang.Al.spec := [
  Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] textT []),
  -- An extern relation premise is a run equation of the `Externs` instance, and the
  -- relation, its attempts and its theorem all take that instance.
  Q.d (.ExternRelD (Q.i "externalRel") (Q.nt (.Arg textT)) [] []),
  Q.d (.RelD (Q.i "viaExtern") (Q.nt (.Arg textT)) []
    [Q.rg "g" ([], [], [])
      [Q.rp "reject" [Q.pr (.RulePr (Q.i "externalRel") (.Arg x) []), no] [x],
       Q.rp "accept" [Q.pr (.RulePr (Q.i "externalRel") (.Arg x) [])] [x]]] none []),
  -- A name bound to a constant stands for the constant: renaming the constant to the name
  -- would leave `flag` unbound and turn every `true` of the rule into it.
  Q.d (.RelD (Q.i "constantAlias") (Q.nt (.Arg textT)) []
    [Q.rg "g" ([], [], [Q.pr (.LetPr flag (Q.e (.BoolE true) .BoolT))])
      [Q.rp "reject" [Q.pr (.IfPr flag), save, no] [x],
       Q.rp "accept" [Q.pr (.IfPr flag)] [fresh]]] none []),
  Q.d (.FuncDecD (Q.i "optional") [] [] optNatT
    [Q.cl [] (Q.e (.OptE (some (Q.e (.NumE (.Nat 3)) natT.it))) optNatT.it) []] none []),
  -- A guard comparing with `none` applies a class method, not a projection of its operand:
  -- the operand is not destructured, and every branch of the later pattern is executed.
  Q.d (.RelD (Q.i "guardedOption") (Q.nt (.Arg natT)) []
    [Q.rg "g" ([], [], [])
      [Q.rp "p" [Q.pr (.LetPr o optionalCall),
        Q.pr (.IfPr (Q.e (.CmpE .EqOp .BoolT (Q.e (.OptE none) optNatT.it) o) .BoolT)),
        Q.pr (.LetPr (Q.e (.OptE (some n)) optNatT.it) optionalCall)] [n]]] none []),
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
  let externs := spec.filter fun d => match d.it with | .ExternRelD .. => true | _ => false
  let ctx : Exp.Ctx := { env, externs := externs.map (·.it.id.it) }
  let emit (f : Std.Format) : Lean.Elab.Command.CommandElabM Unit := do
    let source := Codegen.render f
    let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `command source with
      | .ok stx => pure stx
      | .error e => throwError "state proof source did not parse:\n{source}\n{e}"
    -- A proof elaborated in a task reports its failure outside this command's message
    -- log, and later commands would see the theorem as declared: elaborate here, and stop
    -- at the first error.
    Lean.Elab.Command.withScope
      (fun scope => { scope with opts := Lean.Elab.async.set scope.opts false })
      (Lean.Elab.Command.elabCommand stx)
    if (← get).messages.hasErrors then
      throwError "state proof declaration failed:\n{source}"
  emit (Funcs.externsClass env externs)
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
      let ext := (Exp.callsOfDef d).any ctx.externs.contains
      let formats : Except String (List Std.Format × Coverage.Claim) := do
        let executable ← Rels.relDecl ctx false ext i.it nt (ins.map (·.toNat)) gs eg
        let structural ← Codegen.StateProps.relInductives ctx ext i.it nt
          (ins.map (·.toNat)) gs eg
        let member := { ← Props.memberOf ctx d with externs := ext }
        let sound ← Codegen.StateProps.runSound ext member
        let audit := Props.audit (env.q (Codegen.StateProps.runSoundName member))
        -- each command is parsed on its own: the independent auxiliary predicates precede
        -- the mutual block of the relation and the predicates tied to it
        pure ([executable] ++ structural.attempts ++ structural.free ++
          [mutualBlock (structural.relation :: structural.tied), sound, audit],
          { name := env.q (Codegen.StateProps.runSoundName member), kind := "runSoundness"
            direction := "generatedSuccessToRelation"
            expectedType := Codegen.render (← Codegen.StateProps.runSoundType ext member) })
      match formats with
      | .error e => throwError e
      | .ok (fs, claim) =>
        for f in fs do emit f
        -- the coverage claim's type is the compiled theorem's, for every statement form:
        -- no output, one, several, and with the extern instance
        Lean.Elab.Command.liftTermElabM (Coverage.Check.checkClaim claim)
    | _ => pure ()

private def textResult' (r : Option (Except Fail ByteText × FreshState))
    (text : String) (counter : Int) : Bool :=
  match r with
  | some (.ok v, s) => v == ByteText.ofString text && s.counter == counter
  | _ => false

-- Every complete attempt but the last is a named definition, which later constructors'
-- rejected prefixes apply instead of restating its body.
private def attemptCount (name : String) : Option Nat := do
  let env := Env.ofSpec "P4SpecTecTest.StateProps" spec
  let d ← spec.find? fun d => d.it.id.it == name
  let .RelD i nt ins gs eg _ := d.it | none
  let found ← (Codegen.StateProps.relInductives { env } false i.it nt (ins.map (·.toNat))
    gs eg).toOption
  let text := Codegen.render found.relation
  guard ((text.splitOn "do").length == 1)
  pure found.attempts.length
#guard attemptCount "simple" == some 0
#guard attemptCount "retry" == some 1
-- The definition runs as the first alternative of the executable relation does.
#guard match StateEval.run retry.«@attempt0» 4 with
  | some (.error .unmatch, s) => s == 5
  | _ => false

-- A class method is not a projection of its operand: `x` stays a variable in one goal.
example (x : Option Nat) (h : (none == x) = true) : (none == x) = true := by
  run_tac do
    P4SpecTec.Tactic.projCases
    unless (← Lean.Elab.Tactic.getGoals).length == 1 do
      throwError "a class-method operand was destructured into several goals"
    (← Lean.Elab.Tactic.getMainGoal).withContext do
      unless ((← Lean.getLCtx).findFromUserName? `x).isSome do
        throwError "a class-method operand was destructured"
  exact h
-- A structure projection of a variable still destructures it, so the projection reduces.
example (p : Nat × Nat) (h : p.1 = 3) : p.1 = 3 := by
  run_tac do
    P4SpecTec.Tactic.projCases
    (← Lean.Elab.Tactic.getMainGoal).withContext do
      if ((← Lean.getLCtx).findFromUserName? `p).isSome then
        throwError "a projected variable was not destructured"
  assumption

-- Shared emitter rules that full P4 first exercised.
#guard Names.ruleNames [("g", "a"), ("g", "a"), ("", ""), ("g", "g"), ("", "b"), ("g", "a")] ==
  ["«g/a»", "«g/a_2»", "rule2", "g", "b", "«g/a_3»"]
-- A name inside another variable's quoted name is not an occurrence; the whole quoted
-- token, a projection base and a plain occurrence are; a namespace component is not.
#guard Codegen.render (Props.substText "x" (Std.Format.text "Y")
    "x «a<x>?» «x» f x.1 a.x «x*» (x)") == "Y «a<x>?» «Y» f Y.1 a.x «x*» (Y)"
#guard Props.mentions "x" (Std.Format.text "«a<x>?»") == false
#guard Props.mentions "x" (Std.Format.text "g «a<x>?» x")
#guard textResult' (constantAlias.run 0) "FRESH__1" 2
#guard match guardedOption.run 7 with
  | some (.error .unmatch, s) => s == 7
  | _ => false

-- An auxiliary predicate joins the mutual block only when it mentions a relation of the
-- recursion group, directly or through a nested predicate; independent ones are declared
-- ahead of it, nested first.
private def auxiliaries (name : String) (group : List String) : Option (List String × Nat) := do
  let env := Env.ofSpec "P4SpecTecTest.StateProps" spec
  let d ← spec.find? fun d => d.it.id.it == name
  let .RelD i nt ins gs eg _ := d.it | none
  let found ← (Codegen.StateProps.relInductives { env } false i.it nt (ins.map (·.toNat))
    gs eg group).toOption
  pure (found.free.map fun f => ((Codegen.render f).splitOn " :").head!, found.tied.length)
#guard auxiliaries "simple" ["simple"] == some ([], 0)
#guard auxiliaries "mapped" ["mapped"] == some (["inductive mapped.«@path0».«@iter0»"], 0)
#guard auxiliaries "nestedMapped" ["nestedMapped"] == some
  (["inductive nestedMapped.«@path0».«@iter1»", "inductive nestedMapped.«@path0».«@iter0»"], 0)
#guard auxiliaries "optionalCalls" ["optionalCalls"] == some
  (["inductive optionalCalls.«@path0».«@optional0»"], 0)
-- Were `tagged` in the same recursion group, the predicates calling it would be tied,
-- the outer one through the nested one.
#guard auxiliaries "mapped" ["mapped", "tagged"] == some ([], 1)
#guard auxiliaries "nestedMapped" ["nestedMapped", "tagged"] == some ([], 2)
#guard auxiliaries "jointCaptured" ["jointCaptured", "tagged"] == some
  (["inductive jointCaptured.«@path0».«@iter0»"], 0)

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

/-! ## Recursive groups

A group is proved by one induction over its least fixed point. The fixtures are a relation
calling itself, with a rejected attempt that recurses and consumes state; two relations
calling each other; a function inside a group; an iterated and a negative premise over
relations of the group; a group that takes the extern instance; and a relation of seven
inputs, for which Lean cannot derive `partial_correctness` (instance resolution fails on
the long function type), so that the order instances must be read off the fixed point. -/

private def inputList := Q.e (.VarE (Q.i "l")) listNatT.it
private def inputTail := Q.e (.VarE (Q.i "rest")) listNatT.it
private def collected := Q.e (.VarE (Q.i "collected")) listTextT.it
private def ignored := Q.e (.VarE (Q.i "ignored")) listTextT.it
private def isNil := Q.pr (.IfPr (Q.e (.MatchE inputList (.ListP .Nil)) .BoolT))
private def isCons := Q.pr (.IfPr (Q.e (.MatchE inputList (.ListP .Cons)) .BoolT))
private def uncons := Q.pr (.LetPr (Q.e (.ConsE n inputTail) listNatT.it) inputList)
private def onNil : rulematch := ([], [inputList], [isNil])
private def onCons : rulematch := ([], [inputList], [isCons, uncons])
private def listCall (name : String) (input output : exp) :=
  Q.pr (.RulePr (Q.i name) (.Seq [.Arg input, .Arg output]) [0])
private def noTexts := Q.e (.ListE []) listTextT.it
private def consText := Q.e (.ConsE x collected) listTextT.it
private def listRelation (name : String) (groups : List Lang.Al.rulegroup) : Lang.Al.def :=
  Q.d (.RelD (Q.i name) (Q.nt (.Seq [.Arg listNatT, .Arg listTextT])) [0] groups none [])
private def zero := Q.e (.NumE (.Nat 0)) natT.it
private def isZero := Q.pr (.IfPr (Q.e (.CmpE .EqOp .BoolT n zero) .BoolT))
private def positive := Q.pr (.IfPr (Q.e (.CmpE .LtOp .NatT zero n) .BoolT))
private def taggedCount (input : exp) :=
  Q.pr (.RulePr (Q.i "count") (.Seq [.Arg tag, .Arg input, .Arg collected]) [0, 1])

private def wideInputs : List exp :=
  (["a", "b", "c", "d", "e", "f"].map fun name => Q.e (.VarE (Q.i name)) natT.it) ++ [inputList]
private def wideCall :=
  Q.pr (.RulePr (Q.i "wide")
    (.Seq ((wideInputs.dropLast ++ [inputTail, collected]).map .Arg)) [0, 1, 2, 3, 4, 5, 6])

private def recursiveSpec : Lang.Al.spec := [
  Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] textT []),
  Q.d (.ExternRelD (Q.i "externalRel") (Q.nt (.Arg textT)) [] []),
  Q.d (.RelD (Q.i "count") (Q.nt (.Seq [.Arg natT, .Arg listNatT, .Arg listTextT])) [0, 1]
    [Q.rg "retry" ([], [tag, inputList], [isCons, uncons])
      [Q.rp "reject" [save, taggedCount inputTail, no] [collected]],
     Q.rg "nil" ([], [tag, inputList], [isNil]) [Q.rp "stop" [] [noTexts]],
     Q.rg "cons" ([], [tag, inputList], [isCons, uncons])
      [Q.rp "step" [save, taggedCount inputTail] [consText]]] none []),
  listRelation "ping" [
    Q.rg "nil" onNil [Q.rp "stop" [] [noTexts]],
    Q.rg "cons" onCons [Q.rp "step" [save, listCall "pong" inputTail collected] [consText]]],
  listRelation "pong" [
    Q.rg "retry" onCons
      [Q.rp "reject" [listCall "ping" inputTail collected, save, no] [collected]],
    Q.rg "nil" onNil [Q.rp "stop" [save] [Q.e (.ListE [x]) listTextT.it]],
    Q.rg "cons" onCons [Q.rp "step" [listCall "ping" inputTail collected] [collected]]],
  listRelation "viaFunction" [
    Q.rg "nil" onNil [Q.rp "stop" [] [noTexts]],
    Q.rg "cons" onCons [Q.rp "step" [save, Q.pr (.LetPr collected
      (Q.e (.CallE (Q.i "tailOf") [] [Q.ar (.ExpA inputTail)]) listTextT.it))] [consText]]],
  Q.d (.FuncDecD (Q.i "tailOf") [] [Q.pm (.ExpP listNatT)] listTextT
    [Q.cl [Q.ar (.ExpA inputList)] collected [listCall "viaFunction" inputList collected]]
    none []),
  Q.d (.RelD (Q.i "each") (Q.nt (.Seq [.Arg listNatT, .Arg listTextT])) [0]
    [Q.rg "g" ([], [ns], []) [Q.rp "p" [Q.pr (.IterPr
      (Q.pr (.RulePr (Q.i "item") (.Seq [.Arg n, .Arg x]) [0]))
      (.mk .List [Q.v "n" natT.it] [Q.v "x" .TextT]))] [xs]]] none []),
  Q.d (.RelD (Q.i "item") (Q.nt (.Seq [.Arg natT, .Arg textT])) [0]
    [Q.rg "g" ([], [n], [])
      [Q.rp "absent" [isZero, Q.pr (.IfNotHoldPr (Q.i "never") (.Arg n)), save] [x],
       Q.rp "deep" [listCall "each" (Q.e (.ListE []) listNatT.it) ignored, save] [x]]]
    none []),
  Q.d (.RelD (Q.i "never") (Q.nt (.Arg natT)) [0]
    [Q.rg "g" ([], [n], [])
      [Q.rp "p" [positive, Q.pr (.RulePr (Q.i "item") (.Seq [.Arg n, .Arg x]) [0])] []]]
    none []),
  listRelation "echo" [
    Q.rg "nil" onNil
      [Q.rp "stop" [Q.pr (.RulePr (Q.i "externalRel") (.Arg x) [])]
        [Q.e (.ListE [x]) listTextT.it]],
    Q.rg "cons" onCons [Q.rp "step" [listCall "echo" inputTail collected] [collected]]],
  Q.d (.RelD (Q.i "wide")
    (Q.nt (.Seq ((List.replicate 6 (.Arg natT)) ++ [.Arg listNatT, .Arg listTextT])))
    [0, 1, 2, 3, 4, 5, 6]
    [Q.rg "nil" ([], wideInputs, [isNil]) [Q.rp "stop" [] [noTexts]],
     Q.rg "cons" ([], wideInputs, [isCons, uncons])
      [Q.rp "step" [save, wideCall] [consText]]] none [])]

private def recursiveGroups : List (List String) :=
  [["count"], ["ping", "pong"], ["viaFunction", "tailOf"], ["each", "item", "never"], ["echo"],
   ["wide"]]

/-- The declarations of a recursive group in elaboration order, and its claims. -/
private def recursiveGroup (group : List String) :
    Except String (List Std.Format × List Coverage.Claim) := do
  let env := Env.ofSpec "P4SpecTecTest.StateProps" recursiveSpec
  let externs := recursiveSpec.filter fun d => match d.it with | .ExternRelD .. => true | _ => false
  let ctx : Exp.Ctx := { env, externs := externs.map (·.it.id.it) }
  let defs := recursiveSpec.filter fun d => group.contains d.it.id.it
  let ext := defs.any fun d => (Exp.callsOfDef d).any ctx.externs.contains
  let relations := (defs.filter fun d => match d.it with | .RelD .. => true | _ => false).map
    (·.it.id.it)
  let executable ← defs.mapM fun d => match d.it with
    | .RelD i nt ins gs eg _ => Rels.relDecl ctx true ext i.it nt (ins.map (·.toNat)) gs eg
    | .FuncDecD i ts ps t cs ec _ =>
      Funcs.funcDecl ctx true ext i.it (ts.map (·.it)) (ps.map (·.it)) t.it cs ec
    | _ => throw "not a group member"
  let structural ← defs.filterMapM fun d => match d.it with
    | .RelD i nt ins gs eg _ => do
      pure (some (← Codegen.StateProps.relInductives ctx ext i.it nt (ins.map (·.toNat)) gs eg
        relations))
    | _ => pure none
  let members ← defs.mapM fun d => do pure { ← Props.memberOf ctx d with externs := ext }
  let consumers := (group.flatMap (Funcs.monotonicityConsumers env)).eraseDups
  let sound ← Codegen.StateProps.groupRunSound ext env.q consumers members
  let claims ← (members.filter (·.isRel)).mapM fun member => do
    pure ({ name := env.q (Codegen.StateProps.runSoundName member), kind := "runSoundness"
            direction := "generatedSuccessToRelation"
            expectedType := Codegen.render (← Codegen.StateProps.runSoundType ext member) } :
      Coverage.Claim)
  pure ([mutualBlock executable] ++ structural.flatMap (·.attempts) ++
    structural.flatMap (·.free) ++
    [mutualBlock (structural.map (·.relation) ++ structural.flatMap (·.tied))] ++ sound, claims)

run_cmd do
  for group in recursiveGroups do
    match recursiveGroup group with
    | .error e => throwError e
    | .ok (declarations, claims) =>
      for declaration in declarations do
        let source := Codegen.render declaration
        let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `command source with
          | .ok stx => pure stx
          | .error e => throwError "recursive group source did not parse:\n{source}\n{e}"
        -- As above: elaborate here, and stop at the first error.
        Lean.Elab.Command.withScope
          (fun scope => { scope with opts := Lean.Elab.async.set scope.opts false })
          (Lean.Elab.Command.elabCommand stx)
        if (← get).messages.hasErrors then
          throwError "recursive group declaration failed:\n{source}"
      for claim in claims do
        Lean.Elab.Command.liftTermElabM (Coverage.Check.checkClaim claim)

-- The joint statement names every definition of the group, the function included, and is
-- the conjunction of the relations' theorems alone.
#guard match recursiveGroup ["viaFunction", "tailOf"] with
  | .ok (declarations, claims) =>
    let text := "\n".intercalate (declarations.map Codegen.render)
    text.contains ("state_run_sound_group [P4SpecTecTest.StateProps.viaFunction.run, " ++
      "P4SpecTecTest.StateProps.«$tailOf»] []") &&
    claims.map (·.name) == ["P4SpecTecTest.StateProps.viaFunction.run_sound"]
  | .error _ => false
#guard match recursiveGroup ["each", "item", "never"] with
  | .ok (_, claims) => claims.length == 3
  | .error _ => false

/-- info: 'P4SpecTecTest.StateProps.count.run_sound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms count.run_sound

/-- info: 'P4SpecTecTest.StateProps.pong.run_sound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms pong.run_sound

/-- info: 'P4SpecTecTest.StateProps.never.run_sound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms never.run_sound

/-- info: 'P4SpecTecTest.StateProps.echo.run_sound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms echo.run_sound

/-- info: 'P4SpecTecTest.StateProps.wide.run_sound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms wide.run_sound

-- A statement the definitions do not satisfy is rejected, not proved: here `count` is
-- claimed to return no texts for every input.
run_cmd do
  let source := "theorem wrongCount (p0 : Nat) (p1 : List Nat) (o : List P4SpecTec.ByteText)
      (s t : P4SpecTec.Prelude.FreshState) :
      P4SpecTecTest.StateProps.count.run p0 p1 s = some (.ok o, t) →
      P4SpecTecTest.StateProps.count p0 p1 [] s t := by
    state_run_sound_group [P4SpecTecTest.StateProps.count.run] []"
  let stx ← match Lean.Parser.runParserCategory (← Lean.getEnv) `command source with
    | .ok stx => pure stx
    | .error e => throwError "wrong statement did not parse: {e}"
  let saved ← get
  Lean.Elab.Command.withScope
    (fun scope => { scope with opts := Lean.Elab.async.set scope.opts false })
    (Lean.Elab.Command.elabCommand stx)
  let rejected := (← get).messages.hasErrors
  set saved
  unless rejected do throwError "a false group statement was accepted"

private def texts (r : Option (Except Fail (List ByteText) × FreshState))
    (expected : List String) (state : Int) : Bool :=
  match r with
  | some (.ok found, s) => found == expected.map ByteText.ofString && s == FreshState.ofInt state
  | _ => false

-- The rejected attempt of `count` recurses first: every level consumes state twice.
#guard texts (count.run 7 [1, 2] 0) ["FRESH__3", "FRESH__5"] 6
#guard texts (ping.run [1, 2, 3] 0) ["FRESH__0", "FRESH__4", "FRESH__5"] 6
#guard texts (viaFunction.run [1, 2] 0) ["FRESH__0", "FRESH__1"] 2
#guard texts (each.run [0, 5] 0) ["FRESH__0", "FRESH__1"] 2
#guard texts (wide.run 1 2 3 4 5 6 [7, 8] 0) ["FRESH__0", "FRESH__1"] 2

end P4SpecTecTest.StateProps
