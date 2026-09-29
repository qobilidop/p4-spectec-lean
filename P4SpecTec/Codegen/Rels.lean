import P4SpecTec.Codegen.Funcs
import P4SpecTec.Codegen.Attempt

/-!
Relations, executable encoding: `RelD` to `R.run`, a function from the
inputs the hint names to `Option (Except Fail _)` of the outputs, trying
complete rule-path attempts in order, the `else` group last. Each attempt repeats
its group's input match and shared premises, as `invoke_defined_rel` does in
sequential mode: the reference flattens the paths of all groups into one ordered
sequence of alternatives, and the generated code keeps that structure.
-/

namespace P4SpecTec.Codegen.Rels

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types
open P4SpecTec.Codegen.Exp
open P4SpecTec.Codegen.Funcs

/-- Compile the exact statements and outputs of a complete source attempt. -/
def attemptBlock (attempt : Attempt.RelAttempt) : CgM (List Stmt × List Term) := do
  let (_, ins, shared) := attempt.match_
  let (outs, stmts) ← subBlock do
    for (e, n) in ins.zip (paramNames ins.length) do assign e (.atom n)
    for p in shared ++ attempt.prems do compilePrem p
    attempt.outs.mapM compileExp
  pure (stmts, outs)

/-- Render the same complete block consumed by structural proof generation. -/
def attemptTerm (attempt : Attempt.RelAttempt) : CgM Term := do
  let (stmts, outs) ← attemptBlock attempt
  pure (doOfWith (← read).env.mode stmts (.tuple outs))

/-- A relation's run function. -/
def relDecl (ctx : Ctx) (recursive externs : Bool) (id : String) (nottyp : nottyp)
    (inputs : List Nat) (groups : List Lang.Al.rulegroup) (elsegroup : Option Lang.Al.elsegroup) :
    Except String Format := do
  let args := (Mixfix.args nottyp.it).map (·.it)
  let (ins, outs) := splitArgs inputs args
  let alts ← Exp.run ctx do
    pure (alternatives (← (Attempt.ofRelation groups elsegroup).mapM attemptTerm))
  let mode := ctx.env.mode
  let header := Term.sig (Names.relName id ++ ".run")
    (binders ctx.env [] ins externs ++ stateBinder mode)
    (retTypeWith mode (typTerm.prod (outs.map (typTerm ctx.env []))).arg)
  pure (header ++ Format.nest 2 (Format.line ++
    runBodyWith mode recursive alts (if recursive then monotonicityConsumers ctx.env id else [])))

end P4SpecTec.Codegen.Rels
