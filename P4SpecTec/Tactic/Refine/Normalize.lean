import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Tactic.Simp
import Lean.Meta.Eqns
import P4SpecTec.Refine.Environment
import P4SpecTec.Refine.ValueShape

/-!
Fact-sensitive normalization for refinement tactics. The caller supplies its
SimpSet explicitly; this module does not select a forward or reverse rule preset.
Existing trace and phase state records the action performed by the caller.
-/

namespace P4SpecTec.Tactic

open Lean Elab Tactic Meta
open P4SpecTec.Refine
open P4SpecTec.Interp_al

/-- Tracing for the driver. -/
register_option refine_al.trace : Bool := {
  defValue := false
  descr := "trace the steps of refine_al"
}

/-- Print a trace message when tracing is on: straight to stderr, so that a
failing step does not discard it with its state. -/
def traceStep (msg : MessageData) : TacticM Unit := do
  if refine_al.trace.get (← getOptions) then
    IO.eprintln s!"[refine_al] {← msg.toString}"

/-- Accumulated time per phase, in milliseconds, for the trace. -/
initialize phaseTimes : IO.Ref (List (String × Nat)) ← IO.mkRef []

/-- The action in progress, for error reports. -/
initialize phaseNow : IO.Ref String ← IO.mkRef ""

/-- Note the action in progress. -/
def noteAction (s : String) : TacticM Unit := phaseNow.set s

/-- Run a phase, accumulating its time. -/
def timed {α : Type} (label : String) (act : TacticM α) : TacticM α := do
  let t0 ← IO.monoMsNow
  try act
  finally
    let t1 ← IO.monoMsNow
    phaseTimes.modify fun l =>
      match l.lookup label with
      | some n => (label, n + (t1 - t0)) :: l.filter (·.1 != label)
      | none => (label, t1 - t0) :: l

/-- The library namespace of the generated definition the goal is about,
from the name of the theorem being proved. -/
def libOf : TacticM Name := do
  let some decl := (← Term.getDeclName?) | throwError "refine_al: no declaration name"
  match decl with
  | .str (.str lib _) _ => pure lib
  | .str lib _ => pure lib
  | _ => throwError "refine_al: unexpected theorem name {decl}"

/-- The equation lemmas of a definition. A definition that matches on a
projection of a parameter gets conditional equations (`v.it = C … →
f v = …`), which `simp` cannot instantiate; for those the unfolding
equation is used instead, and the `match` computes once the value is a
literal. -/
def eqnsOf (n : Name) : MetaM (List Name) := do
  match ← getEqnsFor? n with
  | some eqns =>
    let mut conditional := false
    for e in eqns do
      let info ← getConstInfo e
      let hasHyp ← forallTelescopeReducing info.type fun xs _ => do
        xs.anyM fun x => do isProp (← inferType x)
      if hasHyp then conditional := true
    if conditional then pure [n] else pure eqns.toList
  | none => pure [n]

/-- The local hypotheses to rewrite with: equations whose left side is a
projection of a variable or a `canon` of a variable, and the guard. -/
def factHyps : TacticM (List Name) := do
  (← getMainGoal).withContext do
    let mut out := []
    let environment ← getEnv
    let directProjection (value : Expr) : Bool :=
      match value.consumeMData with
      | .proj _ _ receiver => receiver.consumeMData.isFVar
      | value => match value.getAppFn with
        | .const name _ => (environment.getProjectionFnInfo? name).isSome &&
            value.getAppArgs.back?.any (·.consumeMData.isFVar)
        | _ => false
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty := (← instantiateMVars decl.type).consumeMData
      -- a hypothesis of a case split decides its condition wherever it occurs
      if decl.userName.toString.startsWith "rf_c" then
        out := decl.userName :: out
        continue
      if let some (_, lhs, rhs) := ty.eq? then
        let lhs := lhs.consumeMData
        let isFact :=
          (lhs.isAppOfArity ``P4SpecTec.Refine.canon 1 &&
            let value := (lhs.getArg! 0).consumeMData
            value.isFVar || directProjection value) ||
          (lhs.isAppOfArity ``canon' 1 &&
            let payload := (lhs.getArg! 0).consumeMData
            payload.isFVar ||
              (payload.isAppOfArity ``P4SpecTec.Util.Source.info.it 4 &&
                (payload.getArg! 3).consumeMData.isFVar) ||
              (match payload with | .proj _ _ v => v.consumeMData.isFVar | _ => false)) ||
          (lhs.isAppOfArity ``canons 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canonMixfix 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canonMixfixes 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canonFields 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          -- an exposed extern payload's canonical JSON (`canon'_eq_extern`)
          (lhs.isAppOfArity ``Lean.Json.str 1 &&
            let text := (lhs.getArg! 0).consumeMData
            text.isAppOfArity ``Lean.Json.compress 1 && (text.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``P4SpecTec.Util.Source.info.it 4 &&
            (lhs.getArg! 3).consumeMData.isFVar) ||
          (match lhs with | .proj _ _ x => x.consumeMData.isFVar | _ => false) ||
          (lhs.isAppOf ``Interp.Config.guard) ||
          rhs.consumeMData.isConstOf ``Bool.true || rhs.consumeMData.isConstOf ``Bool.false ||
          (lhs.isAppOfArity ``Ctx.t.global 1) ||
          (lhs.isAppOfArity ``Ctx.local.fenv 1) ||
          (lhs.isAppOf ``Std.HashMap.get?)
        if isFact then out := decl.userName :: out
    pure out.reverse

/-- Global simplifier rules prepared for one tactic invocation, without local facts. -/
structure PreparedSimpRules where
  /-- The global lemma names used to prepare the context. -/
  lemmas : Array Name
  /-- The simproc names used to prepare the context. -/
  procs : Array Name
  /-- Lean's elaborated simplifier context and procedures. -/
  result : MkSimpContextResult

/-- The names of the whole simp set, once per tactic call. -/
structure SimpSet where
  /-- The lemmas and definitions. -/
  lemmas : Array Name
  /-- The simprocs and pre-order rewrite lemmas, both applied with `↓`. -/
  procs : Array Name
  /-- Optional global-rule preparation; never contains the changing local facts. -/
  prepared? : Option PreparedSimpRules := none

/-- Construct the explicit simp syntax used by both preparation and the fallback path. -/
def simpSyntax (lemmas procs : Array Name) (hyp? : Option Name := none) :
    TacticM (TSyntax `tactic) := do
  let args ← lemmas.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let procs ← procs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent n):ident)
  let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems (args ++ procs)
  match hyp? with
  | none => `(tactic| simp only [$all,*])
  | some h => `(tactic| simp only [$all,*] at $(mkIdent h):ident)

/-- Elaborate the fixed global rules once, before the tactic changes its local context.
The cached names are checked at each use, so extending a prepared set cannot omit rules. -/
def prepareSimpSet (s : SimpSet) : TacticM SimpSet := withMainContext do
  let result ← mkSimpContext (← simpSyntax s.lemmas s.procs) (eraseLocal := false)
  for (_, arg) in result.simpArgs do
    if let .addLetToUnfold _ := arg then
      throwError "refine_al: prepared rules must not contain local declarations"
    for thm in arg.simpTheorems do
      if thm.proof.hasFVar || thm.proof.hasMVar then
        throwError "refine_al: prepared rules must not contain local declarations"
  pure { s with prepared? := some { lemmas := s.lemmas, procs := s.procs, result } }

/-- Normalize with fixed global rules and freshly elaborated facts for this goal.
Only rule preparation is reused: simplification results and local assumptions are not cached. -/
def runNormalization (s : SimpSet) (facts : List Name) (hyp? : Option Name := none) :
    TacticM Unit := withMainContext do
  if let some prepared := s.prepared? then
    if prepared.lemmas == s.lemmas && prepared.procs == s.procs then
      let base := prepared.result
      let stx ← simpSyntax facts.toArray #[]
      let localRules ← elabSimpArgs stx.raw[4] base.ctx base.simprocs false .simp
      let r : MkSimpContextResult := { base with
        ctx := localRules.ctx, simprocs := localRules.simprocs
        simpArgs := base.simpArgs ++ localRules.simpArgs }
      let loc := match hyp? with
        | none => Location.targets #[] true
        | some h => Location.targets #[mkIdent h] false
      withSimpDiagnostics do
        let stats ← r.dischargeWrapper.with fun discharge? =>
          withLoopChecking r (simpLocation r.ctx r.simprocs discharge? loc)
        if tactic.simp.trace.get (← getOptions) then
          let traceStx ← simpSyntax (s.lemmas ++ facts.toArray) s.procs hyp?
          traceSimpCall traceStx stats.usedTheorems
        else if Linter.getLinterValue linter.unusedSimpArgs (← Linter.getLinterOptions) then
          withRef stx do warnUnusedSimpArgs r.simpArgs stats.usedTheorems
        pure stats.diag
      return
  evalTactic (← simpSyntax (s.lemmas ++ facts.toArray) s.procs hyp?)

/-- Run `simp only` with the set and the facts at the goal; `false` when
nothing changed. -/
def normalize (s : SimpSet) : TacticM Bool := timed "normalize" do
  if (← getGoals).isEmpty then return false
  let facts ← factHyps
  let saved ← saveState
  try
    runNormalization s facts
    pure true
  catch e =>
    saved.restore
    let msg := e.toMessageData
    unless (← msg.toString).startsWith "simp made no progress" do
      traceStep m!"normalize failed: {msg}"
    pure false

/-- Run the simp set at a hypothesis. -/
def normalizeAt (s : SimpSet) (h : Name) : TacticM Bool := timed "normalizeAt" do
  if (← getGoals).isEmpty then return false
  let facts := (← factHyps).filter (· != h)
  let saved ← saveState
  try
    runNormalization s facts h
    pure true
  catch e =>
    saved.restore
    let msg := e.toMessageData
    unless (← msg.toString).startsWith "simp made no progress" do
      traceStep m!"normalize at {h} failed: {msg}"
    pure false

/-- Normalise every fact (a hypothesis the driver rewrites with) at its
own statement: after a case split, `toValue` of a constructor computes
to a literal, which exposure needs. -/
def normalizeFacts (s : SimpSet) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  for h in ← factHyps do
    -- a fact may become `False` and close the goal
    if (← getGoals).isEmpty then return
    let _ ← normalizeAt s h

end P4SpecTec.Tactic
