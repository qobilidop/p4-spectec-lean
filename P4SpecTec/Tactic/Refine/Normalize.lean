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
          (lhs.isAppOfArity ``P4SpecTec.Refine.canon 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canons 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canonMixfix 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canonMixfixes 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
          (lhs.isAppOfArity ``canonFields 1 && (lhs.getArg! 0).consumeMData.isFVar) ||
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

/-- The names of the whole simp set, once per tactic call. -/
structure SimpSet where
  /-- The lemmas and definitions. -/
  lemmas : Array Name
  /-- The simprocs. -/
  procs : Array Name

/-- Run `simp only` with the set and the facts at the goal; `false` when
nothing changed. -/
def normalize (s : SimpSet) : TacticM Bool := timed "normalize" do
  if (← getGoals).isEmpty then return false
  let facts ← factHyps
  let names := s.lemmas ++ facts.toArray
  let args ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let procs ← s.procs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent n):ident)
  let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems (args ++ procs)
  let s ← saveState
  try
    evalTactic (← `(tactic| simp only [$all,*]))
    pure true
  catch e =>
    s.restore
    let msg := e.toMessageData
    unless (← msg.toString).startsWith "simp made no progress" do
      traceStep m!"normalize failed: {msg}"
    pure false

/-- Run the simp set at a hypothesis. -/
def normalizeAt (s : SimpSet) (h : Name) : TacticM Bool := timed "normalizeAt" do
  if (← getGoals).isEmpty then return false
  let facts := (← factHyps).filter (· != h)
  let names := s.lemmas ++ facts.toArray
  let args ← names.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let procs ← s.procs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| ↓ $(mkIdent n):ident)
  let all : Syntax.TSepArray `Lean.Parser.Tactic.simpLemma "," := .ofElems (args ++ procs)
  let s ← saveState
  try
    evalTactic (← `(tactic| simp only [$all,*] at $(mkIdent h):ident))
    pure true
  catch e =>
    s.restore
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
