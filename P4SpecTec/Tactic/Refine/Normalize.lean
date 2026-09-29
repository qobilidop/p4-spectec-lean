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
def factHyps (lookups : Bool := true) : TacticM (List Name) := do
  -- a decided fact with a closed left side (`1 = xs.length`) would rewrite that constant
  -- everywhere; it is used in the other direction
  let flips ← (← getMainGoal).withContext do
    let mut flips : List Name := []
    for decl in ← getLCtx do
      if decl.isImplementationDetail || !decl.userName.toString.startsWith "rf_c" then continue
      if let some (_, lhs, rhs) := (← instantiateMVars decl.type).consumeMData.eq? then
        if !lhs.hasFVar && rhs.hasFVar then flips := decl.userName :: flips
    pure flips
  for name in flips do
    let saved ← saveState
    try evalTactic (← `(tactic| replace $(mkIdent name):ident := Eq.symm $(mkIdent name)))
    catch _ => saved.restore
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
      -- a table fact's right side is a whole quoted definition; it rewrites only lookups
      if !lookups && decl.userName.toString.startsWith "rf_tbl_" then continue
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
  /-- The simproc and pre-order (`↓`) lemma names used to prepare the context. -/
  procs : Array Name
  /-- Lean's elaborated simplifier context and procedures. -/
  result : MkSimpContextResult
  /-- Normalization inputs already known to make no progress with these rules, by hash:
  the simplified statement, then the statements of the facts it rewrites with. -/
  noProgress : IO.Ref (Std.HashMap UInt64 (Array (Array Expr)))
  /-- Simplification results for closed terms, shared by the normalizations of one
  invocation (`seededSimp`), by the local statements that can affect them (`closedInputs`). -/
  closed : IO.Ref (Std.HashMap (Array Expr) (Std.HashMap Expr Simp.Result))

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
  -- Reference contexts carry large values; the default step budget (100000) is exhausted
  -- by ordinary reductions over them, not only by loops.
  match hyp? with
  | none => `(tactic| simp (maxSteps := 1000000) only [$all,*])
  | some h => `(tactic| simp (maxSteps := 1000000) only [$all,*] at $(mkIdent h):ident)

/-- Elaborate the fixed global rules once, before the tactic changes its local context.
The cached names are checked at each use, so extending a prepared set cannot omit rules. -/
def prepareSimpSet (s : SimpSet) : TacticM SimpSet := withMainContext do
  -- the rules are added by constant, as `simp` adds an argument naming one: elaborating their
  -- names would resolve each under the current namespace first, and a candidate such as
  -- `….match_rule.eq_1` reads the matcher extension, which waits for every earlier proof of
  -- the module to be checked
  let base ← mkSimpContext (← simpSyntax #[] #[]) (eraseLocal := false)
  let mut thmsArray := base.ctx.simpTheorems
  let mut thms := thmsArray[0]!
  let mut simprocs := base.simprocs
  -- every rule is a global constant (`getConstVal` fails otherwise), never a local declaration
  let add (thms : SimpTheorems) (n : Name) (post : Bool) : MetaM SimpTheorems := do
    let entries ← if ← isProp (← getConstVal n).type then
        pure ((← mkSimpTheoremFromConst n (post := post)).map SimpEntry.thm)
      else mkSimpEntryOfDeclToUnfold n
    let mut thms := thms
    for entry in entries do
      thms := (thms.uneraseSimpEntry entry).addSimpEntry entry
    pure thms
  for n in s.lemmas do
    if (← Simp.isSimproc n) || (← Simp.isBuiltinSimproc n) then simprocs ← simprocs.add n true
    else thms ← add thms n true
  for n in s.procs do
    if (← Simp.isSimproc n) || (← Simp.isBuiltinSimproc n) then
      simprocs ← simprocs.add n false
    else thms ← add thms n false
  let result := { base with ctx := base.ctx.setSimpTheorems (thmsArray.set! 0 thms), simprocs }
  let noProgress ← IO.mkRef {}
  let closed ← IO.mkRef {}
  let prepared : PreparedSimpRules :=
    { lemmas := s.lemmas, procs := s.procs, result, noProgress, closed }
  pure { s with prepared? := some prepared }

/-- Every local proposition the default discharger may assume. It compares types by
definitional equality, so a syntactic equation-hypothesis test misses reducible aliases. -/
def dischargeAssumptions : TacticM (Array Expr) := withMainContext do
  let mut out := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ← isProp ty then out := out.push ty
  pure out

/-- Local let values can change definitional equality for a rewriting fact or a discharger
assumption, even when its syntactic type is unchanged across tactic backtracking. -/
def localLetInputs : TacticM (Array Expr) := withMainContext do
  let mut out := #[]
  for decl in ← getLCtx do
    if let some value := decl.value? then
      out := out.push (mkFVar decl.fvarId)
      out := out.push (← instantiateMVars decl.type)
      out := out.push (← instantiateMVars value)
  pure out

/-- The local statements that can change how a closed term simplifies. Even a rule with a
local variable on its left may match a closed term by definitional equality after unfolding a
local let. The discharger may likewise use open or aliased propositions, so retain every fact
and every local proposition in the cache key. -/
def closedInputs (facts : List Name) : TacticM (Array Expr) := withMainContext do
  let mut out := #[]
  for n in facts do
    let some decl := (← getLCtx).findFromUserName? n | throwError "refine_al: no hypothesis {n}"
    let ty ← instantiateMVars decl.type
    out := out.push ty
  pure (out ++ #[mkConst `assumed] ++ (← dischargeAssumptions) ++
    #[mkConst `localLets] ++ (← localLetInputs))

/-- The inputs that determine a normalization with prepared rules: the statement it
simplifies (the goal, or hypothesis `hyp?`), the statements of its rewriting facts and the
hypotheses its discharger may assume. The prepared rules and simprocs are fixed and do not read
the local context otherwise, so equal inputs make equal progress. `none` without prepared
rules. -/
def normalizationKey (s : SimpSet) (facts : List Name) (hyp? : Option Name) :
    TacticM (Option (Array Expr)) := withMainContext do
  let some prepared := s.prepared? | return none
  unless prepared.lemmas == s.lemmas && prepared.procs == s.procs do return none
  let statement (n : Name) : TacticM Expr := do
    let some decl := (← getLCtx).findFromUserName? n
      | throwError "refine_al: no hypothesis {n}"
    instantiateMVars decl.type
  let subject ← match hyp? with
    | none => do instantiateMVars (← getMainTarget)
    | some h => do pure (mkApp (mkConst `hyp) (← statement h))
  pure (#[subject] ++ (← facts.toArray.mapM statement) ++ #[mkConst `assumed] ++
    (← dischargeAssumptions) ++ #[mkConst `localLets] ++ (← localLetInputs))

/-- The hash of a normalization key. -/
def keyHash (key : Array Expr) : UInt64 :=
  key.foldl (fun h e => mixHash h e.hash) 7

/-- Whether normalization of `key` is already known to make no progress. -/
def knownNoProgress (s : SimpSet) (key? : Option (Array Expr)) : IO Bool := do
  let (some prepared, some key) := (s.prepared?, key?) | return false
  return ((← prepared.noProgress.get).getD (keyHash key) #[]).contains key

/-- Record that normalization of `key` made no progress. -/
def recordNoProgress (s : SimpSet) (key? : Option (Array Expr)) : IO Unit := do
  let (some prepared, some key) := (s.prepared?, key?) | return
  prepared.noProgress.modify fun m => m.insert (keyHash key) ((m.getD (keyHash key) #[]).push key)

/-- Simplify `e` as `Lean.Meta.simp` does, with the memo table seeded from `closed`. A
result whose term, normal form and proof are all closed holds in every local context, and it
is what simp computes again wherever the rules that can apply to closed terms are the same:
the fixed global rules and `inputs` (`closedInputs`). The new such results are added to
`closed` under `inputs`. Terms with free variables are simplified afresh. -/
def seededSimp (closed : IO.Ref (Std.HashMap (Array Expr) (Std.HashMap Expr Simp.Result)))
    (inputs : Array Expr) (e : Expr) (ctx : Simp.Context) (simprocs : Simp.SimprocsArray)
    (discharge? : Option Simp.Discharge) (stats : Simp.Stats) :
    MetaM (Simp.Result × Simp.Stats) := do
  let known := (← closed.get).getD inputs {}
  let seed : Simp.Cache := { stage₁ := false, map₁ := known, map₂ := {} }
  let (r, state) ← simpCore e ctx simprocs discharge? { stats with cache := seed }
  -- only imported constants: a backtracked attempt rolls back constants realized meanwhile
  let env ← getEnv
  let isClosed (x : Expr) := !x.hasFVar && !x.hasMVar && !x.hasLooseBVars &&
    x.getUsedConstants.all env.isImportedConst
  let fresh := state.cache.map₂.foldl (init := #[]) fun acc k v =>
    if !known.contains k && isClosed k && isClosed v.expr && v.proof?.all isClosed then
      acc.push (k, v)
    else acc
  unless fresh.isEmpty do
    closed.modify fun m => m.insert inputs (fresh.foldl (fun m (k, v) => m.insert k v) known)
  return (r, { usedTheorems := state.usedTheorems, diag := state.diag })

/-- `simpLocation` at the goal (`hyp? = none`) or at one hypothesis, through `seededSimp`;
otherwise `Lean.Meta.simpGoal`'s steps, including its failure without progress. -/
def seededSimpLocation (prepared : PreparedSimpRules) (ctx : Simp.Context)
    (simprocs : Simp.SimprocsArray) (discharge? : Option Simp.Discharge) (facts : List Name)
    (hyp? : Option Name) : TacticM Simp.Stats := withMainContext do
  let closed := prepared.closed
  let inputs ← closedInputs facts
  let mvarId ← getMainGoal
  mvarId.checkNotAssigned `simp
  match hyp? with
  | none =>
    let target ← instantiateMVars (← mvarId.getType)
    let (r, stats) ← seededSimp closed inputs target ctx simprocs discharge? {}
    if r.expr.isTrue then
      match r.proof? with
      | some proof => mvarId.assign (← mkOfEqTrue proof)
      | none => mvarId.assign (mkConst ``True.intro)
      replaceMainGoal []
      return stats
    let mvarIdNew ← applySimpResultToTarget mvarId target r
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "`simp` made no progress"
    replaceMainGoal [mvarIdNew]
    return stats
  | some h =>
    let fvarId ← getFVarId (mkIdent h)
    let localDecl ← fvarId.getDecl
    let type ← instantiateMVars localDecl.type
    let ctx := ctx.setSimpTheorems <| ctx.simpTheorems.eraseTheorem (.fvar fvarId)
    let (r, stats) ← seededSimp closed inputs type ctx simprocs discharge? {}
    let mut mvarIdNew := mvarId
    match r.proof? with
    | some _ =>
      match ← applySimpResult mvarId (mkFVar fvarId) type r with
      | none => replaceMainGoal []; return stats
      | some (value, type') =>
        let (_, m) ← mvarIdNew.assertHypotheses
          #[{ userName := localDecl.userName, type := type', value := value }]
        mvarIdNew ← m.tryClearMany #[fvarId]
    | none =>
      if r.expr.isFalse then
        mvarId.assign (← mkFalseElim (← mvarId.getType) (mkFVar fvarId))
        replaceMainGoal []
        return stats
      mvarIdNew ← mvarIdNew.replaceLocalDeclDefEq fvarId r.expr
    if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
      throwError "`simp` made no progress"
    replaceMainGoal [mvarIdNew]
    return stats

/-- Normalize with fixed global rules and freshly elaborated facts for this goal. Besides rule
preparation, only closed-term results are reused (`seededSimp`); local facts are elaborated
afresh. -/
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
      withSimpDiagnostics do
        let stats ← r.dischargeWrapper.with fun discharge? =>
          withLoopChecking r
            (seededSimpLocation prepared r.ctx r.simprocs discharge? facts hyp?)
        if tactic.simp.trace.get (← getOptions) then
          let traceStx ← simpSyntax (s.lemmas ++ facts.toArray) s.procs hyp?
          traceSimpCall traceStx stats.usedTheorems
        else if Linter.getLinterValue linter.unusedSimpArgs (← Linter.getLinterOptions) then
          withRef stx do warnUnusedSimpArgs r.simpArgs stats.usedTheorems
        pure stats.diag
      return
  evalTactic (← simpSyntax (s.lemmas ++ facts.toArray) s.procs hyp?)

/-- Run `act`; when it exhausts a resource limit (a runtime exception, which `catch`
does not see) and tracing is on, report the goal it was working on, then rethrow the
original exception. Formatting gets a fresh heartbeat budget and cannot replace it. -/
def reportingLimits (what : String) (act : TacticM Unit) : TacticM Unit := do
  let goal ← getMainGoal
  tryCatchRuntimeEx act fun e => do
    if e.isRuntime && refine_al.trace.get (← getOptions) then
      tryCatchRuntimeEx (withCurrHeartbeats do
        -- eager: the lazy goal message loses its context once the exception unwinds
        let shown ← Meta.ppGoal goal
        traceStep m!"{what} exhausted a resource limit on\n{shown}")
        fun _ => pure ()
    throw e

/-- Run `simp only` with the set and the facts at the goal; `false` when
nothing changed. -/
def normalize (s : SimpSet) : TacticM Bool := timed "normalize" do
  if (← getGoals).isEmpty then return false
  let target ← instantiateMVars (← (← getMainGoal).getType)
  let lookups := (target.find? fun e => e.isConstOf ``Std.HashMap.get?).isSome
  let facts ← factHyps lookups
  let key ← normalizationKey s facts none
  if ← knownNoProgress s key then return false
  let saved ← saveState
  try
    let t0 ← IO.monoMsNow
    reportingLimits "normalize" (runNormalization s facts)
    let t1 ← IO.monoMsNow
    if t1 - t0 > 300 then traceStep m!"slow normalize: {t1 - t0} ms"
    pure true
  catch e =>
    saved.restore
    recordNoProgress s key
    -- formatting a failure is costly; only the trace reads it
    unless refine_al.trace.get (← getOptions) do return false
    let msg := e.toMessageData
    let text ← msg.toString
    unless text.startsWith "simp made no progress" do
      traceStep m!"normalize failed: {msg}"
      if (text.splitOn "maximum number of steps").length > 1 &&
          refine_al.trace.get (← getOptions) then
        traceStep m!"on the goal\n{← Meta.ppGoal (← getMainGoal)}"
    pure false

/-- Run the simp set at a hypothesis. -/
def normalizeAt (s : SimpSet) (h : Name) : TacticM Bool := timed "normalizeAt" do
  if (← getGoals).isEmpty then return false
  let facts := (← factHyps false).filter (· != h)
  let key ← normalizationKey s facts h
  if ← knownNoProgress s key then return false
  let saved ← saveState
  try
    let t0 ← IO.monoMsNow
    reportingLimits s!"normalize at {h}" (runNormalization s facts h)
    let t1 ← IO.monoMsNow
    if t1 - t0 > 300 then traceStep m!"slow normalize at {h}: {t1 - t0} ms"
    pure true
  catch e =>
    saved.restore
    recordNoProgress s key
    unless refine_al.trace.get (← getOptions) do return false
    let msg := e.toMessageData
    unless (← msg.toString).startsWith "simp made no progress" do
      traceStep m!"normalize at {h} failed: {msg}"
    pure false

/-- Normalise every fact (a hypothesis the driver rewrites with) at its
own statement: after a case split, `toValue` of a constructor computes
to a literal, which exposure needs. -/
def normalizeFacts (s : SimpSet) : TacticM Unit := do
  if (← getGoals).isEmpty then return
  -- decided case-split facts first: a branch whose test conflicts closes before the
  -- larger facts are traversed
  let facts ← factHyps
  let (decided, others) := facts.partition (·.toString.startsWith "rf_c")
  for h in decided ++ others do
    -- a fact may become `False` and close the goal
    if (← getGoals).isEmpty then return
    -- a table fact is normalized when it is derived (`tableFacts`); its right side is a
    -- closed quoted definition that no later case split changes, and re-simplifying it
    -- would traverse the whole definition at every step
    if h.toString.startsWith "rf_tbl_" then continue
    let _ ← normalizeAt s h

end P4SpecTec.Tactic
