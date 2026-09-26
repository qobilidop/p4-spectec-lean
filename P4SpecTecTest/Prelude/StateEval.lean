import P4SpecTec.Prelude.StateEval

/-! Regression checks for explicit fresh state, including failure effects
and the signed 63-bit wraparound of upstream's 64-bit OCaml runtime. -/

open P4SpecTec.Prelude
open StateEval

local instance [BEq α] : BEq (Except Fail α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private def observe (a : StateEval α) (seed : Int := 0) : Option (Except Fail α × Int) :=
  (run a (FreshState.ofInt seed)).map fun (r, s) => (r, s.counter)

#guard FreshState.initial.counter == 0
#guard observe freshTypeId == some (.ok "FRESH__0", 1)
#guard observe freshTypeId 1 == some (.ok "FRESH__1", 2)

private def two : StateEval (String × String) := do
  let a ← freshTypeId
  let b ← freshTypeId
  pure (a, b)

#guard observe two == some (.ok ("FRESH__0", "FRESH__1"), 2)

private def consumeThenFail (f : Fail) : StateEval String := do
  let _ ← freshTypeId
  throw f

#guard observe (consumeThenFail .unmatch <|> freshTypeId) == some (.ok "FRESH__1", 2)
#guard observe (consumeThenFail .err <|> freshTypeId) == some (.error .err, 1)
#guard observe (freshTypeId <|> freshTypeId) == some (.ok "FRESH__0", 1)
#guard observe (notHold freshTypeId) == some (.error .unmatch, 1)
#guard observe (notHold (consumeThenFail .unmatch)) == some (.ok (), 1)
#guard observe (notHold (consumeThenFail .err)) == some (.error .err, 1)

private def nested : StateEval (List String) := do
  let _ ← two
  [(), (), ()].mapM fun _ => freshTypeId

#guard observe nested == some (.ok ["FRESH__2", "FRESH__3", "FRESH__4"], 5)

private def mapFailure : StateEval (List String) :=
  [false, true, false].mapM fun fails => do
    let x ← freshTypeId
    if fails then throw .unmatch else pure x

#guard observe mapFailure == some (.error .unmatch, 2)
#guard observe (mapFailure <|> [()].mapM (fun _ => freshTypeId)) ==
  some (.ok ["FRESH__2"], 3)

#guard observe (liftEval (pure (7 : Nat))) 12 == some (.ok 7, 12)
#guard observe (liftEval (throw .unmatch : Eval Nat)) 12 == some (.error .unmatch, 12)
#guard observe (liftEval (throw .err : Eval Nat)) 12 == some (.error .err, 12)
#guard observe (liftEval (Eval.diverge : Eval Nat)) 12 == none
#guard observe (liftEval (Eval.diverge : Eval String) <|> freshTypeId) == none

-- Retain an earlier post-state to continue; explicitly choose initial to reset.
private def resumed : Option (Except Fail String × FreshState) := do
  let (_, s) ← run freshTypeId FreshState.initial
  run freshTypeId s

#guard resumed == some (.ok "FRESH__1", FreshState.ofInt 2)
#guard run freshTypeId FreshState.initial == some (.ok "FRESH__0", FreshState.ofInt 1)
#guard observe freshTypeId 42 == some (.ok "FRESH__42", 43)
#guard observe freshTypeId (-1) == some (.ok "FRESH__-1", 0)

-- max_int = 2^62 - 1; min_int = -2^62. The printed value is before increment.
#guard observe two 4611686018427387903 ==
  some (.ok ("FRESH__4611686018427387903", "FRESH__-4611686018427387904"),
    -4611686018427387903)
#guard (FreshState.ofInt 9223372036854775808).counter == 0
