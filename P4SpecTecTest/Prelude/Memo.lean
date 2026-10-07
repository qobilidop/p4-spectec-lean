import P4SpecTec.Prelude.Memo

/-!
The memo wrapper is the computation by definition, on every outcome: success, either
failure, divergence, and runs that allocate. These checks run the compiled implementation
through its cache; a hit must return what the computation itself returns.
-/

open P4SpecTec.Prelude
open StateEval

local instance memoTestBEqExcept [BEq α] : BEq (Except Fail α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private def observe (a : StateEval α) (seed : Int := 0) : Option (Except Fail α × Int) :=
  (run a (FreshState.ofInt seed)).map fun (r, s) => (r, s.counter)

private def key : List Nat := [1, 2, 3]
private def fail : StateEval Nat := throw .unmatch
private def diverge : StateEval Nat := ExceptT.mk fun _ => none

#guard observe (memoRun "a" [MemoKey.of key] freshTypeId) == some (.ok "FRESH__0", 1)
#guard observe (memoRun "a" [MemoKey.of key] freshTypeId) 1 == some (.ok "FRESH__1", 2)
#guard observe (memoRun "f" [] fail) == some (.error .unmatch, 0)
#guard observe (memoRun "d" [] diverge) == none
#guard observe (memoRun "p" [MemoKey.of key] (pure (7 : Nat))) == some (.ok 7, 0)
#guard observe (memoRun "p" [MemoKey.of key] (pure (7 : Nat))) == some (.ok 7, 0)
#guard observe (memoRun "p" [MemoKey.of key] (pure (8 : Nat))) 1 == some (.ok 8, 1)
-- A bounded run: the smaller bound first, then the larger one (a hit), then the smaller
-- again (not a hit of the larger run's entry; the entry is the first run's).
#guard observe (memoRunBounded "b" [MemoKey.of key] 3 (pure (9 : Nat))) == some (.ok 9, 0)
#guard observe (memoRunBounded "b" [MemoKey.of key] 5 (pure (9 : Nat))) == some (.ok 9, 0)
#guard observe (memoRunBounded "b" [MemoKey.of key] 2 freshTypeId) == some (.ok "FRESH__0", 1)
