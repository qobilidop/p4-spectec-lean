import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTec.Refine.Quote
import P4SpecTec.Tactic.Refine

/-!
The same AL evaluator in pure and stateful modes. These small AL programs
exercise state through real calls, rejected alternatives, negative premises,
and repeated shared rule prefixes. They are not full-P4 validation.
-/

namespace P4SpecTecTest.StateInterp

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Interp_al P4SpecTec.Refine
open P4SpecTec.Lang.Il P4SpecTec.Lang.Al

private def textTyp := Q.t .TextT
private def fresh : exp := Q.e (.CallE (Q.i "fresh_typeId") [] []) .TextT
private def x : exp := Q.e (.VarE (Q.i "x")) .TextT
private def save : prem := Q.pr (.LetPr x fresh)
private def mismatch : prem := Q.pr (.IfPr (Q.e (.BoolE false) .BoolT))
-- Assigning a text value to a boolean-shaped expression is a hard error.
private def hardError : prem := Q.pr (.LetPr (Q.e (.BoolE true) .BoolT) x)
private def freshDecl := Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] textTyp [])

private def function (name : String) (prems : List prem) : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i name) [] [] textTyp
    [Q.cl [] fresh prems, Q.cl [] fresh []] none [])

private def negativeFunction (name target : String) : Lang.Al.def :=
  let tagged (tag : String) : exp :=
    Q.e (.CatE (Q.e (.TextE (ByteText.ofString tag)) .TextT) fresh) .TextT
  Q.d (.FuncDecD (Q.i name) [] [] textTyp
    [Q.cl [] (tagged "first:") [Q.pr (.IfNotHoldPr (Q.i target) (.Seq []))],
     Q.cl [] (tagged "fallback:") []] none [])

private def relation (name : String) (prems : List prem) : Lang.Al.def :=
  Q.d (.RelD (Q.i name) (Q.nt (.Seq [])) []
    [Q.rg "one" ([], [], []) [Q.rp "path" prems []]] none [])

private def spec : Lang.Al.spec :=
  [freshDecl,
   function "allocate" [],
   Q.d (.ExternDecD (Q.i "externalFresh") [] [] textTyp []),
   function "externalRetry" [Q.pr (.LetPr x
     (Q.e (.CallE (Q.i "externalFresh") [] []) .TextT))],
   Q.d (.FuncDecD (Q.i "through") [] [Q.pm (.DefP (Q.i "f") [] [] textTyp)] textTyp
     [Q.cl [Q.ar (.DefA (Q.i "f"))] (Q.e (.CallE (Q.i "f") [] []) .TextT) []] none []),
   function "retry" [save, mismatch],
   function "stop" [save, hardError],
   relation "fails" [save, mismatch],
   relation "holds" [save],
   relation "errors" [save, hardError],
   negativeFunction "negative" "fails",
   negativeFunction "negativeSuccess" "holds",
   negativeFunction "negativeError" "errors",
   Q.d (.RelD (Q.i "shared") (Q.nt (.Arg textTyp)) []
     [Q.rg "group" ([], [], [save])
       [Q.rp "reject" [mismatch] [x], Q.rp "accept" [] [x]]] none [])]

#guard (Interp.init spec).isOk
private def globals : Ctx.global := (Interp.init spec).toOption.getD {}
private def cfg : Interp.Config StateEval := { guard := false }

local instance [BEq α] : BEq (Except Fail α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

private def observe (r : Option (Except Fail value × FreshState)) :
    Option (Except Fail (Option String) × Int) :=
  r.map fun (v, s) =>
    (v.map (fun x => Runtime.Value.Get.text x >>= ByteText.toString?), s.counter)

private def call (name : String) (seed : Int := 0) :=
  observe (Interp.evalFuncState 100 cfg globals name [] [] (FreshState.ofInt seed))

#guard call "fresh_typeId" == some (.ok (some "FRESH__0"), 1)
#guard call "retry" == some (.ok (some "FRESH__1"), 2)
#guard call "stop" == some (.error .err, 1)
#guard call "negative" == some (.ok (some "first:FRESH__1"), 2)
#guard call "negativeSuccess" == some (.ok (some "fallback:FRESH__1"), 2)
#guard call "negativeError" == some (.error .err, 1)
#guard call "fresh_typeId" 4611686018427387903 ==
  some (.ok (some "FRESH__4611686018427387903"), -4611686018427387904)

-- An interpreter callback is resolved locally and shares the enclosing session.
#guard observe (Interp.evalFuncState 100 cfg globals "through" []
    [Runtime.Value.Make.func (Q.i "allocate") [] [] textTyp] (FreshState.ofInt 12)) ==
  some (.ok (some "FRESH__12"), 13)

private def externCfg : Interp.Config StateEval := { cfg with
  extern := {
    eval_extern_rel := fun _ _ => throw .unmatch
    eval_extern_func := fun _ _ _ => do
      let _ ← StateEval.freshTypeId
      throw .unmatch } }

#guard observe (Interp.evalFuncState 100 externCfg globals "externalRetry" [] [] 0) ==
  some (.ok (some "FRESH__1"), 2)

-- A shared premise is rerun for the second full path, not hoisted across choice.
#guard match Interp.evalRelState 100 cfg globals "shared" [] 0 with
  | some (.ok [v], s) =>
    Runtime.Value.Get.text v == some (ByteText.ofString "FRESH__1") && s.counter == 2
  | _ => false

-- Builtin arity errors are BuiltinError/mismatch, before allocation.
private def builtin (targs : List typ) (args : List value) :=
  observe (StateEval.run
    (Interp.invoke_builtin_func 1 cfg (Ctx.empty globals) (Q.i "fresh_typeId")
      [] targs args textTyp) (FreshState.ofInt 7))

#guard builtin [textTyp] [] == some (.error .unmatch, 7)
#guard builtin [] [Runtime.Value.Make.text (ByteText.ofString "argument")] ==
  some (.error .unmatch, 7)
#guard builtin [] [] == some (.ok (some "FRESH__7"), 8)

-- Output checking happens after allocation and cannot roll the counter back.
#guard match StateEval.run (Interp.invoke_builtin_func 1
    ({ guard := true } : Interp.Config StateEval) (Ctx.empty globals)
    (Q.i "fresh_typeId") [] [] [] (Q.t .BoolT)) 0 with
  | some (.error .err, s) => s.counter == 1
  | _ => false

-- A caller can continue the session after failure without resetting it.
private def resume : Option (Except Fail value × FreshState) := do
  let (_, s) ← Interp.evalFuncState 100 cfg globals "stop" [] [] 0
  Interp.evalFuncState 100 cfg globals "fresh_typeId" [] [] s

#guard observe resume == some (.ok (some "FRESH__1"), 2)
#guard Interp.evalFuncState 0 cfg globals "fresh_typeId" [] [] 0 == none

-- Existing pure call syntax, including an unannotated configuration, still works.
#guard match (Interp.invoke_builtin_func 1 { guard := false } (Ctx.empty globals)
    (Q.i "fresh_typeId") [] [] [] textTyp).run with
  | some (.error .unmatch) => true
  | _ => false

-- The tactic must find fuel past the implicit carrier and effect instance.
run_elab do
  let term ← Lean.Elab.Term.elabTerm (← `(Interp.eval_exp (m := StateEval)
    7 cfg (Ctx.empty globals) fresh)) none
  let some fuel ← P4SpecTec.Tactic.fuelArgument? term
    | throwError "missing generic interpreter fuel"
  unless ← Lean.Meta.isDefEq fuel (Lean.mkNatLit 7) do
    throwError "generic interpreter fuel is not 7"

end P4SpecTecTest.StateInterp
