import NanoP4Spec.«8.14-eval-convention»
import P4SpecTec.BackendSim.NanoSwitch.PipeContract
import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTec.Refine.Value
import P4SpecTec.Runtime.Value.Match

/-!
The runtime-only raw extern alternative represents the actual extract result.
Source packet/object constructors remain disjoint. Contextual execution checks
exercise the generated continuation as well as its failed receiver reuse.
-/

namespace P4SpecTecTest.NanoTargetRepresentation

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine

/-- Every raw extern has a runtime representation without a PACKET wrapper. -/
theorem rawExternRepresented (note : Lang.Il.typ') (json : Lean.Json) :
    Rel (Runtime.Value.Make.extern note json) (NanoP4Spec.value.runtimeExtern ⟨json⟩) := by
  rfl

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.rawExternRepresented'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rawExternRepresented

/-- One positive decoder step recovers the raw runtime alternative. -/
theorem rawExternDecoded (fuel : Nat) (note : Lang.Il.typ') (json : Lean.Json) :
    NanoP4Spec.value.ofValue (fuel + 1) (Runtime.Value.Make.extern note json) =
      some (.runtimeExtern ⟨json⟩) := by
  rfl

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.rawExternDecoded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rawExternDecoded

/-- A raw runtime receiver still fails the source packet subtype check. -/
theorem rawExternNotPacket (json : Lean.Json) :
    NanoP4Spec.value.is_packetValue (.runtimeExtern ⟨json⟩) = false ∧
      NanoP4Spec.value.of_packetValue (.runtimeExtern ⟨json⟩) = none := by
  exact ⟨rfl, rfl⟩

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.rawExternNotPacket'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rawExternNotPacket

/-- Source object decoding is not widened by runtime value decoding. -/
theorem rawExternNotObject (fuel : Nat) (note : Lang.Il.typ') (json : Lean.Json) :
    NanoP4Spec.objectValue.ofValue fuel (Runtime.Value.Make.extern note json) = none := by
  cases fuel <;> rfl

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.rawExternNotObject'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rawExternNotObject

/-- Independent source variant membership rejects raw externs at every positive depth. -/
theorem rawExternNotSourceVariant
    (find : Runtime.Value.Match.FindTypdef) (sig : Runtime.Value.Match.FindFuncChecked)
    (name : String) (params : List Lang.Il.tparam) (cases : List Lang.Il.typcase)
    (h : find name = some (.Defined params (Q.dt (.VariantT cases))))
    (depth : Nat) (note : Lang.Il.typ') (json : Lean.Json) :
    Runtime.Value.Match.sub_checked find sig (depth + 1) (Q.t (Q.varT name []))
      (Runtime.Value.Make.extern note json) = some (.ok false) := by
  simp [Runtime.Value.Match.sub_checked, Q.t, Q.varT, Q.i, Runtime.Value.Make.extern,
    Runtime.Value.Make.mk, h, Q.dt]
  rfl

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.rawExternNotSourceVariant'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rawExternNotSourceVariant

/-- Once lookup returns a raw receiver, actual generated callee selection mismatches. -/
theorem rawReceiverCalleeMismatch (scope : NanoP4Spec.scope) (ctx : NanoP4Spec.evalContext)
    (base : NanoP4Spec.lvalue) (member : NanoP4Spec.nonTypeName) (json : Lean.Json)
    (lookup : NanoP4Spec.Lvalue_eval.run scope ctx base =
      some (.ok (.runtimeExtern ⟨json⟩))) :
    NanoP4Spec.Callee_eval.run scope ctx (.dot base member) = some (.error .unmatch) := by
  simp [NanoP4Spec.Callee_eval.run, NanoP4Spec.lvalue.is_nonTypeName,
    NanoP4Spec.lvalue.of_nonTypeName, lookup, Eval.check, Eval.err?, Eval.ofOption,
    Bind.bind, ExceptT.bind,
    ExceptT.bindCont, ExceptT.run, ExceptT.mk, Pure.pure, ExceptT.pure,
    throw, throwThe, MonadExceptOf.throw]
  rfl

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.rawReceiverCalleeMismatch'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rawReceiverCalleeMismatch

/-- The generated receiver write passes the raw alternative to the actual context updater. -/
theorem rawReceiverWrite (scope : NanoP4Spec.scope) (ctx out : NanoP4Spec.evalContext)
    (name key : NanoP4Spec.nameIR) (json : Lean.Json)
    (named : NanoP4Spec.«$id» (._ID name) = some (.ok key))
    (updated : NanoP4Spec.«$update_var_e» scope ctx key (.runtimeExtern ⟨json⟩) =
      some (.ok out)) :
    NanoP4Spec.Lvalue_write.run scope ctx (._ID name) (.runtimeExtern ⟨json⟩) =
      some (.ok out) := by
  rw [NanoP4Spec.Lvalue_write.run.eq_def]
  simp [NanoP4Spec.lvalue.is_nonTypeName, NanoP4Spec.lvalue.of_nonTypeName,
    named, updated, Eval.check, Eval.err?, Eval.ofOption,
    Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk,
    Pure.pure, ExceptT.pure, throw, throwThe, MonadExceptOf.throw]
  rfl

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.rawReceiverWrite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms rawReceiverWrite

/-- The actual source target rejects a decoded raw receiver before any callback and
preserves its fresh counter on this hard-error branch. -/
theorem rawReceiverHandlerError (call : BackendSim.NanoSwitch.Pipe.Call StateEval)
    (ctx method names : Lang.Il.value) (note : Lang.Il.typ') (json : Lean.Json)
    (state : FreshState) :
    StateEval.run (BackendSim.NanoSwitch.Pipe.eval_extern_method_call call
      [ctx, Runtime.Value.Make.extern note json, method, names]) state =
      some (.error .err, state) := by
  exact BackendSim.NanoSwitch.Pipe.rawReceiverHandlerError call ctx method names note json state

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.rawReceiverHandlerError'
depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms rawReceiverHandlerError

/-- Actual generated OUT copy-out passes its looked-up value unchanged to Lvalue_write. -/
theorem copyOutArgument (callerScope calleeScope : NanoP4Spec.scope)
    (caller callee out : NanoP4Spec.evalContext) (typ : NanoP4Spec.typeIR)
    (name : NanoP4Spec.nameIR) (lv : NanoP4Spec.lvalue) (v : NanoP4Spec.value)
    (found : NanoP4Spec.«$find_var_e» calleeScope callee name = some (.ok v))
    (written : NanoP4Spec.Lvalue_write.run callerScope caller lv v = some (.ok out)) :
    NanoP4Spec.Copy_out_arg.run callerScope caller (.mk .OUT typ name)
      calleeScope callee (some lv) = some (.ok out) := by
  have outEq : (NanoP4Spec.direction.OUT == NanoP4Spec.direction.OUT) = true := by cbv
  simp [NanoP4Spec.Copy_out_arg.run, found, written, outEq, Eval.check,
    Bind.bind, ExceptT.bind, ExceptT.bindCont, ExceptT.run, ExceptT.mk,
    Pure.pure, ExceptT.pure, throw, throwThe, MonadExceptOf.throw]
  rfl

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.copyOutArgument'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms copyOutArgument


/-!
A closed receiver-reuse probe connects the actual quoted AL rules to the generated
callee evaluator. The context is in the extended runtime carrier: its local binding
is raw extern state, not a source packet/object. The unchanged quotation closure
uses the ordinary source interpreter with guards disabled and no callback overrides.
The packet oracle separately compares the entire context produced by actual extract,
copy-out and receiver write for both full and short packets.
-/
namespace ReceiverReuse

open NanoP4Spec

/-- Unchanged source quotation closure needed by this bounded receiver lookup. -/
def sourceSpec : Lang.Al.spec :=
  [scope.al, nonTypeName.al, lvalue.al, referenceExpression.al, name.al,
   map.al, set.al, pair.al, nameIR.al, id.al, frame.al,
   «$print_».al, «$id».al, «$find_map».al, «$find_maps».al, «$find_var_e».al,
   expression.al, «$expression_of_lvalue».al, Expr_eval.al, Lvalue_eval.al, Callee_eval.al]

/-- A closed global layer, untouched by the receiver lookup. -/
def global : globalEvalLayer :=
  ⟨.lbrace_rbrace [], .lbrace_rbrace [], .lbrace_rbrace [],
    .PARSER_lparen_rparen_lbrace_rbrace (ByteText.ofString "p") [] ._EMPTY
      (.STATE_lbrace_rbrace (._ID (ByteText.ofString "start")) ._EMPTY
        (.TRANSITION (.semi (._ID (ByteText.ofString "accept"))))),
    .CONTROL_lparen_rparen_lbrace_APPLY_rbrace (ByteText.ofString "c") [] ._EMPTY
      (.lbrace_rbrace ._EMPTY)⟩

/-- The post-write context contains raw state; `null` is this bounded payload fixture. -/
def context : evalContext :=
  ⟨global, ⟨.lbrace_rbrace []⟩,
    ⟨[.lbrace_rbrace [.colon (ByteText.ofString "pkt") (.runtimeExtern ⟨.null⟩)]]⟩⟩

/-- A subsequent method selection on the raw receiver. -/
def receiver : lvalue :=
  .dot (._ID (ByteText.ofString "pkt")) (._ID (ByteText.ofString "extract"))

/-- Actual AL receiver reuse, including initialization of the unchanged source closure. -/
def sourceResult : Except String (Option (Except Fail (List Lang.Il.value))) :=
  (Interp_al.Interp.init sourceSpec).map fun env =>
    Interp_al.Interp.eval_rel 30 { guard := false } env "Callee_eval"
      [toValue scope.LOCAL, toValue context, toValue receiver]

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Actual generated lookup recovers the raw value from the post-write context. -/
theorem generatedLookup :
    Lvalue_eval.run .LOCAL context (._ID (ByteText.ofString "pkt")) =
      some (.ok (.runtimeExtern ⟨.null⟩)) := by
  rw [Lvalue_eval.run.eq_def]
  cbv

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.ReceiverReuse.generatedLookup'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms generatedLookup

-- A definitional branch rule avoids generating all 48 lazy dispatcher equations
-- while reducing this probe; the source builtin dispatcher itself is unchanged.
/-- The actual builtin map-list dispatch is its implementation branch. -/
theorem invokeFindMaps (tk tv : Lang.Il.typ) (ms k : Lang.Il.value) :
    Builtin.Call.invoke "find_maps" [tk, tv] [ms, k] = (do
      let maps ← (← Runtime.Value.Get.list ms).mapM fun m => do
        (← Builtin.Call.map_of_value m).mapM Builtin.Call.pair_of_value
      pure (Runtime.Value.Make.opt (.IterT tv .Opt) (Builtin.Maps.find_maps maps k))) := rfl

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.ReceiverReuse.invokeFindMaps'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invokeFindMaps

attribute [local cbv_eval] invokeFindMaps

/-- Actual quoted AL and generated evaluation both reject reuse of this raw receiver.
This checks the affected continuation on a bounded runtime context, not a universal
target contract or a source packet/object membership claim. -/
theorem calleeMismatchPair :
    sourceResult = .ok (some (.error .unmatch)) ∧
      Callee_eval.run .LOCAL context receiver = some (.error .unmatch) := by
  constructor
  · cbv
  · exact rawReceiverCalleeMismatch .LOCAL context (._ID (ByteText.ofString "pkt"))
      (._ID (ByteText.ofString "extract")) .null generatedLookup

/-- info: 'P4SpecTecTest.NanoTargetRepresentation.ReceiverReuse.calleeMismatchPair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms calleeMismatchPair

end ReceiverReuse

end P4SpecTecTest.NanoTargetRepresentation
