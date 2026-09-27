import NanoP4Spec.«5.02-typing-type»
import P4SpecTec.Interp.InterpAl.Interp
/-!
Bounded actual Nano relation observations, not universal SCC certificates. The
reference environment loads only unchanged quoted type dependencies and the two
actual relation definitions. All inputs are generated typed images; guards are
explicitly disabled as in the refinement profile. Kernel facts include actual
recursive execution on both sides. Further native checks below are executable
evidence, not theorem proofs. Hard errors are distinct from ordered mismatch and
fuel exhaustion; no malformed value or synthetic callee body is substituted.
-/

namespace P4SpecTecTest.NanoRelation

open P4SpecTec P4SpecTec.Prelude NanoP4Spec

def narrowSpec : Lang.Al.spec :=
  [set.al, pair.al, map.al, id.al, callableId.al, nameIR.al, typeId.al,
   direction.al, integerTypeIR.al, baseTypeIR.al, parameterIR.al,
   fieldTypeIR.al, externMethodTypeDefIR.al, externMethodTypeDefEnv.al,
   typeIR.al, structTypeIR.al, headerTypeIR.al, dataTypeIR.al,
   externObjectTypeIR.al, parserObjectTypeIR.al, controlObjectTypeIR.al,
   packageObjectTypeIR.al, tableObjectTypeIR.al, objectTypeIR.al,
   Type_eq.al, ParameterType_eq.al]

def txt := ByteText.ofString

def inner : typeIR := .PARSER_lparen_rparen (txt "P") [.mk .IN .BOOL (txt "x")]
def innerOther : typeIR := .PARSER_lparen_rparen (txt "Q") [.mk .IN .BOOL (txt "renamed")]
def outer : typeIR := .PACKAGE_lparen_rparen (txt "K") [.mk .INOUT inner (txt "p")]
def outerOther : typeIR := .PACKAGE_lparen_rparen (txt "L") [.mk .INOUT innerOther (txt "q")]

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
def cfg : Interp_al.Interp.Config := { guard := false }

def reference (fuel : Nat) (name : String) (args : List Lang.Il.value) :=
  (Interp_al.Interp.init narrowSpec).map (fun g =>
    Interp_al.Interp.eval_rel fuel cfg g name args)

-- Type_eq → ParameterType_eq → Type_eq, with actual quoted recursive dispatch.
-- Object IDs and parameter names deliberately differ: the source rules ignore them.
theorem recursiveTypePair :
    reference 25 "Type_eq" [toValue inner, toValue innerOther] = .ok (some (.ok [])) ∧
    Type_eq.run inner innerOther = some (.ok ()) := by
  constructor
  · cbv
  · rw [Type_eq.run.eq_def]
    cbv

/-- info: 'P4SpecTecTest.NanoRelation.recursiveTypePair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recursiveTypePair

def parameter : parameterIR := .mk .IN inner (txt "argument")
def parameterOther : parameterIR := .mk .IN innerOther (txt "renamed")

theorem recursiveParameterPair :
    reference 35 "ParameterType_eq" [toValue parameter, toValue parameterOther] =
      .ok (some (.ok [])) ∧
    ParameterType_eq.run parameter parameterOther = some (.ok ()) := by
  constructor
  · cbv
  · rw [ParameterType_eq.run.eq_def]
    cbv

/-- info: 'P4SpecTecTest.NanoRelation.recursiveParameterPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recursiveParameterPair

def wrongDirection : parameterIR := .mk .OUT innerOther (txt "renamed")

-- The direction check rejects before any recursive type comparison.
theorem directionMismatchPair :
    reference 35 "ParameterType_eq" [toValue parameter, toValue wrongDirection] =
      .ok (some (.error .unmatch)) ∧
    ParameterType_eq.run parameter wrongDirection = some (.error .unmatch) := by
  constructor
  · cbv
  · rw [ParameterType_eq.run.eq_def]
    cbv

/-- info: 'P4SpecTecTest.NanoRelation.directionMismatchPair' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms directionMismatchPair

def wrongType : typeIR :=
  .PARSER_lparen_rparen (txt "P") [.mk .IN (.BIT_langle_rangle 8) (txt "x")]
def wrongLength : typeIR := .PARSER_lparen_rparen (txt "P") []

-- Recursive type disagreement and unequal lengths are ordered mismatches,
-- not hard errors. The source outcomes include actual environment initialization.
theorem orderedMismatchPairs :
    (reference 25 "Type_eq" [toValue inner, toValue wrongType] =
      .ok (some (.error .unmatch)) ∧
      Type_eq.run inner wrongType = some (.error .unmatch)) ∧
    (reference 25 "Type_eq" [toValue inner, toValue wrongLength] =
      .ok (some (.error .unmatch)) ∧
      Type_eq.run inner wrongLength = some (.error .unmatch)) := by
  constructor
  all_goals
    constructor
    · cbv
    · rw [Type_eq.run.eq_def]
      cbv

/-- info: 'P4SpecTecTest.NanoRelation.orderedMismatchPairs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms orderedMismatchPairs

-- A bounded reference fuel can exhaust even though this admitted recursive
-- input has a generated success; exhaustion must not be reclassified as mismatch.
theorem recursiveExhaustion :
    reference 10 "Type_eq" [toValue inner, toValue innerOther] = .ok none := by
  cbv

/-- info: 'P4SpecTecTest.NanoRelation.recursiveExhaustion' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recursiveExhaustion

-- The compositional interface consumes the executable callee result directly;
-- it needs no logical determinism of the mutually recursive relations.
theorem parameterRunOfTypeRun (d e : direction) (a b : typeIR) (n m : ByteText)
    (hdir : (d == e) = true) :
    ParameterType_eq.run (.mk d a n) (.mk e b m) = Type_eq.run a b := by
  rw [ParameterType_eq.run.eq_def]
  simp only [hdir, Eval.check, ite_true, pure_bind]
  cases Type_eq.run a b with
  | none => rfl
  | some result =>
    cases result with
    | ok u => cases u; rfl
    | error _ => rfl

/-- info: 'P4SpecTecTest.NanoRelation.parameterRunOfTypeRun' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms parameterRunOfTypeRun

-- Results compare exact empty relation outputs and both failure kinds.
def sameOutcome : Option (Except Fail (List Lang.Il.value)) →
    Option (Except Fail Unit) → Bool
  | some (.ok []), some (.ok ()) => true
  | some (.error a), some (.error b) => a == b
  | none, none => true
  | _, _ => false

def expect (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"Nano relation observation failed: {label}")

-- Native evidence: recursive package/control paths, ordered type/length/kind
-- mismatch, and exhaustion on a proper admitted value. This does not prove a
-- universal absence of hard errors or a universal fuel bound.
def checkObservations : IO Unit := do
  let .ok g := Interp_al.Interp.init narrowSpec
    | throw (IO.userError "Nano relation quoted environment failed to initialize")
  let control : typeIR := .CONTROL_lparen_rparen (txt "C") [.mk .IN inner (txt "x")]
  let controlOther : typeIR :=
    .CONTROL_lparen_rparen (txt "D") [.mk .IN innerOther (txt "renamed")]
  for (label, a, b, expected) in [
    ("nested-package", outer, outerOther, some (.ok ())),
    ("nested-control", control, controlOther, some (.ok ())),
    ("recursive-type-mismatch", inner, wrongType, some (.error .unmatch)),
    ("length-mismatch", inner, wrongLength, some (.error .unmatch)),
    ("object-kind-mismatch", inner, control, some (.error .unmatch))] do
    let generated := Type_eq.run a b
    let source := Interp_al.Interp.eval_rel 100 cfg g "Type_eq" [toValue a, toValue b]
    expect label (sameOutcome (expected.map (Except.map fun _ => [])) generated &&
      sameOutcome source generated)
  expect "recursive-exhaustion"
    ((Interp_al.Interp.eval_rel 10 cfg g "Type_eq"
      [toValue inner, toValue innerOther]).isNone)
  IO.println "[NanoRelation] recursive/type/length/kind observations agree; exhaustion retained"

#eval checkObservations

end P4SpecTecTest.NanoRelation
