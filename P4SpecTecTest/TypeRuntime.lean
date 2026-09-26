import P4SpecTec.Runtime.Type.Equiv
import P4SpecTec.Runtime.Value.Match
import P4SpecTec.Interp.InterpAl.Interp
import P4SpecTec.Refine.Quote

/-!
Bounded tests for the checked runtime type port, including alias expansion,
alpha-equivalent function signatures, errors and fuel exhaustion.
-/

namespace P4SpecTecTest.TypeRuntime

open P4SpecTec P4SpecTec.Lang.Il P4SpecTec.Util.Source
open P4SpecTec.Runtime.Type

private def varType (name : String) (args : List typ := []) : typ :=
  mkPhrase (.VarT (mkPhrase name) args)

private def parameter (name : String) : tparam := mkPhrase name
private def boolType : typ := mkPhrase .BoolT
private def textType : typ := mkPhrase .TextT

private def find : Expand.FindTypdef
  | "BoolAlias" => some (.Defined [] (mkPhrase (.PlainT boolType)))
  | "BoundAlias" => some (.Defined [] (mkPhrase (.PlainT (varType "A"))))
  | "UnaryAlias" => some (.Defined [parameter "X"]
      (mkPhrase (.PlainT (varType "X"))))
  | "UnaryStruct" => some (.Defined [parameter "X"] (mkPhrase (.StructT [])))
  | "DuplicateAlias" => some (.Defined [parameter "X", parameter "X"]
      (mkPhrase (.PlainT (varType "X"))))
  | "A" => some (.Defined [] (mkPhrase (.PlainT boolType)))
  | _ => none

private def yields (expected : Bool) (result : Subst.Checked Bool) : Bool :=
  match result.run with
  | some (.ok actual) => actual == expected
  | _ => false

private def errors (expected : String) (result : Subst.Checked α) : Bool :=
  match result.run with
  | some (.error actual) => actual == expected
  | _ => false

#guard yields true (Equiv.equiv_typ find (varType "BoolAlias") boolType)
#guard yields true (Equiv.equiv_typ find (varType "UnaryAlias" [textType]) textType)
#guard yields true (Equiv.equiv_typ find (varType "DuplicateAlias" [boolType, textType])
  textType)
#guard errors "type arguments do not match"
  (Equiv.equiv_typ find (varType "UnaryAlias") boolType)
#guard errors "type variable Missing is not defined"
  (Equiv.equiv_typ find (varType "Missing") boolType)

#guard yields true (Equiv.equiv_functyp find [parameter "X"] [varType "X"] (varType "X")
  [parameter "Y"] [varType "Y"] (varType "Y"))
#guard yields false (Equiv.equiv_functyp find [parameter "X"] [varType "X"] (varType "X")
  [parameter "Y"] [varType "Y"] boolType)
-- An alias body introducing `A` must see the global alias, not the caller's
-- function binder of the same spelling.
#guard yields true (Equiv.equiv_functyp find [parameter "A"] [varType "BoundAlias"] boolType
  [parameter "B"] [boolType] boolType)
#guard errors "higher-order substitution is disallowed"
  (Equiv.equiv_functyp find [parameter "X"] [varType "X" [boolType]] boolType
    [parameter "Y"] [varType "Y" [boolType]] boolType)
#guard yields false (Equiv.equiv_functyp find [parameter "X"] [varType "X"] boolType
  [] [boolType] boolType)
#guard errors "type variable Missing is not defined"
  (Equiv.equiv_typ find (mkPhrase (.IterT (varType "Missing") .Opt))
    (mkPhrase (.IterT boolType .List)))
private def leftNotation : nottyp :=
  mkPhrase (.Seq [.Arg (varType "Missing"), .Atom (mkPhrase (.Keyword "LEFT"))])
private def rightNotation : nottyp :=
  mkPhrase (.Seq [.Arg boolType, .Atom (mkPhrase (.Keyword "RIGHT"))])
#guard errors "type variable Missing is not defined"
  (Equiv.equiv_nottyp find leftNotation rightNotation)

private def replacement : Subst.theta := [("X", boolType)]
#guard (Subst.subst_typ_checked 0 replacement (varType "X")).run.isNone
#guard errors "higher-order substitution is disallowed"
  (Subst.subst_typ_checked 1 replacement (varType "X" [textType]))
#guard errors "function-type substitution requires type-fresh state"
  (Subst.subst_typ_checked Subst.fuel replacement
    (mkPhrase (.FuncT [parameter "Y"] [varType "Y"] (varType "Y"))))
#guard (Subst.subst_typ_checked 0 []
  (mkPhrase (.FuncT [parameter "Y"] [varType "Y"] (varType "Y")))).run.isSome
#guard (Expand.expand_typ 0 find boolType).run.isNone
#guard (Equiv.equiv_typ_inner find 0 boolType boolType).run.isNone

private def functionValue : value :=
  P4SpecTec.Runtime.Value.Make.func (mkPhrase "f") [parameter "Y"]
    [varType "Y"] (varType "Y")

private def findFunction : P4SpecTec.Runtime.Value.Match.FindFuncChecked
  | "f" => pure (some ([parameter "Y"], [varType "Y"], varType "Y"))
  | _ => pure none

private def functionType : typ :=
  mkPhrase (.FuncT [parameter "X"] [varType "X"] (varType "X"))

#guard yields true (P4SpecTec.Runtime.Value.Match.sub_checked find findFunction 1000
  functionType functionValue)
#guard yields true (P4SpecTec.Runtime.Value.Match.check_checked find findFunction 1000
  (.RecurseSC functionType) functionValue)
#guard (P4SpecTec.Runtime.Value.Match.sub_checked find findFunction 0
  functionType functionValue).run.isNone
#guard errors "type variable Missing is not defined"
  (P4SpecTec.Runtime.Value.Match.sub_checked find findFunction 1000
    (varType "Missing") functionValue)
#guard errors "List.fold_left2"
  (P4SpecTec.Runtime.Value.Match.sub_checked find findFunction 1000
    (varType "UnaryAlias") (P4SpecTec.Runtime.Value.Make.bool true))
#guard yields false (P4SpecTec.Runtime.Value.Match.sub_checked find findFunction 1000
  (varType "UnaryStruct") (P4SpecTec.Runtime.Value.Make.bool true))

open P4SpecTec.Interp_al P4SpecTec.Prelude
private def boolLiteral : exp := P4SpecTec.Refine.Q.e (.BoolE true) .BoolT
private def subExpression (typ : typ) : exp :=
  P4SpecTec.Refine.Q.e (.SubE boolLiteral typ (.RecurseSC typ)) .BoolT
private def emptyContext : Ctx.t := Ctx.empty {}
private def pureConfig : Interp.Config Eval := {}
private def callbackContext : Ctx.t :=
  let table : Std.HashMap String P4SpecTec.Runtime.Dynamic_al.Func.t := {}
  let table := table.insert "f"
    (.Extern [parameter "Y"] [mkPhrase (.ExpP (varType "Y"))] (varType "Y"))
  let table := table.insert "accept" (.Extern [] [mkPhrase (.ExpP functionType)] boolType)
  { global := { ftbl := table }
    «local» := { venv := [((mkPhrase "v", []), functionValue)] } }
private def callbackSubExpression : exp :=
  P4SpecTec.Refine.Q.e (.SubE
    (P4SpecTec.Refine.Q.e (.VarE (mkPhrase "v")) functionType.it)
    functionType (.RecurseSC functionType)) .BoolT

#guard match (Interp.eval_exp 30 pureConfig emptyContext (subExpression boolType)).run with
  | some (.ok ⟨.BoolV true, _, _⟩) => true
  | _ => false
#guard match (Interp.eval_exp 30 pureConfig emptyContext
    (subExpression (varType "Missing"))).run with
  | some (.error .err) => true
  | _ => false
#guard (Interp.eval_exp 0 pureConfig emptyContext (subExpression boolType)).run.isNone
#guard match (Interp.eval_exp 30 pureConfig callbackContext callbackSubExpression).run with
  | some (.ok ⟨.BoolV true, _, _⟩) => true
  | _ => false
#guard match (Interp.check_func_inputs pureConfig callbackContext (mkPhrase "accept") []
    [functionValue]).run with
  | some (.ok ()) => true
  | _ => false
#guard (P4SpecTec.Runtime.Value.Match.sub_checked find
  (Ctx.find_func_signature_opt_checked' 0 callbackContext) 1000
  functionType functionValue).run.isNone
#guard match (Ctx.find_func_signature_opt_checked' 0 callbackContext "absent").run with
  | some (.ok none) => true
  | _ => false
private def nestedParameter : param :=
  mkPhrase (.DefP (mkPhrase "g") [] [mkPhrase (.ExpP boolType)] boolType)
#guard (Typ.Make.of_param_il_checked 1 nestedParameter).isNone
#guard (Typ.Make.of_param_il_checked 2 nestedParameter).isSome
#guard match (Interp.check_func_output ({ guard := false } : Interp.Config Eval)
    emptyContext (mkPhrase "f") [] boolType []
    (P4SpecTec.Runtime.Value.Make.text (ByteText.ofString "wrong"))).run with
  | some (.ok ()) => true
  | _ => false
#guard match (Interp.check_func_output ({ guard := true } : Interp.Config Eval)
    emptyContext (mkPhrase "f") [] boolType []
    (P4SpecTec.Runtime.Value.Make.text (ByteText.ofString "wrong"))).run with
  | some (.error .err) => true
  | _ => false

end P4SpecTecTest.TypeRuntime
