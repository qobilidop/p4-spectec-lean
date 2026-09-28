import NanoP4Spec.Refinement.Spec
import P4SpecTec.Codegen.Certificates.Forward
import P4SpecTec.Codegen.Certificates.Reverse
import P4SpecTec.Codegen.Certificates.SourceEntry
import P4SpecTec.Refine.Init
import P4SpecTec.Refine.Subtype
import P4SpecTec.Interp.InterpAl.Interp

/-! Polymorphic membership certificates retain actual equality and registration boundaries. -/

namespace P4SpecTecTest.Codegen.ForwardCertificates

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Codegen P4SpecTec.Refine

private def env := Env.ofSpec "NanoP4Spec" NanoP4Spec.spec

#guard Validate.unsupported env [] NanoP4Spec.«$in_set».al == none
#guard Validate.unsupported env [] NanoP4Spec.«$dom_map».al == none
#guard Validate.unsupported env [] NanoP4Spec.«$codom_map».al == none
#guard Validate.functionListColumns env NanoP4Spec.«$default».al
#guard Props.requiresColumnsOf NanoP4Spec.«$default».al
#guard Validate.unsupported env [] NanoP4Spec.«$default».al == none

private def columnClauses (mutate : Nat → Lang.Il.prem → Lang.Il.prem)
    (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name tps ps ret clauses alternative hints =>
    let clauses := clauses.map fun clause =>
      let (arguments, output, premises) := clause.it
      let (_, premises) := premises.foldl (fun (index, result) premise =>
        match premise.it with
        | .IterPr .. => (index + 1, result ++ [mutate index premise])
        | _ => (index, result ++ [premise])) (0, [])
      { clause with it := (arguments, output, premises) }
    { d with it := .FuncDecD name tps ps ret clauses alternative hints }
  | _ => d

private def optionalColumns := columnClauses (fun _ p => match p.it with
  | .IterPr inner (.mk _ bound bind) => { p with it := .IterPr inner (.mk .Opt bound bind) }
  | _ => p) NanoP4Spec.«$default».al

private def missingExtractedColumn := columnClauses (fun i p =>
  if i == 0 then match p.it with
    | .IterPr inner (.mk kind bound bind) =>
      { p with it := .IterPr inner (.mk kind bound (bind.take 1)) }
    | _ => p
  else p) NanoP4Spec.«$default».al

private def unrelatedColumn := columnClauses (fun i p =>
  if i == 2 then match p.it with
    | .IterPr inner (.mk kind (first :: rest) bind) =>
      { p with it := .IterPr inner (.mk kind
          (Q.v "unrelated" first.typ.it first.iters :: rest) bind) }
    | _ => p
  else p) NanoP4Spec.«$default».al

private def typedElementCall := columnClauses (fun i p =>
  if i == 1 then match p.it with
    | .IterPr inner iteration => match inner.it with
      | .LetPr output call => match call.it with
        | .CallE name _ arguments =>
          let newCall := { call with it := .CallE name [Q.t .BoolT] arguments }
          let newInner := { inner with it := .LetPr output newCall }
          { p with it := .IterPr newInner iteration }
        | _ => p
      | _ => p
    | _ => p
  else p) NanoP4Spec.«$default».al

#guard !Validate.functionListColumns env optionalColumns
#guard !Validate.functionListColumns env missingExtractedColumn
#guard !Validate.functionListColumns env unrelatedColumn
#guard !Validate.functionListColumns env typedElementCall
#guard [optionalColumns, missingExtractedColumn, unrelatedColumn, typedElementCall].all
  (fun d => (Validate.unsupported env [] d).isSome)
private def mutualColumns := columnClauses (fun i p =>
  if i == 1 then match p.it with
    | .IterPr inner iteration => match inner.it with
      | .LetPr output call => match call.it with
        | .CallE _ types arguments =>
          let newCall := { call with it := .CallE (Q.i "columnPeer") types arguments }
          let newInner := { inner with it := .LetPr output newCall }
          { p with it := .IterPr newInner iteration }
        | _ => p
      | _ => p
    | _ => p
  else p) NanoP4Spec.«$default».al

private def columnPeer : Lang.Al.def :=
  let d := NanoP4Spec.«$default».al
  match d.it with
  | .FuncDecD _ tps ps ret clauses alternative hints =>
    { d with it := .FuncDecD (Q.i "columnPeer") tps ps ret clauses alternative hints }
  | _ => d

private def mutualColumnEnv : Env :=
  { env with
    defs := env.defs ++ [columnPeer]
    funcs := env.funcs.insert "columnPeer" ((env.funcs.get? "default").getD
      { kind := .defined, tparams := [], params := [], ret := .BoolT, file := "" }) }

#guard Validate.recursiveFunction mutualColumnEnv mutualColumns
#guard !Validate.singletonRecursiveFunction mutualColumnEnv mutualColumns
#guard !Validate.functionListColumns mutualColumnEnv mutualColumns
#guard (Validate.unsupported mutualColumnEnv [] mutualColumns).isSome

#guard !(Props.requiresColumnsOf NanoP4Spec.Type_eq.al)
#guard !(Props.requiresColumnsOf NanoP4Spec.«$dom_map».al)
#guard !(Props.requiresColumnsOf NanoP4Spec.Var_init.al)

private def columnMember : Props.Member :=
  ((Props.memberOf { env } NanoP4Spec.«$default».al).toOption).getD default
#guard columnMember.requiresColumns
#guard (Validate.forwardProof columnMember).pretty == "refine_al (columns)"

-- A checked operation does not waive source call arity or closed type arguments.
#guard Validate.closedTypedCalls env NanoP4Spec.«$add_var_e».al
#guard (Validate.unsupported env [] NanoP4Spec.«$add_var_e».al).isSome
#guard Validate.unsupported env [] NanoP4Spec.«$add_var_e».al ["add_map"] == none

private def typedCall (types : List Lang.Il.typ) (args : List Lang.Il.arg) : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i "caller") [] [] (Q.t .BoolT)
    [Q.cl [] (Q.e (.CallE (Q.i "find_map") types args) .BoolT) []] none [])

private def callArguments : List Lang.Il.arg :=
  List.replicate 2 (Q.ar (.ExpA (Q.e (.BoolE true) .BoolT)))

#guard Validate.closedTypedCalls env (typedCall [Q.t .BoolT, Q.t .BoolT] callArguments)
#guard !Validate.closedTypedCalls env (typedCall [Q.t .BoolT] callArguments)
#guard !Validate.closedTypedCalls env
  (typedCall [Q.t (.VarT (Q.i "free") []), Q.t .BoolT] callArguments)
#guard !Validate.closedTypedCalls env
  (typedCall [Q.t (.VarT (Q.i "map") []), Q.t .BoolT] callArguments)
#guard !Validate.closedTypedCalls env (typedCall [Q.t .BoolT, Q.t .BoolT] [])
#guard !Validate.closedTypedCalls env
  (typedCall [Q.t .BoolT, Q.t .BoolT]
    [Q.ar (.DefA (Q.i "callback")), Q.ar (.ExpA (Q.e (.BoolE true) .BoolT))])

#guard (Validate.unsupported env [] (typedCall [] callArguments) ["find_map"]).isSome
#guard (Validate.unsupported env []
  (typedCall [Q.t .BoolT, Q.t .BoolT] []) ["find_map"]).isSome

-- Only exact scalar guards enter the subtype driver; nested recursive checks stay excluded.
#guard Validate.scalarTypeChecks env NanoP4Spec.«$typeIR_of_typeDefIR».al
#guard Validate.scalarTypeChecks env NanoP4Spec.Type_ok.al
#guard Validate.unsupported env [] NanoP4Spec.«$typeIR_of_typeDefIR».al == none
#guard Validate.unsupported env [] NanoP4Spec.Type_ok.al == none

private def subtypeCaller (target : Lang.Il.typ) (guard : Lang.Il.subcheck) : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i "caller") [] [] (Q.t .BoolT)
    [Q.cl [] (Q.e (.SubE (Q.e (.BoolE true) .BoolT) target guard) .BoolT) []] none [])

#guard !(Validate.scalarTypeChecks env
  (subtypeCaller (Q.t .BoolT) (.RecurseSC (Q.t .BoolT))))
#guard !(Validate.scalarTypeChecks env
  (subtypeCaller (Q.t (.NumT .NatT)) (.RecurseSC (Q.t (.NumT .IntT)))))
#guard !(Validate.scalarTypeChecks env
  (subtypeCaller (Q.t (.VarT (Q.i "free") [])) (.MixopSC [])))

private def nestedGuard : Lang.Il.exp :=
  let nested := Q.e (.SubE (Q.e (.BoolE true) .BoolT) (Q.t .BoolT)
    (.RecurseSC (Q.t .BoolT))) .BoolT
  Q.e (.TupleE [nested]) (.TupleT [Q.t .BoolT])

#guard !Validate.scalarTypeCheckExp env nestedGuard
#guard Props.requiresTypeRulesExp nestedGuard

-- Recursive functions with subtype checks are admitted; registering type parameters is not.
-- Every builtin has a checked contract, so all enter the caller frontier, as in the emitter.
private def builtins : List String := NanoP4Spec.spec.filterMap fun d => match d.it with
  | .BuiltinDecD name .. => some name.it
  | _ => none

private def recursiveReason (name : String) : Option (Option String) :=
  (NanoP4Spec.spec.find? (fun d => d.it.id.it == name)).bind fun d =>
    if Validate.recursiveFunction env d then
      some (Validate.unsupported env [] d builtins)
    else none

private def supportedRecursive : List String :=
  ["flatten_tableActionList", "flatten_parserStateList", "lvalue_of_expression",
   "expression_of_lvalue", "flatten_nameList", "flatten_argumentList", "flatten_parameterList",
   "find_var_t", "find_var_e"]

#guard supportedRecursive.all fun name => recursiveReason name == some none
-- registration freshness and unused downcast bindings no longer exclude a definition
#guard ["update_var_e", "add_vars_t", "expression_is_lvalue"].all fun name =>
  recursiveReason name == some none
-- Numeric casts compose like other expressions; only an uncertified `bitstr_to_int` blocks.
#guard (Validate.unsupported env [] NanoP4Spec.«$un_op».al ["pow2", "int_to_bitstr"]) ==
  some "calls a builtin"
#guard (Validate.unsupported env [] NanoP4Spec.«$un_op».al builtins).isNone

private def changedOutput (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name tps ps ret [clause] none hints =>
    let (args, _, prems) := clause.it
    { d with it := (.FuncDecD name tps ps ret
      [{ clause with it := (args, Q.e (.BoolE true) .BoolT, prems) }] none hints) }
  | _ => d

private def duplicateParameter (d : Lang.Al.def) : Lang.Al.def :=
  match d.it with
  | .FuncDecD name (tp :: tps) ps ret clauses ec hints =>
    { d with it := .FuncDecD name (tp :: tp :: tps) ps ret clauses ec hints }
  | _ => d

-- A constant output leaves the membership shape; it is then an ordinary pure clause.
#guard !Validate.polymorphicMembership env (changedOutput NanoP4Spec.«$in_set».al)
#guard Validate.polymorphicPure env (changedOutput NanoP4Spec.«$in_set».al)
#guard (Validate.unsupported env [] (duplicateParameter NanoP4Spec.«$in_set».al)).isSome
#guard (Validate.unsupported env [] (changedOutput NanoP4Spec.«$dom_map».al)).isSome
#guard (Validate.unsupported env [] (duplicateParameter NanoP4Spec.«$dom_map».al)).isSome

-- Monomorphic callers inherit registration freshness from their actual callee closure.
#guard (Props.registrationNames env NanoP4Spec.«$add_var_e».al).contains "K" &&
  (Props.registrationNames env NanoP4Spec.«$add_var_e».al).contains "V"
#guard (Props.registrationNames env NanoP4Spec.Var_init.al).contains "K" &&
  (Props.registrationNames env NanoP4Spec.Var_init.al).contains "V"

#guard [NanoP4Spec.«$find_typeDef_t».al, NanoP4Spec.«$add_var_e».al].all fun d =>
  (Props.memberOf { env } d).toOption.any fun m => m.requiresTypeRules &&
    render (Validate.forwardProof m) == "refine_al (subtypes)"

private def membershipMember :=
  (Props.memberOf { env } NanoP4Spec.«$in_set».al).toOption

#guard membershipMember.any fun m => m.valueEquality && m.tparams == ["K"] &&
  (render (Validate.refinementType "NanoP4Spec" m)).contains "Representation.ValueBEq τK" &&
  (render (Reverse.realizationType "NanoP4Spec" m)).contains "ctx.global.tdtbl.get? \"K\" = none"

#guard [NanoP4Spec.«$in_set».al, NanoP4Spec.«$dom_map».al].all fun d =>
  (Props.memberOf { env } d).toOption.any fun m =>
    (Validate.groupTheorems "NanoP4Spec" false [m] []).all fun declaration =>
      ((render declaration).splitOn "\n").all (fun line => line.length ≤ 100)

private def sourceCtx (blocked : Bool) : Interp_al.Ctx.t :=
  { global := Init.global (NanoP4Spec.«$in_set».al ::
      if blocked then [Q.d (.ExternTypD (Q.i "K") [])] else []), «local» := {} }

private def referenceMembership (blocked : Bool) :=
  (Interp_al.Interp.invoke_func 32 { guard := false } false (sourceCtx blocked)
    (Q.i "in_set") [Q.t .BoolT]
    [toValue (NanoP4Spec.set.lbrace_rbrace [true]), toValue true]).run

-- A real global type collision fails before body evaluation, despite related arguments.
#guard match referenceMembership true with
  | some (.error .err) => true
  | _ => false
#guard match referenceMembership false with
  | some (.ok v) => Runtime.Value.eq v (toValue true)
  | _ => false

-- A representation-incoherent parameter dictionary changes generated membership.
#guard match (letI : BEq Bool := ⟨fun _ _ => false⟩
    NanoP4Spec.«$in_set» (NanoP4Spec.set.lbrace_rbrace [true]) true) with
  | some (.ok false) => true
  | _ => false

-- Actual recursive Nat membership retains the source integer-tag boundary.
example (types : Runtime.Value.Match.FindTypdef)
    (functions : Runtime.Value.Match.FindFuncChecked) :
    Interp_al.Interp.checked_type (Runtime.Value.Match.check_checked types functions 1
      (.RecurseSC (Q.t (.NumT .NatT))) (Runtime.Value.Make.int (-1))) =
      (pure false : Eval Bool) := by
  rw [checkedRecurseNat types functions 0 _ rfl]
  rfl

example (types : Runtime.Value.Match.FindTypdef)
    (functions : Runtime.Value.Match.FindFuncChecked) :
    Interp_al.Interp.checked_type (Runtime.Value.Match.check_checked types functions 1
      (.RecurseSC (Q.t (.NumT .NatT))) (Runtime.Value.Make.int 0)) =
      (pure true : Eval Bool) := by
  rw [checkedRecurseNat types functions 0 _ rfl]
  rfl

-- Joint certificates have an immediate explicit audit as well as audited corollaries.
#guard (Props.memberOf { env } NanoP4Spec.Type_eq.al).toOption.any fun member =>
  let declarations := Validate.groupTheorems "NanoP4Spec" true [member] []
  declarations[1]?.any fun declaration =>
    render declaration == "#audit_axioms NanoP4Spec.Type_eq.refines_group"

-- Actual recursive relation iteration is admitted structurally, including its length guard.
#guard Validate.relationListIteration env NanoP4Spec.Type_eq.al
#guard Validate.unsupported env [] NanoP4Spec.Type_eq.al == none
#guard Validate.unsupported env [] NanoP4Spec.ParameterType_eq.al == none

private def parameterType : Lang.Il.typ' := Q.varT "parameterIR" []
private def boundParameters : List Lang.Il.var :=
  [Q.v "left" parameterType [], Q.v "right" parameterType []]

private def parameter (name : String) : Lang.Il.exp := Q.e (.VarE (Q.i name)) parameterType

private def listLength (name : String) : Lang.Il.exp :=
  Q.e (.LenE (Q.e (.IterE (parameter name)
    (.mk .List [Q.v name (.IterT (Q.t parameterType) .List) []]))
    (.IterT (Q.t parameterType) .List))) (.NumT .NatT)

private def lengthGuard : Lang.Il.prem :=
  Q.pr (.IfPr (Q.e (.CmpE .EqOp .BoolT (listLength "left") (listLength "right")) .BoolT))

private def parameterHold : Lang.Il.prem :=
  Q.pr (.IfHoldPr (Q.i "ParameterType_eq")
    (.Infix (.Arg (parameter "left")) (Q.a .Tilde2) (.Arg (parameter "right"))))

private def iteration (kind : Lang.Il.iter) (bound bind : List Lang.Il.var) : Lang.Il.prem :=
  Q.pr (.IterPr parameterHold (.mk kind bound bind))

#guard Validate.relationIterationPrem env [lengthGuard] (iteration .List boundParameters [])
#guard !Validate.relationIterationPrem env [] (iteration .List boundParameters [])
#guard !Validate.relationIterationPrem env [lengthGuard] (iteration .Opt boundParameters [])
#guard !Validate.relationIterationPrem env [lengthGuard]
  (iteration .List boundParameters [Q.v "output" parameterType []])
#guard !Validate.relationIterationPrem env [lengthGuard]
  (iteration .List [Q.v "left" parameterType [], Q.v "left" parameterType []] [])
#guard !Validate.relationIterationPrem env [lengthGuard]
  (iteration .List [Q.v "left" .BoolT [], Q.v "right" parameterType []] [])

-- The print-hint hypothesis follows the actual callable closure, not the shared name `id`
-- (a type and a function), and stops at builtins.
#guard Props.reachesPrintHints env NanoP4Spec.«$id».al
#guard Props.reachesPrintHints env NanoP4Spec.Parameters_ok.al
#guard !Props.reachesPrintHints env NanoP4Spec.Type_ok.al
#guard !Props.reachesPrintHints env NanoP4Spec.«$find_map».al

-- Pure polymorphic clauses: no calls, and only conditions over closed types; shadowing a
-- global type is rejected.
#guard Validate.polymorphicPure env NanoP4Spec.«$empty_map».al
#guard Validate.polymorphicPure env NanoP4Spec.«$ite».al
#guard !Validate.polymorphicPure env NanoP4Spec.«$add_map».al
#guard !Validate.polymorphicPure env NanoP4Spec.«$empty_frame».al

-- Chained updates and optional unwrapping select the structural preset; one update does not.
#guard Props.requiresStructureRulesOf NanoP4Spec.«$inherit_e».al
#guard Props.requiresStructureRulesOf NanoP4Spec.«$make_evalContext».al
#guard !Props.requiresStructureRulesOf NanoP4Spec.«$enter_e».al

-- A plain alias's encoder converts a codec's explicit relation to the resolved instance.
#guard (SourceEntry.aliasEncoders env (Q.t (Q.varT "expression" []))).contains
  "NanoP4Spec.argument.toValue"
#guard SourceEntry.aliasEncoders env (Q.t (Q.varT "typeIR" [])) == []

end P4SpecTecTest.Codegen.ForwardCertificates
