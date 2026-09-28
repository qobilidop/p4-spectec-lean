import P4SpecTec.Codegen.Certificates.ProducerTotal

/-!
Source admission at call sites whose actual argument carriers are entirely admitted.
The source call signatures, type arguments and expression notes are checked together.
Calls involving a restricted runtime carrier require a separate preservation proof.
-/

namespace P4SpecTec.Codegen.CallAdmission

open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Refine

private def arguments (env : Env) (expected : List typ') (actual : List exp) :
    Except String (List typ) := do
  unless expected.length == actual.length do throw "call admission argument arity differs"
  for (type, value) in expected.zip actual do
    unless Types.typEq (env.resolveDeep type) (env.resolveDeep value.note) do
      throw "call admission argument note differs from its instantiated callee signature"
  pure (expected.map Q.t)

private partial def expression (env : Env) (e : exp) : Except String (List typ) := do
  let here ← match e.it with
    | .CallE name types args => do
      let some callee := env.funcs[name.it]? | throw "call admission has an unknown callee"
      unless callee.tparams.length == types.length do
        throw "call admission type-argument arity differs"
      let bindings := callee.tparams.zip (types.map (·.it))
      let expected ← callee.params.mapM fun p => match p with
        | .ExpP type => pure (Env.substTyp bindings type.it)
        | _ => throw "call admission needs first-order callee arguments"
      let actual ← args.mapM fun a => match a.it with
        | .ExpA e => pure e
        | _ => throw "call admission needs first-order actual arguments"
      arguments env expected actual
    | _ => pure []
  let nested ← (Exp.pairsOfExp.children e).mapM (expression env)
  pure (here ++ nested.flatten)

private partial def premise (env : Env) (p : prem) : Except String (List typ) := do
  let here ← match p.it with
    | .RulePr name tree _ | .IfHoldPr name tree | .IfNotHoldPr name tree => do
      let some callee := env.rels[name.it]? | throw "call admission has an unknown relation"
      unless callee.inputs.all (· < callee.args.length) &&
          callee.inputs.eraseDups.length == callee.inputs.length do
        throw "call admission relation modes are invalid"
      let actual := Mixfix.args tree
      let _ ← arguments env callee.args actual
      pure (Exp.splitArgs callee.inputs (callee.args.map Q.t)).1
    | .IterPr body _ => premise env body
    | _ => pure []
  let nested ← (Exp.expsOfPrem p).mapM (expression env)
  pure (here ++ nested.flatten)

private def premises (d : Lang.Al.def) : Except String (List prem) := do
  match d.it with
  | .FuncDecD _ [] params _ clauses fallback _ =>
    unless params.all (fun p => match p.it with | .ExpP _ => true | _ => false) do
      throw "call admission does not assume contracts for locally bound callbacks"
    unless (clauses ++ fallback.toList).all (fun c => c.it.1.all
        (fun a => match a.it with | .ExpA _ => true | _ => false)) do
      throw "call admission needs first-order clause arguments"
    pure ((clauses ++ fallback.toList).flatMap (·.it.2.2))
  | .RelD _ _ _ groups fallback _ =>
    pure ((groups.flatMap fun group => group.it.2.1.2.2 ++
      group.it.2.2.flatMap (·.2.1)) ++
      fallback.toList.flatMap (fun group => group.it.2.1.2.2 ++ group.it.2.2.2.1))
  | _ => throw "call admission needs a closed bodied function or relation"

/-- Exact source argument types at every call, checked against instantiated callee signatures. -/
def argumentTypes (env : Env) (d : Lang.Al.def) : Except String (List typ) := do
  let calls ← (Exp.expsOfDef d).mapM (expression env)
  let relations ← (← premises d).mapM (premise env)
  pure ((calls.flatten ++ relations.flatten).foldl (init := []) fun types t =>
    if types.any (fun old => Types.typEq old.it t.it) then types else types ++ [t])

/-- A checked conjunction admitting every native value of every actual call argument type. -/
structure Plan where
  /-- Exact compiled call-domain proposition. -/
  type : String
  /-- Audited generated theorem. -/
  declarations : String
  /-- Codec and totality sidecars required by its proof. -/
  dependencies : List String

/-- Emit universal argument admission only from independently proved carrier totals. Calls
without arguments admit the empty conjunction, `True`. -/
def plan (env : Env) (d : Lang.Al.def)
    (known : String → Option RepresentationTotals.TotalContract) : Except String Plan := do
  unless env.mode == .pure do throw "call admission needs the pure profile"
  let types ← argumentTypes env d
  let fields ← types.mapM
    (RepresentationFields.resolve env (fun n => (known n).map (·.nominal)))
  let totals ← types.mapM (RepresentationTotals.fieldProof env known)
  let statements ← (types.zip fields).mapM fun (type, field) => do
    pure (s!"(∀ x : ({field.carrier}), " ++ (← Producer.admission env type "x") ++ ")")
  let proofs := (types.zip (fields.zip totals)).map fun (type, field, total) =>
    "(fun x => (@Representation.Codec.encodingValid (" ++ field.carrier ++ ") ⟨" ++
    field.encoder ++ "⟩ ⟨" ++ field.decoder ++ "⟩ (" ++ RepresentationFields.source env type ++
    ") (" ++ field.admitted ++ ") (" ++ field.codec ++ ")) x ((" ++ total ++ ") x))"
  let owner := match d.it with
    | .RelD .. => Names.relName d.it.id.it
    | _ => Names.funcName d.it.id.it
  let type := " ∧\n".intercalate (statements ++ ["True"])
  let declarations :=
    "/-- All values of the actual call argument carriers are source-valid. -/\n" ++
    s!"theorem {owner}.{env.part "callArgumentsSource"} :\n    " ++ type.replace "\n" "\n    " ++
    " :=\n  " ++ (if proofs.isEmpty then "trivial" else
      "⟨" ++ ", ".intercalate (proofs ++ ["trivial"]) ++ "⟩") ++ "\n" ++
    s!"#audit_axioms {owner}.{env.part "callArgumentsSource"}\n"
  pure { type, declarations := boundedLines declarations
         dependencies := (fields.flatMap (·.dependencies)).eraseDups }

end P4SpecTec.Codegen.CallAdmission
