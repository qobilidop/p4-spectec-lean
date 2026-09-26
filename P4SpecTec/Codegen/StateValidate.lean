import P4SpecTec.Codegen.Validate

/-!
Bounded exact-state refinement emission. Eligibility is deliberately separate
from executable support: excluded definitions receive explicit reasons, while
eligible proofs must elaborate and pass the generated axiom audit.
-/

namespace P4SpecTec.Codegen.StateValidate

open Std (Format)
open P4SpecTec.Lang.Il P4SpecTec.Lang.Al P4SpecTec.Codegen.Props

/-- The initial stateful refinement fragment has direct scalar ABI types only. -/
def scalar : typ' → Bool
  | .BoolT | .NumT .NatT | .NumT .IntT | .TextT => true
  | _ => false

/-- Reject expression families not yet exercised by stateful refinement automation. -/
partial def unsupportedExp (e : exp) : Option String :=
  let here := match e.it with
    | .VarE .. | .BoolE .. | .NumE .. | .TextE .. => none
    | .BinE .DivOp .NatT ⟨.NumE _, _, _⟩ ⟨.NumE _, _, _⟩ => none
    | .CallE _ ts args =>
      if !ts.isEmpty then some "call with type arguments"
      else if args.any (fun a => match a.it with | .DefA .. => true | _ => false) then
        some "function-valued argument"
      else none
    | _ => some "expression outside initial scalar stateful refinement fragment"
  here.orElse fun _ => (Exp.pairsOfExp.children e).findSome? unsupportedExp

/-- Only scalar binding, boolean checks, and debug evaluation are initially supported. -/
def unsupportedPrem (p : prem) : Option String :=
  match p.it with
  | .LetPr l r =>
    match l.it with
    | .VarE .. => (unsupportedExp l).orElse fun _ => unsupportedExp r
    | _ => some "nonvariable let pattern"
  | .IfPr e | .DebugPr e => unsupportedExp e
  | _ => some "premise outside initial stateful function refinement fragment"

/-- Eligibility does not imply that any called definition has a theorem;
the production caller must propagate exclusions through the dependency graph. -/
def unsupported (env : Env) (externs : List String) (d : Lang.Al.def) : Option String := Id.run do
  if env.mode != .freshState then return some "not an explicit-state specification"
  if (Exp.callsOfDef d).any externs.contains then return some "calls an extern"
  for c in Exp.callsOfDef d do
    if let some info := env.funcs.get? c then
      if info.kind == .builtin && c != "fresh_typeId" then return some "calls another builtin"
  match d.it with
  | .BuiltinDecD i ts ps t _ =>
    let textResult := match t.it with | .TextT => true | _ => false
    if i.it == "fresh_typeId" && ts.isEmpty && ps.isEmpty && textResult then
      return none
    return some "builtin other than zero-argument fresh_typeId"
  | .FuncDecD _ ts ps t cs ec _ =>
    if !ts.isEmpty then return some "type parameters"
    if !scalar t.it then return some "nonscalar result"
    for p in ps do
      match p.it with
      | .ExpP t => if !scalar t.it then return some "nonscalar parameter"
      | _ => return some "function-typed parameter"
    for c in cs ++ ec.toList do
      let (patterns, result, premises) := c.it
      for p in patterns do
        match p.it with
        | .ExpA ⟨.VarE _, _, _⟩ => pure ()
        | _ => return some "nonvariable clause pattern"
      if let some reason := unsupportedExp result then return some reason
      if let some reason := premises.findSome? unsupportedPrem then return some reason
    return none
  | _ => return some "not a scalar function definition"

/-- State-aware theorem binders preserve the pure generator's parameter layout. -/
def binders (lib : String) (m : Member) : Format :=
  let n := m.params.length
  let vs := (List.range n).map fun i => s!"v{i}"
  let ps := Funcs.paramNames n
  let values := if n == 0 then Format.nil
    else Format.line ++ Format.text ("(" ++ " ".intercalate vs ++ " : Lang.Il.value)")
  let rels := Format.join ((List.range n).map fun i =>
    Format.line ++ Format.text s!"(h{i} : Rel v{i} {ps.getD i ""})")
  Format.text "(cfg : Interp_al.Interp.Config StateEval)" ++ Format.line ++
    Format.text "(ctx : Interp_al.Ctx.t) (internal : Bool)" ++
    Format.line ++ Format.text "(hguard : cfg.guard = false) (hfenv : ctx.local.fenv = [])" ++
    Format.line ++ Format.text s!"(hspec : HoldsSpec {lib}.spec ctx.global)" ++
    values ++ paramBinders m.params ++ rels

/-- Every terminating interpreter result must match both the outcome and final state. -/
def conclusion (m : Member) : Format :=
  Format.group (Format.nest 2 (Format.text "StateRefines " ++ Validate.resultRel m ++
    Format.line ++ Validate.invocation m ++ Format.line ++ Validate.generated m))

/-- Emit a scalar theorem, including the actual fresh builtin boundary. -/
def theoremOf (lib : String) (m : Member) : List Format :=
  let proof := if m.id == "fresh_typeId" then
      "by\n  exact freshStateRefinesOfHolds fuel cfg hguard ctx internal hfenv\n" ++
      s!"    (hspec {lib}.{m.localName}.al (by simp [{lib}.spec]))"
    else "by state_refine_al"
  [Format.group (Format.nest 4 (Format.text ("theorem " ++ m.localName ++
      ".state_refines") ++ Format.line ++ Format.text "(fuel : Nat)" ++ Format.line ++
      binders lib m ++ " :" ++ Format.line ++ conclusion m ++ " :=")) ++
      Format.nest 2 (Format.line ++ Format.text proof),
    audit (m.defName ++ ".state_refines")]

/-- Recursive groups remain explicitly excluded in this bounded increment. -/
def groupTheorems (lib : String) (recursive : Bool) (members : List Member)
    (reasons : List (String × String)) : List Format :=
  if !reasons.isEmpty then
    reasons.map fun (name, reason) =>
      Format.text s!"-- no state refinement theorem: {name}: {reason}"
  else if recursive then
    members.map fun m => Format.text s!"-- no state refinement theorem: {m.id}: recursive group"
  else members.flatMap (theoremOf lib)

end P4SpecTec.Codegen.StateValidate
