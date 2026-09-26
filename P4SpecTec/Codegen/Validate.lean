import P4SpecTec.Codegen.Props

/-!
Refinement theorems (design section 5.1, rung 3): per definition `d`, the
statement that the AL interpreter run on the quoted definition `d.al`
refines the generated code, discharged by `refine_al`
(`Tactic/Refine.lean`). A recursion group gets one theorem by strong
induction on the interpreter's fuel, with one conjunct per member, and a
corollary per member. The fragment the tactic covers is decided here,
syntactically (`unsupported`): a definition outside it gets no theorem
and is listed in the generated module with its reason, so that nothing is
`sorry`ed and the coverage is visible.
-/

namespace P4SpecTec.Codegen.Validate

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types
open P4SpecTec.Codegen.Exp
open P4SpecTec.Codegen.Funcs
open P4SpecTec.Codegen.Props

/-! ## The fragment -/

/-- The first expression form outside the fragment, in `e`, if any. -/
partial def unsupportedExp (e : exp) : Option String :=
  let here : Option String := match e.it with
    | .UpCastE .. => some "upcast"
    | .DownCastE .. => some "downcast"
    | .SubE .. => some "subtype check"
    | .MemE .. => some "membership"
    | .IdxE .. => some "indexing"
    | .SliceE .. => some "slicing"
    | .UpdE _ p _ => if (dotPath p).isSome then none else some "path update with indexing"
    | .IterE .. => if (iterVar? e).isSome then none else some "iterated expression"
    | .CallE _ targs _ => if targs.isEmpty then none else some "call with type arguments"
    | _ => none
  match here with
  | some r => some r
  | none => (pairsOfExp.children e).findSome? unsupportedExp

/-- The first premise form outside the fragment, in `p`, if any. -/
partial def unsupportedPrem (p : prem) : Option String :=
  match p.it with
  | .IterPr .. => some "iterated premise"
  | _ => (expsOfPrem p).findSome? unsupportedExp

/-- Why `d` is outside the fragment, if it is. -/
def unsupported (env : Env) (externs : List String) (d : Lang.Al.def) : Option String := Id.run do
  if env.mode == .freshState then return some "stateful refinement is not implemented"
  let calls := callsOfDef d
  if calls.any externs.contains then return some "calls an extern"
  if calls.any fun c => match env.funcs.get? c with
      | some info => info.kind == .builtin
      | none => false then return some "calls a builtin"
  let prems : List prem := match d.it with
    | .RelD _ _ _ groups eg _ =>
      groups.flatMap (fun g =>
        let (_, (_, _, ps), paths) := g.it
        ps ++ paths.flatMap fun (_, ps, _) => ps) ++ (match eg with
        | some e => let (_, (_, _, ps), (_, ps', _)) := e.it; ps ++ ps'
        | none => [])
    | .FuncDecD _ _ _ _ clauses ec _ =>
      clauses.flatMap (fun c => let (_, _, ps) := c.it; ps) ++ (match ec with
        | some c => let (_, _, ps) := c.it; ps
        | none => [])
    | .TableDecD _ _ _ rows _ => rows.flatMap fun r => let (_, _, _, ps) := r.it; ps
    | _ => []
  match d.it with
  | .RelD _ _ _ _ (some _) _ => return some "else group"
  | .FuncDecD _ tparams params _ _ _ _ =>
    if !tparams.isEmpty then return some "type parameters"
    if params.any fun p => match p.it with | .DefP .. => true | _ => false then
      return some "function-typed parameter"
  | .TableDecD _ params .. =>
    if params.any fun p => match p.it with | .DefP .. => true | _ => false then
      return some "function-typed parameter"
  | .RelD .. => pure ()
  | _ => return some "not a definition with a body"
  if let some r := prems.findSome? unsupportedPrem then return some r
  if let some r := (expsOfDef d).findSome? unsupportedExp then return some r
  none

/-! ## Statements -/

/-- The value relation of a member's results: `Rel` for a function, the
outputs against the tuple's values for a relation. -/
def resultRel (m : Member) : Format :=
  if !m.isRel then Format.text "Rel"
  else
    let vals := match m.nOuts with
      | 0 => []
      | 1 => [Format.text "toValue o"]
      | n => (projections n).map fun p => Format.text ("toValue o" ++ p)
    let binder := if m.nOuts == 0 then "(_ : Unit)" else "(o : " ++ (render m.ret.fmt) ++ ")"
    Format.paren (Format.text ("fun vs " ++ binder ++ " => Outs vs [") ++
      Format.joinSep vals (Format.text ", ") ++ "]")

/-- The interpreter's invocation of the member on values `v0, v1, ...`. -/
def invocation (m : Member) : Format :=
  let vs := (List.range m.params.length).map fun i => s!"v{i}"
  let list := "[" ++ ", ".intercalate vs ++ "]"
  let head := if m.isRel then "Interp_al.Interp.invoke_rel" else "Interp_al.Interp.invoke_func"
  let targs := if m.isRel then Format.nil else Format.line ++ Format.text "[]"
  Format.paren (Format.group (Format.nest 2 (Format.text (head ++ " fuel cfg internal ctx") ++
    Format.line ++ Format.text s!"(Q.i {m.id.quote})" ++ targs ++ Format.line ++
    Format.text list)))

/-- The generated computation. -/
def generated (m : Member) : Format :=
  let ps := paramNames m.params.length
  Format.paren (Format.text "ExceptT.mk " ++ (Term.call m.defName (ps.map Term.atom)).arg)

/-- The `Refines` conclusion. -/
def conclusion (m : Member) : Format :=
  Format.group (Format.nest 2 (Format.text "Refines " ++ resultRel m ++ Format.line ++
    invocation m ++ Format.line ++ generated m))

/-- The binders after the fuel: the configuration, the context, the
values, the generated values and their relations. -/
def binders (lib : String) (m : Member) : Format :=
  let n := m.params.length
  let vs := (List.range n).map fun i => s!"v{i}"
  let ps := paramNames n
  let values := if n == 0 then Format.nil
    else Format.line ++ Format.text ("(" ++ " ".intercalate vs ++ " : Lang.Il.value)")
  let rels := Format.join ((List.range n).map fun i =>
    Format.line ++ Format.text s!"(h{i} : Rel v{i} {ps.getD i ""})")
  Format.text "(cfg : Interp_al.Interp.Config) (ctx : Interp_al.Ctx.t) (internal : Bool)" ++
    Format.line ++ Format.text "(hguard : cfg.guard = false) (hfenv : ctx.local.fenv = [])" ++
    Format.line ++ Format.text s!"(hspec : HoldsSpec {lib}.spec ctx.global)" ++
    values ++ paramBinders m.params ++ rels

/-- The statement of a member inside a group theorem, for a fuel `fuel`. -/
def groupStatement (lib : String) (m : Member) : Format :=
  let n := m.params.length
  let vs := (List.range n).map fun i => s!"v{i}"
  let ps := paramNames n
  let values := if n == 0 then Format.nil
    else Format.text ("(" ++ " ".intercalate vs ++ " : Lang.Il.value)")
  let params := Format.join ((ps.zip m.params).map fun (p, t) =>
    Format.line ++ Format.text ("(" ++ p ++ " : ") ++ t.fmt ++ ")")
  let rels := Format.join ((List.range n).map fun i =>
    Format.line ++ Format.text s!"Rel v{i} {ps.getD i ""} →")
  Format.paren (Format.group (Format.nest 2 (
    Format.text "∀ (cfg : Interp_al.Interp.Config) (ctx : Interp_al.Ctx.t) (internal : Bool)," ++
    Format.line ++ Format.text s!"cfg.guard = false → ctx.local.fenv = [] →" ++
    Format.line ++ Format.text s!"HoldsSpec {lib}.spec ctx.global →" ++
    (if n == 0 then Format.nil else Format.line ++ Format.text "∀ " ++ values ++ params ++ ",") ++
    rels ++ Format.line ++ conclusion m)))

/-- The arguments a corollary passes on to the group statement, each
after a break point. -/
def corollaryArgs (m : Member) : Format :=
  let n := m.params.length
  let vs := (List.range n).map fun i => s!"v{i}"
  let hs := (List.range n).map fun i => s!"h{i}"
  Format.joinSep ((["cfg", "ctx", "internal", "hguard", "hfenv", "hspec"] ++ vs ++ paramNames n ++
    hs).map Format.text) Format.line

/-- The audit of a theorem's axioms. -/
def audit (name : String) : Format := Format.text ("#audit_axioms " ++ name)

/-- The theorems of a group, or the reasons its members have none. -/
def groupTheorems (lib : String) (recursive : Bool) (members : List Member)
    (reasons : List (String × String)) : List Format := Id.run do
  if !reasons.isEmpty then
    -- one line per definition and reason, grouped by definition
    let ids := (reasons.map (·.1)).eraseDups
    return ids.map fun i =>
      let rs := (reasons.filter (·.1 == i)).map (·.2)
      Format.text s!"-- no refinement theorem: {i}" ++
        Format.nest 4 (Format.join (rs.map fun r => Format.text ("\n--   " ++ r)))
  if members.isEmpty then return []
  if !recursive then
    return members.flatMap fun m =>
      [Format.group (Format.nest 4 (Format.text ("theorem " ++ m.localName.replace ".run" "" ++
          ".refines") ++ Format.line ++ Format.text "(fuel : Nat)" ++ Format.line ++
          binders lib m ++ " :" ++ Format.line ++ conclusion m ++ " :=")) ++
        Format.nest 2 (Format.line ++ Format.text "by refine_al"),
       audit (m.defName.replace ".run" "" ++ ".refines")]
  let first := members.head!
  let groupName := first.localName.replace ".run" "" ++ ".refines_group"
  let stmts := members.map (groupStatement lib)
  let proofs := if members.length == 1 then "refine_al"
    else "exact ⟨" ++ ", ".intercalate (members.map fun _ => "by refine_al") ++ "⟩"
  let groupThm := Format.group (Format.nest 4 (Format.text ("theorem " ++ groupName ++ " :") ++
      Format.line ++ Format.text "∀ (fuel : Nat)," ++
      Format.nest 2 (Format.line ++ Format.joinSep stmts (Format.text " ∧" ++ Format.line)) ++
      " := by")) ++
    Format.nest 2 (Format.line ++ Format.text "intro fuel" ++ Format.line ++
      Format.text "induction fuel using Nat.strongRecOn with" ++ Format.line ++
      Format.text s!"| ind fuel ih => {proofs}")
  let mut out := [groupThm]
  let n := members.length
  for (m, k) in members.zip (List.range n) do
    let proj := String.join ((List.range k).map fun _ => ".2") ++ (if k < n - 1 then ".1" else "")
    let name := m.localName.replace ".run" "" ++ ".refines"
    out := out ++ [Format.group (Format.nest 4 (Format.text ("theorem " ++ name) ++
        Format.line ++ Format.text "(fuel : Nat)" ++ Format.line ++ binders lib m ++ " :" ++
        Format.line ++ conclusion m ++ " :=")) ++
      Format.nest 2 (Format.line ++ Format.group (Format.nest 2 (
        Format.text s!"({lib}.{groupName} fuel){proj}" ++ Format.line ++ corollaryArgs m))),
      audit (m.defName.replace ".run" "" ++ ".refines")]
  out

end P4SpecTec.Codegen.Validate
