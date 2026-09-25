import Lean.Data.Json.FromToJson
import P4SpecTec.Lang.Al.Json
import P4SpecTec.Codegen.Emit

/-!
Full-spec reconnaissance without weakening the generator's rejection policy.
Each callable and subtype bridge is probed independently with the real emitter;
successful text emission is not a claim that Lean elaborates it. SCCs and the
syntactic refinement frontier use the generator's own dependency routines.
The deterministic JSON report can be regenerated or checked in CI.
-/

set_option linter.missingDocs false

open Lean (Json toJson)
open P4SpecTec P4SpecTec.Util.Source P4SpecTec.Lang.Il P4SpecTec.Lang.Al
open P4SpecTec.Codegen

def kind : Lang.Al.def' → String
  | .ExternTypD .. => "ExternTypD" | .TypD .. => "TypD" | .VarD .. => "VarD"
  | .ExternRelD .. => "ExternRelD" | .RelD .. => "RelD" | .ExternDecD .. => "ExternDecD"
  | .BuiltinDecD .. => "BuiltinDecD" | .TableDecD .. => "TableDecD" | .FuncDecD .. => "FuncDecD"

def callable (d : Lang.Al.def) : Bool :=
  match d.it with
  | .FuncDecD .. | .BuiltinDecD .. | .TableDecD .. | .RelD .. => true
  | _ => false

def premsOf (d : Lang.Al.def) : List prem :=
  match d.it with
  | .RelD _ _ _ gs eg _ =>
    gs.flatMap (fun g => g.it.2.1.2.2 ++ g.it.2.2.flatMap (·.2.1)) ++
      (eg.toList.flatMap fun g => g.it.2.1.2.2 ++ g.it.2.2.2.1)
  | .FuncDecD _ _ _ _ cs ec _ => (cs ++ ec.toList).flatMap (·.it.2.2)
  | .TableDecD _ _ _ rs _ => rs.flatMap (·.it.2.2.2)
  | _ => []

partial def premFeatures (p : prem) : List String :=
  match p.it with
  | .IterPr q _ => "iterated premise" :: premFeatures q
  | .IfNotHoldPr .. => ["negative premise"]
  | _ => []

partial def expFeatures (e : exp) : List String :=
  (match e.it with
    | .UpCastE .. => ["upcast"] | .DownCastE .. => ["downcast"]
    | .SubE .. => ["subtype check"] | .MemE .. => ["membership"]
    | .IdxE .. => ["indexing"] | .SliceE .. => ["slicing"]
    | .UpdE _ p _ => if (Exp.dotPath p).isSome then [] else ["path update with indexing"]
    | .IterE .. => if (Exp.iterVar? e).isSome then [] else ["iterated expression"]
    | .CallE _ targs _ => if targs.isEmpty then [] else ["call with type arguments"]
    | _ => []) ++ (Exp.pairsOfExp.children e).flatMap expFeatures

def features (env : Env) (externs : List String) (d : Lang.Al.def) : List String :=
  let calls := Exp.callsOfDef d
  let sig := match d.it with
    | .FuncDecD _ ts ps _ cs ec _ =>
      (if ts.isEmpty then [] else ["type parameters"]) ++
      (if ps.any (fun p => match p.it with | .DefP .. => true | _ => false)
        then ["function-typed parameter"] else []) ++
      (if cs.isEmpty && ec.isNone then ["no clauses"] else [])
    | .RelD _ _ _ _ (some _) _ => ["else group"]
    | _ => []
  (sig ++ (Exp.expsOfDef d).flatMap expFeatures ++ (premsOf d).flatMap premFeatures ++
    (if calls.any externs.contains then ["calls an extern"] else []) ++
    (if calls.any (fun c => (env.funcs.get? c).any (·.kind == .builtin))
      then ["calls a builtin"] else [])).eraseDups

def probe (r : Except String Std.Format) : Json :=
  match r with
  | .error e => Json.mkObj [("error", toJson e)]
  | .ok f =>
    let s := render f
    Json.mkObj [("lines", toJson (s.splitOn "\n").length), ("bytes", toJson s.utf8ByteSize)]

def emitCallable (ctx : Exp.Ctx) (recursive ext : Bool) (d : Lang.Al.def) :
    Except String Std.Format :=
  match d.it with
  | .FuncDecD i ts ps t cs ec _ =>
    Funcs.funcDecl ctx recursive ext i.it (ts.map (·.it)) (ps.map (·.it)) t.it cs ec
  | .BuiltinDecD i ts ps t _ =>
    Funcs.builtinDecl ctx.env i.it (ts.map (·.it)) (ps.map (·.it)) t.it
  | .TableDecD i ps t rs _ =>
    Funcs.tableDecl ctx recursive ext i.it (ps.map (·.it)) t.it rs
  | .RelD i n ins gs eg _ => Rels.relDecl ctx recursive ext i.it n (ins.map (·.toNat)) gs eg
  | _ => .error "not a callable"

def census (spec : Lang.Al.spec) : Json := Id.run do
  let env := Env.ofSpec "P4Spec" spec
  let files := (spec.map Env.fileOf).eraseDups
  let defs := spec.filter callable
  let ids := defs.map (·.it.id.it)
  let byId := Std.HashMap.ofList (defs.map fun d => (d.it.id.it, d))
  let calls (id : String) := ((byId.get? id).toList.flatMap Exp.callsOfDef).eraseDups
  let deps (id : String) := (calls id).filter ids.contains
  let groups := Graph.sccs ids deps
  let externs := spec.filterMap fun d => match d.it with
    | .ExternDecD i .. | .ExternRelD i .. => some i.it
    | _ => none
  let ctx : Exp.Ctx := { env, externs }
  let mut covered : List String := []
  let mut extIds := externs
  let mut reports : List Json := []
  let mut groupReports : List Json := []
  for group in groups do
    let recursive := Graph.isRecursive group deps
    let ext := group.any fun id => (calls id).any extIds.contains
    if ext then extIds := extIds ++ group
    let ds := group.filterMap byId.get?
    let localReasons := ds.filterMap fun d =>
      (Validate.unsupported env externs d).map fun r => s!"{d.it.id.it}: {r}"
    let uncovered := (group.flatMap calls).eraseDups.filter fun c =>
      ids.contains c && !group.contains c && !covered.contains c
    let bodied := ds.filter fun d => match d.it with | .BuiltinDecD .. => false | _ => true
    let eligible := !ext && localReasons.isEmpty && uncovered.isEmpty
    if eligible then covered := covered ++ bodied.map (·.it.id.it)
    groupReports := groupReports ++ [Json.mkObj [
      ("members", toJson group), ("recursive", toJson recursive),
      ("sourceFiles", toJson (ds.map Env.fileOf).eraseDups),
      ("needsExterns", toJson ext), ("refinementEligible", toJson eligible),
      ("localExclusions", toJson localReasons), ("uncoveredCallees", toJson uncovered)]]
    for d in ds do
      let prop := match d.it with
        | .RelD i n ins gs eg _ =>
          probe (Props.relInductive ctx ext i.it n (ins.map (·.toNat)) gs eg)
        | _ => .null
      reports := reports ++ [Json.mkObj [
        ("name", toJson d.it.id.it), ("kind", toJson (kind d.it)),
        ("source", toJson (string_of_region d.at)), ("features", toJson (features env externs d)),
        ("runEmission", probe (emitCallable ctx recursive ext d)), ("propEmission", prop)]]
  let typeDefs := spec.filter fun d => match d.it with
    | .TypD .. | .ExternTypD .. => true | _ => false
  let typeIds := typeDefs.map (·.it.id.it)
  let typeDeps (id : String) := match env.types.get? id with
    | some info => info.deftyp.toList.flatMap Env.deftypRefs |>.eraseDups
    | none => []
  let typeGroups := Graph.sccs typeIds typeDeps
  let typeReports := typeGroups.map fun group =>
    let members := group.filterMap fun id => do
      let info ← env.types.get? id
      let dt ← info.deftyp
      pure (id, info.tparams, dt)
    let recursive := Graph.isRecursive group typeDeps
    -- Emit omits self edges: a singleton inductive needs no mutual wrapper
    -- and its aliases are not unfolded with Types.unfoldAll. Report both.
    let emitterMutual := Graph.isRecursive group fun id => (typeDeps id).filter (· != id)
    let fs := group.filterMap fun id => (env.types.get? id).map (·.file)
    Json.mkObj [("members", toJson group), ("recursive", toJson recursive),
      ("emitterMutualBlock", toJson emitterMutual),
      ("sourceFiles", toJson fs.eraseDups),
      ("declarationLines", toJson (members.map fun (tid, ts, dt) =>
        let unfold := match dt with
          | .PlainT _ => []
          | _ => if emitterMutual then [Types.unfoldAll] else []
        let text := render (Types.typeDecl env unfold tid ts dt)
        (text.splitOn "\n").length).sum)]
  let pairs := Exp.pairsOfSpec env spec
  let bridges := pairs.map fun (s, t) =>
    let result := Types.subtypeDecls env s t
    Json.mkObj [("sub", toJson (Types.typeHead s)), ("sup", toJson (Types.typeHead t)),
      ("subType", toJson (render (Types.typTerm env [] s).fmt)),
      ("supType", toJson (render (Types.typTerm env [] t).fmt)), ("emission", probe result)]
  let kinds := ["TypD", "ExternTypD", "VarD", "FuncDecD", "BuiltinDecD", "ExternDecD",
    "TableDecD", "RelD", "ExternRelD"]
  let printHints := spec.filterMap fun d =>
    let hs := Emit.printHints d
    if hs.isEmpty then none else some (Json.mkObj [
      ("name", toJson d.it.id.it), ("occurrences", toJson hs.length)])
  let fileCounts := files.map fun f => Json.mkObj [
    ("file", toJson f), ("definitions", toJson (spec.filter (Env.fileOf · == f)).length)]
  let counts := kinds.map fun k => (k, toJson (spec.filter (fun d => kind d.it == k)).length)
  return Json.mkObj [
    ("scope", toJson
      "Emission probes and syntactic estimates only; no full-P4 Lean build or proofs"),
    ("definitions", toJson spec.length), ("counts", Json.mkObj counts),
    ("files", toJson fileCounts), ("printHints", toJson printHints),
    ("typeGroups", toJson typeReports), ("callableGroups", toJson groupReports),
    ("callables", toJson reports), ("subtypeBridges", toJson bridges),
    ("refinementEligible", toJson covered),
    ("callableNameCollisions", toJson (ids.filter fun id => ids.count id > 1).eraseDups)]

def main (args : List String) : IO UInt32 := do
  let [input, mode, output] := args
    | IO.eprintln "usage: p4spectec-census <export> --update|--check <report.json>"; return 2
  if mode != "--update" && mode != "--check" then
    IO.eprintln "expected --update or --check"; return 2
  let spec ← Lang.Al.Json.readSpec input
  let report := (census spec).pretty ++ "\n"
  if mode == "--update" then IO.FS.writeFile output report
  else if (← IO.FS.readFile output) != report then
    IO.eprintln s!"stale census: {output}"; return 1
  IO.println s!"[census] {spec.length} definitions; {output} {mode}"
  return 0
