import P4SpecTec.Codegen.Rels
import P4SpecTec.Codegen.Props
import P4SpecTec.Codegen.StateProps
import P4SpecTec.Codegen.Certificates.StateRunSound
import P4SpecTec.Codegen.Reify
import P4SpecTec.Codegen.Certificates.Builtin
import P4SpecTec.Codegen.Certificates.Equality
import P4SpecTec.Codegen.Certificates.Extern
import P4SpecTec.Codegen.Certificates.Forward
import P4SpecTec.Codegen.Certificates.Initialization
import P4SpecTec.Codegen.Certificates.Producer
import P4SpecTec.Codegen.Certificates.ProducerComposition
import P4SpecTec.Codegen.Certificates.ProducerContextProof
import P4SpecTec.Codegen.Certificates.ProducerContextCall
import P4SpecTec.Codegen.Certificates.ProducerUpdateCall
import P4SpecTec.Codegen.Certificates.ProducerDefault
import P4SpecTec.Codegen.Certificates.ProducerTotal
import P4SpecTec.Codegen.Certificates.CallAdmission
import P4SpecTec.Codegen.Certificates.SourceProfile
import P4SpecTec.Codegen.Certificates.Representation
import P4SpecTec.Codegen.Certificates.Reverse
import P4SpecTec.Codegen.Certificates.SourceEntry
import P4SpecTec.Codegen.Certificates.SourceBuiltin
import P4SpecTec.Codegen.Certificates.SourcePolymorphic
import P4SpecTec.Codegen.Graph
import P4SpecTec.Codegen.PrintHints
import P4SpecTec.Codegen.Coverage

/-!
The plan and the modules: definitions are grouped into recursion groups
(types, then subtype bridges, then the `Externs` class, then functions and
relations, each followed by the `Prop` encoding of its relations and
their run-soundness theorems), every group is assigned to the module of
the last spec file it or its dependencies come from, and one module is
written per spec file that has something to say, in spec order, each
importing the previous. Every definition is also quoted (`d.al`). The
refinement theorems of rung 3 (`Codegen/Certificates/Forward.lean`) come after the
spec files: `Refinement/Spec` holds the quoted spec as a list, one module
per recursion group holds that group's theorems and imports the modules
of its callees' theorems (so that Lake rechecks only what changed, and
independent groups in parallel), and `Refinement` gathers them with the
coverage summary. Only these modules import the refinement calculus and
tactic, so editing the tactic leaves the spec modules built. Design
section 4.1 and the deviations "a recursive group spanning files is
emitted in the module of the last file" and "the refinement theorems are
in modules after the spec files".
-/

namespace P4SpecTec.Codegen.Emit

/-- The default heartbeat budget of a certificate module; larger groups add to it per path. -/
def certificateHeartbeats : Nat := 4000000

open Std (Format)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Lang.Al
open P4SpecTec.Codegen.Types
open P4SpecTec.Codegen.Exp
open P4SpecTec.Codegen.Funcs
open P4SpecTec.Codegen.Rels

/-- A generated file. -/
structure Output where
  /-- The path relative to the output directory. -/
  path : String
  /-- The text. -/
  text : String

/-- A unit of the plan. -/
structure Unit where
  /-- The unit's id. -/
  id : String
  /-- The index of the spec file it is emitted into. -/
  file : Nat
  /-- The text. -/
  decls : Format
  /-- Whether it needs the `Externs` class. -/
  externs : Bool := false

/-- The refinement theorems of one recursion group, in their own module. -/
structure RefGroup where
  /-- The module's last name component. -/
  name : String
  /-- The theorems. -/
  decls : Format
  /-- The module names of the groups whose theorems these call. -/
  deps : List String
  /-- A builtin family needs its contracts instead of symbolic-execution tactics. -/
  supportImports : Option (List String) := none
  /-- What the module holds, when not refinement theorems. -/
  what : Option String := none

/-- Shared proof support before selecting a direction's tactic. -/
private def commonProofImports : List String :=
  ["P4SpecTec.Prelude", "P4SpecTec.Tactic.Audit", "P4SpecTec.Refine.Quote",
   "P4SpecTec.Refine.Calc"]

/-- Only the forward symbolic-execution tactic is needed by forward groups. -/
private def forwardProofImports : List String :=
  commonProofImports ++ ["P4SpecTec.Tactic.Refine"]

/-- The reverse tactic imports the forward support it shares transitively. -/
private def reverseProofImports : List String :=
  commonProofImports ++ ["P4SpecTec.Tactic.Realize"]

/-- The rung 3 part of the plan. -/
structure RefPlan where
  /-- The quoted spec, `def spec`. -/
  spec : Format
  /-- The coverage line and the reasons for the definitions without a theorem. -/
  summary : Format
  /-- The covered groups, in dependency order. -/
  groups : List RefGroup
  /-- Per-callable metadata collected at the same decisions that emit proofs. -/
  coverage : List Coverage.Entry
  /-- Type representation claims, separate from callable identities. -/
  representations : List Coverage.Entry

/-- A module name component for a group, from its first definition's id:
letters, digits and `_` only, so that no quoting is needed. -/
def groupModuleName (id : String) : String :=
  let s := String.join (id.toList.map fun c =>
    if c.isAlphanum || c == '_' then c.toString else if c == '\'' then "_p" else "")
  if s.isEmpty || s.front.isDigit then "G" ++ s else s

/-- The header comment every generated file starts with: grep-able lines naming
its generator and inputs. Long provenance descriptions use a continuation comment. -/
def headerLine (lib exportPath file : String) : String :=
  let sourceLine := s!"-- source: {exportPath}, {file}"
  s!"-- GENERATED by p4spectec-gen for {lib}; do not edit, regenerate.\n" ++
    if sourceLine.length ≤ 100 then sourceLine
    else s!"-- source: {exportPath}\n-- artifact: {file}"

/-- Move each top-level `#audit_axioms` command to the end of its namespace or section, before
the next scope command or `mutual` block. An audit waits for its theorem's proof; directly
after the theorem it keeps Lean from elaborating the module's later proofs in parallel with
that one. -/
def hoistAudits (text : String) : String := Id.run do
  let mut out : Array String := #[]
  let mut pending : Array String := #[]
  let mut removed := false
  for line in text.splitOn "\n" do
    if line.startsWith "#audit_axioms " then
      pending := pending.push line
      removed := true
      continue
    -- the audit's blank separator goes with it
    if removed && line.isEmpty && out.back? == some "" then
      removed := false
      continue
    removed := false
    -- a `mutual` block admits no commands, so audits also go ahead of one
    let scope := line == "end" || line.startsWith "end " || line.startsWith "namespace " ||
      line == "section" || line.startsWith "section " || line == "mutual"
    if scope && !pending.isEmpty then
      if out.back? != some "" then out := out.push ""
      out := out ++ pending ++ #[""]
      pending := #[]
    out := out.push line
  unless pending.isEmpty do
    if out.back? == some "" then out := out.pop
    out := out ++ #[""] ++ pending ++ #[""]
  return "\n".intercalate out.toList

/-- The preamble after the imports. -/
def preamble (lib module file : String) : String :=
  String.join [
    s!"/-! # {lib}.{module}\n\nThe rendering of `{file}`.\n",
    "Generated: every definition here mirrors one definition of that file, in\n",
    "order, by the encodings of `docs/design.md`.\n-/\n\n",
    "set_option linter.missingDocs false\nset_option linter.unusedVariables false\n",
    "set_option autoImplicit false\nset_option maxHeartbeats 1000000\n\n",
    "open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine\n\n",
    s!"namespace {lib}\n\n"]

/-- The types named by casts inside an expression. -/
partial def castTypes (e : exp) : List String :=
  Env.typeRefs e.note ++ (match e.it with
    | .UpCastE t _ | .DownCastE t _ | .SubE _ t _ => Env.typeRefs t.it
    | .CallE _ targs _ => targs.flatMap fun t => Env.typeRefs t.it
    | _ => []) ++ (pairsOfExp.children e).flatMap castTypes

/-- The types a definition's signature and body mention. -/
def typesOfDef (d : Lang.Al.def) : List String :=
  let sig := match d.it with
    | .TypD _ _ dt _ => Env.deftypRefs dt.it
    | .VarD _ t _ => Env.typeRefs t.it
    | .ExternRelD _ n _ _ | .RelD _ n _ _ _ _ =>
      (Mixfix.args n.it).flatMap fun t => Env.typeRefs t.it
    | .ExternDecD _ _ ps t _ | .BuiltinDecD _ _ ps t _ | .FuncDecD _ _ ps t _ _ _ =>
      Env.typeRefs t.it ++ (paramTypes (ps.map (·.it))).flatMap Env.typeRefs
    | .TableDecD _ ps t _ _ =>
      Env.typeRefs t.it ++ (paramTypes (ps.map (·.it))).flatMap Env.typeRefs
    | _ => []
  let body := (expsOfDef d).flatMap fun e => Env.typeRefs e.note ++ castTypes e
  sig ++ body

/-- Every type a definition states in full: declared bodies, signatures, expression notes,
casts, type arguments and iteration variables. -/
partial def statedTypes (d : Lang.Al.def) : List typ' :=
  let ofParams (ps : List param) := paramTypes (ps.map (·.it))
  let sig : List typ' := match d.it with
    | .TypD _ _ dt _ => (match dt.it with
      | .PlainT t => [t.it]
      | .StructT fields => fields.map (·.2.it)
      | .VariantT cases => cases.flatMap fun c => (Mixfix.args c.nottyp.it).map (·.it))
    | .VarD _ t _ => [t.it]
    | .ExternRelD _ n _ _ | .RelD _ n _ _ _ _ => (Mixfix.args n.it).map (·.it)
    | .ExternDecD _ _ ps t _ | .BuiltinDecD _ _ ps t _ | .FuncDecD _ _ ps t _ _ _ =>
      t.it :: ofParams ps
    | .TableDecD _ ps t _ _ => t.it :: ofParams ps
    | _ => []
  sig ++ (expsOfDef d).flatMap ofExp ++ (premsOfDef d).flatMap ofPrem
where
  /-- The types an expression states, with its sub-expressions'. -/
  ofExp (e : exp) : List typ' :=
    e.note :: (match e.it with
      | .UpCastE t _ | .DownCastE t _ | .SubE _ t _ => [t.it]
      | .CallE _ targs _ => targs.map (·.it)
      | .IterE _ (.mk _ vars) => vars.map varTyp
      | _ => []) ++ (pairsOfExp.children e).flatMap ofExp
  /-- The iteration variables of a premise, at every depth. -/
  ofPrem (p : prem) : List typ' :=
    match p.it with
    | .IterPr q ip => (ip.vars_bound ++ ip.vars_bind).map varTyp ++ ofPrem q
    | _ => []

/-- A generated tuple is a right-nested product, encoded as one flat IL tuple. Two shapes have
no such form: a single component, which is its component, and a last component that is itself
a tuple, which the product merges into its parent. Neither occurs at the pinned specifications;
reject them instead of emitting a carrier whose encoding differs from the source value.
Types are checked as stated: a generic alias of a tuple instantiated at a tuple in its last
position is not expanded here, and no pinned specification declares such an alias. -/
partial def validateTuples (env : Env) (spec : Lang.Al.spec) :
    Except String _root_.Unit := do
  for d in spec do
    for t in statedTypes d do
      if let some reason := ambiguous t then
        throw s!"{d.it.id.it}: {reason} has no right-nested product carrier"
where
  /-- The first tuple of a type whose product form is ambiguous. -/
  ambiguous : typ' → Option String
    | .TupleT ts =>
      let nested := match ts.getLast? with
        | some last => match env.resolve last.it with
          | .TupleT (_ :: _) => true
          | _ => false
        | none => false
      if ts.length == 1 then some "a single-component tuple"
      else if nested then some "a tuple whose last component is a tuple"
      else ts.findSome? fun t => ambiguous t.it
    | .IterT t _ => ambiguous t.it
    | .VarT _ ts => ts.findSome? fun t => ambiguous t.it
    | .FuncT _ ts t => (ts ++ [t]).findSome? fun t => ambiguous t.it
    | _ => none

/-- The `print` hints of a definition, for the capability census. -/
def printHints (d : Lang.Al.def) : List String :=
  let hintsOf (hs : List Lang.Il.hint) : List String :=
    hs.filterMap fun h =>
      match h.getObjVal? "it" >>= (·.getObjVal? "hintid") >>= (·.getObjVal? "it") with
      | .ok (.str "print") => some d.it.id.it
      | _ => none
  match d.it with
  | .TypD _ _ dt hs =>
    hintsOf hs ++ (match dt.it with
      | .VariantT cases => cases.flatMap fun c => match c with | .mk _ _ chs => hintsOf chs
      | _ => [])
  | _ => []

/-- Why an explicit-state specification's definitions carry no certificate yet. -/
def statefulReason : String :=
  "explicit-state specification: certificates are not generated yet"

/-- Whether the pure-mode certificates are planned. An explicit-state specification gets
its executable definitions, quotations and state-indexed logical relations, with a state
run-soundness theorem for each relation that reaches no recursive relation through its
premises; every other certificate is recorded as an exclusion, because the certificate
emitters below are stated for the pure ABI. -/
def certified (env : Env) : Bool := env.mode == .pure

/-- Generate the plan for a spec. -/
def plan (env : Env) (spec : Lang.Al.spec) :
    Except String (List Unit × List String × RefPlan) := do
  let certified := certified env
  Types.validateRepresentation env
  Funcs.validateSignatures env
  validateTuples env spec
  let printEnv ← P4.Unparse.hints_of_spec_al spec
  PrintHints.validate env spec printEnv
  let files := (spec.map Env.fileOf).eraseDups
  let fileIdx (f : String) : Nat := (files.idxOf? f).getD 0
  -- Spec namespaces overlap: Nano-P4 has a type `id` and a function `$id`.
  -- A metavariable may also share a name. Keep type and callable lookups separate.
  let typeDefById : Std.HashMap String Lang.Al.def :=
    Std.HashMap.ofList (spec.filterMap fun d => match d.it with
      | .TypD i .. | .ExternTypD i .. => some (i.it, d)
      | _ => none)
  let defById : Std.HashMap String Lang.Al.def :=
    Std.HashMap.ofList (spec.filterMap fun d => match d.it with
      | .RelD i .. | .ExternRelD i .. | .FuncDecD i .. | .BuiltinDecD i ..
      | .TableDecD i .. | .ExternDecD i .. => some (i.it, d)
      | _ => none)
  let typeFile (id : String) : Nat := match typeDefById.get? id with
    | some d => fileIdx (Env.fileOf d)
    | none => 0
  let defFile (id : String) : Nat := match defById.get? id with
    | some d => fileIdx (Env.fileOf d)
    | none => 0
  -- types
  let typeIds := spec.filterMap fun d => match d.it with
    | .TypD i .. | .ExternTypD i _ => some i.it
    | _ => none
  let typeDeps (id : String) : List String := match env.types.get? id with
    | some info => match info.deftyp with
      | some dt => (Env.deftypRefs dt).eraseDups.filter (· != id)
      | none => []
    | none => []
  let typeGroups := Graph.sccs typeIds typeDeps
  let mut units : List Unit := []
  let mut refGroups : List RefGroup := []
  let mut representationEntries : List Coverage.Entry := []
  let representations := if certified then RepresentationCertificates.catalog env else {}
  let knownRepresentation := fun name => do
    (← (← representations[name]?).toOption).nominal
  -- Runtime-profile codecs of the runtime closure, in their own modules beside the source ones.
  let runtimeRepresentations :=
    if certified then RepresentationCertificates.runtimeCatalog env representations else {}
  let runtimeClosure := if certified then RepresentationCertificates.runtimeClosure env else []
  let runtimeModule := fun id => "Representation.Runtime." ++ groupModuleName id
  let runtimeDependency := fun id => match runtimeRepresentations[id]? with
    | some (.ok _) => runtimeModule id
    | _ => "Representation." ++ groupModuleName id
  let runtimeSupport := RepresentationCertificates.supportImports ++
    ["P4SpecTec.Refine.Representation.SourceRuntime"]
  let mut runtimeClosedEmitted := false
  let rt := { env with runtimeProfile := true }
  -- runtime-profile codecs: the runtime catalog's, and every other type's lifted source codec
  let runtimeKnown : String → Option RepresentationFields.NominalContract := fun name =>
    match runtimeRepresentations[name]? with
    | some (.ok plan) => plan.nominal
    | _ => do
      let nominal ← (← (← representations[name]?).toOption).nominal
      let qualified := env.q (Names.typeName name)
      let codec := rt.liftRuntime qualified (qualified ++ ".toValue")
        (qualified ++ ".ofValue") nominal.codec
      pure { nominal with codec }
  let runtimeTotality := fun name => do
    let plan ← match runtimeRepresentations[name]? with
      | some (.ok plan) => some plan
      | _ => (← representations[name]?).toOption
    pure { nominal := ← runtimeKnown name, proof := ← plan.total :
      RepresentationTotals.TotalContract }
  let runtimeModules := fun (ids : List String) =>
    "Representation.Runtime" :: ids.map runtimeDependency
  if !printEnv.isEmpty then
    units := [{ id := "H:print", file := 0, decls := ← PrintHints.tableDecl printEnv }]
  let mut unitOfType : Std.HashMap String Nat := {}   -- type id → unit index
  let mut typeUnitFile : Std.HashMap String Nat := {}
  for group in typeGroups do
    let members := group.filterMap fun id => match env.types.get? id with
      | some info => match info.deftyp with
        | some dt => some (id, info.tparams, dt)
        | none => none
      | none => none
    let externTypes := group.filter fun id => match env.types.get? id with
      | some info => info.deftyp.isNone
      | none => false
    let recursive := Graph.isRecursive group typeDeps
    let unfold := if recursive then [Types.unfoldAll] else []
    let depFiles := group.flatMap fun id => (typeDeps id).map fun d => typeUnitFile.getD d 0
    let file := (group.map typeFile ++ depFiles).foldl max 0
    let externDecls := externTypes.map fun tid =>
      Format.text s!"abbrev {Names.typeName tid} : Type := ExternValue"
    let decls := if recursive then
      let inductives := members.filter fun (_, _, dt) =>
        match dt with | .PlainT _ => false | _ => true
      let block := mutualBlock (inductives.map fun (tid, tparams, dt) =>
        typeDecl env unfold tid tparams dt)
      let aliasDecls := members.filterMap fun (tid, tparams, dt) => match dt with
        | .PlainT _ => some (typeDecl env [] tid tparams dt)
        | _ => none
      joinDecls ([block] ++ aliasDecls)
    else joinDecls (members.map fun (tid, tparams, dt) => typeDecl env [] tid tparams dt)
    let encoders := if members.isEmpty then []
      else [toValueDecls env members, ofValueDecls env members]
    let quotedTypes := group.filterMap fun id => match typeDefById.get? id with
      | some d => some (Reify.quoted (Names.typeName id) d)
      | none => none
    let unitIdx := units.length
    let allDecls := joinDecls (externDecls ++ [decls] ++ encoders ++ quotedTypes)
    let u : Unit := { id := "T:" ++ ",".intercalate group, file := file, decls := allDecls }
    units := units ++ [u]
    for id in group do
      unitOfType := unitOfType.insert id unitIdx
      typeUnitFile := typeUnitFile.insert id file
    for id in group do
      let some d := typeDefById.get? id | throw s!"unknown representation type {id}"
      let mut claims : List Coverage.Claim := []
      let mut exclusions : List Coverage.Exclusion := []
      if !certified then
        representationEntries := representationEntries ++ [{
          id, kind := match d.it with | .ExternTypD .. => "externType" | _ => "type"
          source := Env.fileOf d, group, recursive, dependencies := typeDeps id
          claims
          exclusions := [{ kind := "representation", definition := id, reason := statefulReason }]
          }]
        continue
      match representations[id]?.getD (.error "source codec absent from catalog") with
      | .error reason =>
        exclusions := [{ kind := "representation", definition := id, reason }]
      | .ok representation =>
        let name := "Representation." ++ groupModuleName id
        if refGroups.any (·.name == name) then
          throw s!"representation module name collision: {id}"
        let dependencies := representation.dependencies
        refGroups := refGroups ++ [{
          name, decls := representation.declarations
          deps := dependencies.map (fun id => "Representation." ++ groupModuleName id)
          supportImports := some RepresentationCertificates.supportImports }]
        claims := [{
          name := env.q (Names.typeName id) ++ ".codec"
          kind := "representation", direction := "sourceCodec"
          expectedType := render representation.type }]
        if let some theoremName := representation.total then
          let some nominal := representation.nominal | throw "total admission lacks nominal codec"
          claims := claims ++ [{
            name := theoremName, kind := "admission", direction := "wholeCarrier"
            expectedType := s!"∀ x : {env.q (Names.typeName id)}, ({nominal.admitted}) x" }]
      match runtimeRepresentations[id]? with
      | none => pure ()
      | some (.error reason) =>
        exclusions := exclusions ++ [{ kind := "runtimeRepresentation", definition := id, reason }]
      | some (.ok representation) =>
        if !runtimeClosedEmitted then
          if refGroups.any (·.name == "Representation.Runtime") then
            throw "representation module name collision: Runtime"
          refGroups := refGroups ++ [{
            name := "Representation.Runtime"
            decls := RepresentationCertificates.runtimeClosedDeclarations env
            deps := [], supportImports := some runtimeSupport }]
          runtimeClosedEmitted := true
        let name := runtimeModule id
        if refGroups.any (·.name == name) then
          throw s!"representation module name collision: runtime {id}"
        let owner := if runtimeClosure.contains id then []
          else ["Representation." ++ groupModuleName id]
        refGroups := refGroups ++ [{
          name, decls := representation.declarations
          deps := ["Representation.Runtime"] ++ owner ++
            representation.dependencies.map runtimeDependency
          supportImports := some runtimeSupport }]
        claims := claims ++ [{
          name := env.q (Names.typeName id) ++ ".runtimeCodec"
          kind := "representation", direction := "runtimeCodec"
          expectedType := render representation.type }]
        if let some theoremName := representation.total then
          let some nominal := representation.nominal | throw "total admission lacks nominal codec"
          claims := claims ++ [{
            name := theoremName, kind := "admission", direction := "runtimeWholeCarrier"
            expectedType := s!"∀ x : {env.q (Names.typeName id)}, ({nominal.admitted}) x" }]
      representationEntries := representationEntries ++ [{
        id, kind := match d.it with | .ExternTypD .. => "externType" | _ => "type"
        source := Env.fileOf d, group, recursive, dependencies := typeDeps id
        claims, exclusions }]
  -- subtype bridges
  let pairs := pairsOfSpec env spec
  for (s, t) in pairs do
    let file := ((Env.typeRefs s ++ Env.typeRefs t).map (typeUnitFile.getD · 0)).foldl max 0
    let decls ← subtypeDecls env s t
    let u : Unit := { id := "S:" ++ upName s t, file, decls }
    units := units ++ [u]
  -- externs
  let externDefs := spec.filter fun d => match d.it with
    | .ExternDecD .. | .ExternRelD .. => true
    | _ => false
  let externNames := externDefs.map fun d => d.it.id.it
  let externsUnitFile := (externDefs.map fun d =>
    (typesOfDef d).map (typeUnitFile.getD · 0) ++ [fileIdx (Env.fileOf d)]).flatten.foldl max 0
  if !externDefs.isEmpty then
    let quotedExterns := externDefs.map fun d => match d.it with
      | .ExternRelD i .. => Reify.quoted (Names.relName i.it) d
      | _ => Reify.quoted (Names.funcName d.it.id.it) d
    let u : Unit :=
      { id := "X", file := externsUnitFile,
        decls := joinDecls (externsClass env externDefs :: quotedExterns) }
    units := units ++ [u]
  -- functions and relations
  let funIds := spec.filterMap fun d => match d.it with
    | .FuncDecD i .. | .BuiltinDecD i .. | .TableDecD i .. | .RelD i .. => some i.it
    | _ => none
  let calls (id : String) : List String := match defById.get? id with
    | some d => (callsOfDef d).eraseDups
    | none => []
  let funDeps (id : String) : List String := (calls id).filter funIds.contains
  let funGroups := Graph.sccs funIds funDeps
  let mut unitFile : Std.HashMap String Nat := {}
  let mut needsExt : Std.HashMap String Bool := {}
  -- Extern relations have invocation certificates under the abstract extern contract;
  -- extern functions have no contract yet.
  let externMembers := if certified then externDefs.filterMap (ExternCertificates.member env)
    else []
  let externFunctionNames := externDefs.filterMap fun d => match d.it with
    | .ExternDecD i .. => some i.it
    | _ => none
  let mut coverageEntries : List Coverage.Entry := externDefs.map fun d =>
    let base : Coverage.Entry :=
      { id := d.it.id.it
        kind := match d.it with | .ExternRelD .. => "externRelation" | _ => "externFunction"
        source := Env.fileOf d
        group := [d.it.id.it]
        recursive := false
        dependencies := []
        claims := []
        exclusions := [{ definition := d.it.id.it, reason := "extern" }] }
    match externMembers.find? (·.id == d.it.id.it) with
    | none => base
    | some m => { base with
        exclusions := []
        claims := [
          { name := m.defName ++ ".refines", kind := "refinement"
            direction := "referenceToGenerated"
            expectedType := render (Validate.refinementType env.lib m) },
          { name := m.defName ++ ".realizes", kind := "refinement"
            direction := "generatedToReference"
            expectedType := render (Reverse.realizationType env.lib m) },
          { name := m.defName ++ ".invocations", kind := "externContract"
            direction := "abstractTwoWay"
            expectedType := render (ExternCertificates.invocationType env.lib m) }] }
  -- Only checked builtin contracts enter the caller frontier. The print contract's
  -- empty-hint condition is stated by every caller whose closure reaches it.
  let certifiedBuiltins := if !certified then [] else spec.filterMap fun d =>
    if (BuiltinCertificates.checkSupport env d).isOk then some d.it.id.it else none
  let mut groupModule : Std.HashMap String String := {}   -- covered id → its module
  let mut forwardModule : Std.HashMap String String := {}
  let mut reverseModule : Std.HashMap String String := {}
  let mut coveredIds : List String := []
  let mut reverseCoveredIds : List String := []
  let mut detIds : List String := []
  let mut producerIds : List String := []
  let mut relationModule : Std.HashMap String String := {}   -- relation → its Prop module
  let mut soundModule : Std.HashMap String String := {}      -- relation → its soundness module
  if !externMembers.isEmpty then
    refGroups := refGroups ++ [{
      name := "Externs", decls := joinDecls (ExternCertificates.theorems env.lib externMembers)
      deps := []
      supportImports := some ["P4SpecTec.Prelude", "P4SpecTec.Tactic.Audit",
        "P4SpecTec.Refine.Quote", "P4SpecTec.Refine.Calc", "P4SpecTec.Refine.Extern",
        "P4SpecTec.Tactic.Refine", "P4SpecTec.Tactic.Realize"] }]
    for m in externMembers do
      groupModule := groupModule.insert m.id "Externs"
      forwardModule := forwardModule.insert m.id "Externs"
      reverseModule := reverseModule.insert m.id "Externs"
      coveredIds := coveredIds ++ [m.id]
      reverseCoveredIds := reverseCoveredIds ++ [m.id]
  let ctxBase : Ctx := { env, externs := externNames }
  for group in funGroups do
    let recursive := Graph.isRecursive group funDeps
    let ext := group.any fun id =>
      (calls id).any fun c => externNames.contains c || needsExt.getD c false
    let depFiles := group.flatMap fun id =>
      (calls id).map (fun c => unitFile.getD c 0) ++ (match defById.get? id with
        | some d => (typesOfDef d).map (typeUnitFile.getD · 0)
        | none => [])
    let extFile := if ext then [externsUnitFile] else []
    let file := (group.map defFile ++ depFiles ++ extFile).foldl max 0
    let tmpPrefix := if (group.any fun id => match defById.get? id with
        | some d => (expsOfDef d).any fun e => match e.it with
          | .VarE v => v.it.startsWith "tmp_"
          | _ => false
        | none => false) then "tmp__" else "tmp_"
    let ctx := { ctxBase with tmpPrefix }
    let mut decls : List Format := []
    let mut props : List Format := []
    let mut members : List Props.Member := []
    for id in group do
      let some d := defById.get? id | throw s!"unknown definition {id}"
      let f ← match d.it with
        | .FuncDecD i tparams params ret clauses ec _ =>
          funcDecl ctx recursive ext i.it (tparams.map (·.it)) (params.map (·.it)) ret.it clauses ec
        | .BuiltinDecD i tparams params ret _ =>
          builtinDecl env i.it (tparams.map (·.it)) (params.map (·.it)) ret.it
        | .TableDecD i params ret rows _ =>
          tableDecl ctx recursive ext i.it (params.map (·.it)) ret.it rows
        | .RelD i nottyp inputs groups eg _ =>
          relDecl ctx recursive ext i.it nottyp (inputs.map (·.toNat)) groups eg
        | _ => throw s!"unexpected definition kind for {id}"
      decls := decls ++ [f]
      if !certified then continue
      if let .RelD i nottyp inputs groups eg _ := d.it then
        props := props ++
          [← Props.relInductive ctx ext i.it nottyp (inputs.map (·.toNat)) groups eg]
      members := members ++ [{ ← Props.memberOf ctx d with externs := ext }]
    -- determinism is closed under callees: a relation premise on a
    -- relation without its own determinism theorem leaves outputs open
    members := members.map fun m =>
      if m.isRel && m.detReason.isNone then
        let relCallees := (calls m.id).filter fun c => env.rels.contains c && c != m.id
        match relCallees.find? fun c => !detIds.contains c with
        | some c => { m with detReason := some s!"calls {c}, which has no determinism theorem" }
        | none => m
      else m
    detIds := detIds ++ (members.filter fun m => m.isRel && m.detReason.isNone).map (·.id)
    let theorems := Props.groupTheorems ext recursive members
    -- the quoted definitions, for the refinement theorems (rung 3)
    let quoted := group.filterMap fun id => match defById.get? id with
      | some d => match d.it with
        | .RelD i .. => some (Reify.quoted (Names.relName i.it) d)
        | .FuncDecD i .. | .TableDecD i .. | .BuiltinDecD i .. =>
          some (Reify.quoted (Names.funcName i.it) d)
        | _ => none
      | none => none
    let text := joinDecls ([if recursive then mutualBlock decls else joinDecls decls] ++
      (if props.isEmpty then [] else [mutualBlock props]) ++ theorems ++ quoted)
    let u : Unit :=
      { id := "F:" ++ ",".intercalate group, file := file, decls := text, externs := ext }
    units := units ++ [u]
    for id in group do
      unitFile := unitFile.insert id file
      needsExt := needsExt.insert id ext
    if !certified then
      -- The state-indexed logical relations of the group, in a module beside the chain of
      -- spec modules: one mutual block per recursion group, after the relations it calls.
      let isRel (id : String) : Bool := match defById.get? id with
        | some d => match d.it with | .RelD .. => true | _ => false
        | none => false
      let rels := group.filter isRel
      let mut relationReason : Option String := none
      let mut soundClaims : List (String × Coverage.Claim) := []
      let mut soundReason : Option (String × Option String) := none
      if let some first := rels.head? then
        let callees := (rels.flatMap fun id =>
          (calls id).filter fun c => isRel c && !group.contains c).eraseDups
        let emitted : Except String (List StateProps.Inductives) := rels.mapM fun id => do
          let some d := defById.get? id | throw s!"unknown definition {id}"
          let .RelD i nottyp inputs groups eg _ := d.it | throw s!"{id} is not a relation"
          StateProps.relInductives ctx ext i.it nottyp (inputs.map (·.toNat)) groups eg rels
        match emitted, callees.find? (!relationModule.contains ·) with
        | .error reason, _ => relationReason := some reason
        | _, some callee =>
          relationReason := some s!"premise relation {callee} has no logical relation"
        | .ok inductives, none =>
          let name := "Relation." ++ groupModuleName first
          -- file systems that ignore case would overwrite one module with the other
          if refGroups.any (·.name.toLower == name.toLower) then
            throw s!"relation module name collision: {first}"
          refGroups := refGroups ++ [{
            name, decls := StateProps.Inductives.declarations inductives
            deps := (callees.filterMap relationModule.get?).eraseDups
            supportImports := some ["P4SpecTec.Prelude", "P4SpecTec.Refine.StateRules"]
            what := some s!"state-indexed logical relations, group {first}" }]
          for id in rels do relationModule := relationModule.insert id name
          -- Run-soundness, where symbolic execution of the run suffices: a relation outside
          -- every recursion group whose premises call only relations that have the theorem.
          if recursive then
            soundReason := some
              ("recursive group: state run-soundness is not generated yet", none)
          else if let some callee := callees.find? (!soundModule.contains ·) then
            soundReason := some
              (s!"calls {callee}, which has no state run-soundness theorem", some callee)
          else
            let sound : Except String (Format × Coverage.Claim) := do
              let some d := defById.get? first | throw s!"unknown definition {first}"
              let m := { ← Props.memberOf ctx d with externs := ext }
              pure (joinDecls [← StateProps.runSound ext m,
                  Props.audit (env.q (StateProps.runSoundName m))],
                { name := env.q (StateProps.runSoundName m), kind := "runSoundness"
                  direction := "generatedSuccessToRelation"
                  expectedType := render (← StateProps.runSoundType ext m) })
            match sound with
            | .error reason => soundReason := some (reason, none)
            | .ok (proof, claim) =>
              let soundName := "RunSound." ++ groupModuleName first
              refGroups := refGroups ++ [{
                name := soundName, decls := proof
                deps := name :: (callees.filterMap soundModule.get?).eraseDups
                supportImports := some ["P4SpecTec.Prelude", "P4SpecTec.Tactic.StateRunSound",
                  "P4SpecTec.Tactic.Audit"]
                what := some s!"state run-soundness, relation {first}" }]
              soundModule := soundModule.insert first soundName
              soundClaims := [(first, claim)]
      for id in group do
        let some d := defById.get? id | throw s!"unknown coverage definition {id}"
        let relationExclusion : List Coverage.Exclusion := if !isRel id then [] else
          match relationReason, soundReason with
          | some reason, _ => [{ kind := "logicalRelation", definition := id, reason }]
          | none, some (reason, dependency) =>
            [{ kind := "runSoundness", definition := id, reason, dependency }]
          | none, none => []
        coverageEntries := coverageEntries ++ [{
          id, source := Env.fileOf d, group, recursive, dependencies := calls id
          kind := match d.it with
            | .RelD .. => "relation" | .TableDecD .. => "table" | .BuiltinDecD .. => "builtin"
            | _ => "function"
          claims := (soundClaims.filter (·.1 == id)).map (·.2)
          exclusions := [{ definition := id, reason := statefulReason }] ++ relationExclusion }]
      continue
    -- the refinement theorems of the group (rung 3): the group is covered
    -- when every member is in the fragment and every callee outside the
    -- group is covered
    let reasons : List Coverage.Exclusion := group.filterMap fun id => match defById.get? id with
      | some d => (Validate.unsupported env externFunctionNames d certifiedBuiltins).map fun r =>
        { definition := id, reason := r }
      | none => none
    let uncoveredCallees : List Coverage.Exclusion := group.flatMap fun id =>
      ((calls id).filter fun c => !group.contains c && !coveredIds.contains c &&
        funIds.contains c).map fun c =>
          { definition := id, reason := s!"calls {c}, which has no theorem", dependency := some c }
    let bodied := members.filter fun m => match env.funcs.get? m.id with
      | some info => info.kind != .builtin
      | none => true
    let reasons := if bodied.isEmpty then [] else reasons ++ uncoveredCallees
    -- mutual groups use joint outcome induction over the generated fixed point
    let reverseBlockers : List Coverage.Exclusion :=
      group.flatMap fun id =>
        ((calls id).filter fun c => !group.contains c && !reverseCoveredIds.contains c &&
          funIds.contains c).map fun c =>
            { kind := "realization", definition := id
              reason := s!"calls {c}, which has no reverse theorem", dependency := some c }
    let reverseReasons := reasons ++ reverseBlockers
    -- symbolic execution explores every clause or rule path: the budget of each
    -- certificate grows with the source paths of its group, from the module default
    let paths := bodied.foldl (fun total m =>
      total + ((defById.get? m.id).map (Validate.premiseSequences · |>.length)).getD 1) 0
    let budget := certificateHeartbeats + 1000000 * paths
    let withBudget (declaration : Format) : Format :=
      if budget > certificateHeartbeats && (render declaration).startsWith "theorem" then
        Format.text s!"set_option maxHeartbeats {budget} in" ++ Term.hardLine ++ declaration
      else declaration
    let forwardTheorems := (Validate.groupTheorems env.lib recursive bodied
      (reasons.map fun r => (r.definition, r.reason))).map withBudget
    let reverseTheorems := (Reverse.groupTheorems env.lib recursive bodied
      (reverseReasons.map fun r => (r.definition, r.reason))).map withBudget
    if reasons.isEmpty && !bodied.isEmpty then
      let base := groupModuleName bodied.head!.id
      let aggregateGroups := refGroups.filter fun g =>
        !g.name.startsWith "Forward." && !g.name.startsWith "Reverse."
      let taken := aggregateGroups.map (·.name)
      let name := if taken.contains base then s!"{base}_{aggregateGroups.length}" else base
      let forwardName := "Forward." ++ name
      let reverseName := "Reverse." ++ name
      let deps (modules : Std.HashMap String String) :=
        (group.flatMap fun id => (calls id).filterMap fun c =>
          if group.contains c then none else modules.get? c).eraseDups
      refGroups := refGroups ++ [
        { name := forwardName, decls := joinDecls forwardTheorems
          deps := deps forwardModule, supportImports := some forwardProofImports },
        { name := reverseName, decls := joinDecls reverseTheorems
          deps := deps reverseModule, supportImports := some reverseProofImports },
        { name, decls := Format.nil, deps := [forwardName, reverseName]
          supportImports := some [] }]
      for m in bodied do
        groupModule := groupModule.insert m.id name
        forwardModule := forwardModule.insert m.id forwardName
        if reverseReasons.isEmpty then
          reverseModule := reverseModule.insert m.id reverseName
    for m in members do
      let some d := defById.get? m.id | throw s!"unknown coverage definition {m.id}"
      let kind := match d.it with
        | .RelD .. => "relation"
        | .TableDecD .. => "table"
        | .BuiltinDecD .. => "builtin"
        | _ => "function"
      let mut claims : List Coverage.Claim := []
      let mut exclusions := if kind == "builtin" then
        [{ definition := m.id, reason := "builtin has no generated AL body" }]
        else reasons ++ reverseBlockers
      if m.isRel then
        claims := claims ++ [{
          name := m.defName ++ "_sound", kind := "runSoundness"
          direction := "generatedSuccessToRelation"
          expectedType := render (Props.corollaryType ext m) }]
        if !recursive && m.detReason.isNone then
          claims := claims ++ [{
            name := m.defName.replace ".run" "" ++ ".det"
            kind := "determinism", direction := "relationOutputsUnique"
            expectedType := render (Props.detTheoremType ext m) }]
        else
          exclusions := exclusions ++ [{
            kind := "determinism", definition := m.id
            reason := if recursive then "recursive group"
              else m.detReason.getD "determinism not emitted" }]
      if reasons.isEmpty && kind != "builtin" then
        claims := claims ++ [{
          name := m.defName.replace ".run" "" ++ ".refines"
          kind := "refinement", direction := "referenceToGenerated"
          expectedType := render (Validate.refinementType env.lib m) }]
      if reverseReasons.isEmpty && kind != "builtin" then
        claims := claims ++ [{
          name := m.defName.replace ".run" "" ++ ".realizes"
          kind := "refinement", direction := "generatedToReference"
          expectedType := render (Reverse.realizationType env.lib m) }]
      if reverseReasons.isEmpty && kind != "builtin" then
        match SourceEntry.declarations env d m (some knownRepresentation) with
        | .error reason =>
          exclusions := exclusions ++ [{ kind := "sourceEntry", definition := m.id, reason }]
        | .ok proof =>
          let fields ← SourceEntry.contracts env d (some knownRepresentation)
          let name := "SourceEntry." ++ groupModuleName m.id
          let some pairedModule := groupModule.get? m.id
            | throw s!"source entry has no paired invocation module: {m.id}"
          let dependencies := (fields.flatMap fun (_, field) => field.dependencies).eraseDups
          refGroups := refGroups ++ [{
            name, decls := proof
            deps := pairedModule :: dependencies.map (fun id =>
              "Representation." ++ groupModuleName id)
            supportImports := some RepresentationCertificates.supportImports }]
          claims := claims ++ [{
            name := m.defName.replace ".run" "" ++ ".sourceCorrespondence"
            kind := "sourceEntry", direction := "sourceInputsToTwoWay"
            expectedType := ← SourceEntry.theoremType env d m (some knownRepresentation) }]
      if kind == "function" || kind == "relation" then
        let totality := fun name => do
          let candidate ← (← representations[name]?).toOption
          pure { nominal := ← candidate.nominal, proof := ← candidate.total :
            RepresentationTotals.TotalContract }
        match (if (calls m.id).isEmpty then .error "call admission needs a call site"
            else CallAdmission.plan env d totality) with
        | .error reason =>
          exclusions := exclusions ++ [{ kind := "callAdmission", definition := m.id, reason }]
        | .ok admission =>
          refGroups := refGroups ++ [{
            name := "CallAdmission." ++ groupModuleName m.id
            decls := Format.text admission.declarations
            deps := admission.dependencies.map (fun id =>
              "Representation." ++ groupModuleName id)
            supportImports := some RepresentationCertificates.supportImports }]
          claims := claims ++ [{
            name := m.defName.replace ".run" "" ++ ".callArgumentsSource"
            kind := "callAdmission", direction := "allCallArgumentCarriers"
            expectedType := admission.type }]
        let producerName := m.defName.replace ".run" ""
        let callClaim := fun suffix direction statement =>
          { name := producerName ++ suffix, kind := "callAdmission", direction,
            expectedType := statement : Coverage.Claim }
        let producer : Except String (String × List String × List Coverage.Claim) := do
          if let .ok total := ProducerTotal.plan env d totality then
            return (total.declarations, total.dependencies.map (fun id =>
              "Representation." ++ groupModuleName id), [])
          if let .ok proof := Producer.declarations env d then
            return (proof ++ "\n\n" ++ render (← ProducerUpdateCall.declarations env d), [],
              [callClaim ".recursiveInputsSource" "sourceRecursiveSuffixes"
                (← ProducerUpdateCall.theoremType env d)])
          if let .ok proof := ProducerDefault.declarations env d then return (proof, [], [])
          if let .ok proof := ProducerContextProof.declarations env d then
            let mut declarations := render proof
            let mut dependencies := ← ProducerContextProof.dependencies env d
            let mut callClaims := []
            if let .ok statement := ProducerContextProof.callInputTheoremType env d then
              declarations := declarations ++ "\n\n" ++
                render (← ProducerContextCall.declarations env d totality)
              let insertion ← ProducerContexts.insertPlan env d
              let keys ← RepresentationFields.resolve env
                (fun name => (totality name).map (·.nominal))
                (P4SpecTec.Refine.Q.t (P4SpecTec.Refine.Q.varT insertion.frame.set
                  [insertion.frame.key]))
              dependencies := (dependencies ++ keys.dependencies).eraseDups
              callClaims := [callClaim ".callInputsSource" "sourceContextProjections" statement,
                callClaim ".callArgumentsSource" "sourceContextCalls"
                  (← ProducerContextCall.theoremType env d)]
            return (declarations, dependencies.map (fun id =>
              "Representation." ++ groupModuleName id), callClaims)
          let dependencies ← ProducerComposition.dependencies env d
          unless dependencies.all producerIds.contains do
            throw "source producer composition requires every callee's checked producer"
          return ((← ProducerComposition.declarations env d) ++ "\n\n" ++
            (← ProducerComposition.callAdmissionDeclarations env d),
            dependencies.map (fun id => "Producer." ++ groupModuleName id),
            [callClaim ".callArgumentsSource" "sourceCallPrefixes"
              (← ProducerComposition.callAdmissionType env d)])
        match producer with
        | .error reason =>
          exclusions := exclusions ++ [{ kind := "producer", definition := m.id, reason }]
        | .ok (proof, dependencies, callClaims) =>
          producerIds := producerIds ++ [m.id]
          refGroups := refGroups ++ [{
            name := "Producer." ++ groupModuleName m.id
            decls := Format.text proof
            deps := dependencies
            supportImports := some (RepresentationCertificates.supportImports ++
              ["P4SpecTec.Refine.Producer", "P4SpecTec.Refine.ProducerMap",
                "P4SpecTec.Tactic.Encoding"]) }]
          claims := claims ++ [{
            name := m.defName.replace ".run" "" ++ ".producesSource"
            kind := "producer", direction := "sourceInputsToSourceOutput"
            expectedType := ← Producer.theoremType env d }]
          claims := claims ++ callClaims
      -- Runtime-profile domain evidence, where the source profile's is incomplete. Outside
      -- the runtime closure both profiles have the same values; inside it, evaluation
      -- contexts may hold the runtime-only raw extern after a callback.
      let sourceIncomplete := exclusions.any fun e =>
        ["sourceEntry", "producer"].contains e.kind ||
          (e.kind == "callAdmission" && e.reason != "call admission needs a call site")
      if (kind == "function" || kind == "relation") && reverseReasons.isEmpty &&
          sourceIncomplete && !runtimeClosure.isEmpty then
        let base := m.defName.replace ".run" ""
        match SourceEntry.declarations rt d m (some runtimeKnown) with
        | .error reason =>
          exclusions := exclusions ++ [{ kind := "runtimeSourceEntry", definition := m.id, reason }]
        | .ok proof =>
          let fields ← SourceEntry.contracts rt d (some runtimeKnown)
          let some pairedModule := groupModule.get? m.id
            | throw s!"runtime entry has no paired invocation module: {m.id}"
          refGroups := refGroups ++ [{
            name := "SourceEntry.Runtime." ++ groupModuleName m.id, decls := proof
            deps := pairedModule :: runtimeModules
              (fields.flatMap fun (_, field) => field.dependencies).eraseDups
            supportImports := some runtimeSupport }]
          claims := claims ++ [{
            name := base ++ "." ++ rt.part "sourceCorrespondence"
            kind := "sourceEntry", direction := "runtimeInputsToTwoWay"
            expectedType := ← SourceEntry.theoremType rt d m (some runtimeKnown) }]
        match ProducerTotal.plan rt d runtimeTotality m.externs with
        | .error reason =>
          exclusions := exclusions ++ [{ kind := "runtimeProducer", definition := m.id, reason }]
        | .ok total =>
          refGroups := refGroups ++ [{
            name := "Producer.Runtime." ++ groupModuleName m.id
            decls := Format.text total.declarations, deps := runtimeModules total.dependencies
            supportImports := some runtimeSupport }]
          claims := claims ++ [{
            name := base ++ "." ++ rt.part "producesSource"
            kind := "producer", direction := "runtimeInputsToRuntimeOutput"
            expectedType := ← Producer.theoremType rt d m.externs }]
        if !(calls m.id).isEmpty then
          match CallAdmission.plan rt d runtimeTotality with
          | .error reason =>
            exclusions := exclusions ++
              [{ kind := "runtimeCallAdmission", definition := m.id, reason }]
          | .ok admission =>
            refGroups := refGroups ++ [{
              name := "CallAdmission.Runtime." ++ groupModuleName m.id
              decls := Format.text admission.declarations
              deps := runtimeModules admission.dependencies
              supportImports := some runtimeSupport }]
            claims := claims ++ [{
              name := base ++ "." ++ rt.part "callArgumentsSource"
              kind := "callAdmission", direction := "runtimeCallArgumentCarriers"
              expectedType := admission.type }]
      if kind == "builtin" then
        match BuiltinCertificates.declarations env d with
        | .error reason =>
          exclusions := [{ kind := "builtinContract", definition := m.id, reason }]
        | .ok builtinProofs =>
          let base := groupModuleName m.id
          let aggregateGroups := refGroups.filter fun g =>
            !g.name.startsWith "Forward." && !g.name.startsWith "Reverse."
          let name := if (aggregateGroups.map (·.name)).contains base then
            s!"{base}_{aggregateGroups.length}" else base
          refGroups := refGroups ++ [{
            name, decls := builtinProofs, deps := []
            supportImports := some (BuiltinCertificates.supportImports d) }]
          claims := [{
            name := BuiltinCertificates.dispatchName env d
            kind := "builtinContract", direction := "twoWayDispatch"
            expectedType := render (← BuiltinCertificates.dispatchType env d) }]
          for direction in [BuiltinCertificates.Direction.forward, .reverse] do
            claims := claims ++ [{
              name := BuiltinCertificates.theoremName env d direction
              kind := "refinement"
              direction := if direction == .forward then "referenceToGenerated"
                else "generatedToReference"
              expectedType := render (← BuiltinCertificates.theoremType env d direction) }]
          exclusions := []
          groupModule := groupModule.insert m.id name
          forwardModule := forwardModule.insert m.id name
          reverseModule := reverseModule.insert m.id name
          coveredIds := coveredIds ++ [m.id]
          reverseCoveredIds := reverseCoveredIds ++ [m.id]
      let sourceDomain := if kind == "builtin" then
          SourceBuiltinCertificates.complete env knownRepresentation d
        else SourcePolymorphic.complete env knownRepresentation d
      match sourceDomain with
      | .error reason =>
        exclusions := exclusions ++ [{ kind := "sourceDomain", definition := m.id, reason }]
      | .ok (proof, statement, dependencies) =>
        refGroups := refGroups ++ [{
          name := "SourceDomain." ++ groupModuleName m.id
          decls := Format.text proof
          deps := dependencies.map (fun id => "Representation." ++ groupModuleName id)
          supportImports := some (RepresentationCertificates.supportImports ++
            SourceBuiltinCertificates.supportImports) }]
        claims := claims ++ [{
          name := m.defName.replace ".run" "" ++ ".sourceDomain"
          kind := "sourceDomain", direction := "sourceInputsAndOutput"
          expectedType := statement }]
      coverageEntries := coverageEntries ++ [{
        id := m.id, kind, source := Env.fileOf d
        group, recursive, dependencies := calls m.id, claims, exclusions }]
    if reasons.isEmpty then
      coveredIds := coveredIds ++ bodied.map (·.id)
    if reverseReasons.isEmpty then
      reverseCoveredIds := reverseCoveredIds ++ bodied.map (·.id)
  -- runtime entry of each extern relation: every runtime-valid input is covered, and both
  -- directions hold under the abstract extern contract
  if !runtimeClosure.isEmpty then
    for d in externDefs do
      let some m := externMembers.find? (·.id == d.it.id.it) | continue
      match SourceEntry.declarations rt d m (some runtimeKnown) with
      | .error reason =>
        coverageEntries := coverageEntries.map fun e => if e.id != m.id then e else
          { e with exclusions := e.exclusions ++
            [{ kind := "runtimeSourceEntry", definition := m.id, reason }] }
      | .ok proof =>
        let fields ← SourceEntry.contracts rt d (some runtimeKnown)
        refGroups := refGroups ++ [{
          name := "SourceEntry.Runtime." ++ groupModuleName m.id, decls := proof
          deps := "Externs" :: runtimeModules
            (fields.flatMap fun (_, field) => field.dependencies).eraseDups
          supportImports := some runtimeSupport }]
        let claim : Coverage.Claim := {
          name := m.defName ++ "." ++ rt.part "sourceCorrespondence"
          kind := "sourceEntry", direction := "runtimeInputsToTwoWay"
          expectedType := ← SourceEntry.theoremType rt d m (some runtimeKnown) }
        coverageEntries := coverageEntries.map fun e =>
          if e.id == m.id then { e with claims := e.claims ++ [claim] } else e
  -- the quoted spec, in order, for the refinement theorems
  let quotedNames := spec.filterMap fun d => match d.it with
    | .RelD i .. | .ExternRelD i .. => some (env.q (Names.relName i.it) ++ ".al")
    | .FuncDecD i .. | .TableDecD i .. | .BuiltinDecD i .. | .ExternDecD i .. =>
      some (env.q (Names.funcName i.it) ++ ".al")
    | .TypD i .. | .ExternTypD i .. => some (env.q (Names.typeName i.it) ++ ".al")
    | .VarD .. => none
  if quotedNames.length != quotedNames.eraseDups.length then
    throw "a type and a relation share a name; their quoted definitions would clash"
  -- an explicit chain of `::`: the list macro chunks a long literal into
  -- nested `have`s, which the tactic's membership proofs cannot walk
  let specDecl := Term.defn (Format.text "def spec : List Lang.Al.def")
    (Format.text (" ::\n  ".intercalate quotedNames ++ " ::\n  []"))
  pure (units, files,
    { spec := specDecl, summary := Format.text (Coverage.summary coverageEntries)
      groups := refGroups, coverage := coverageEntries, representations := representationEntries })

private def profileClaims (lib : String) (spec : Lang.Al.spec) : List Coverage.Claim :=
  [{ name := lib ++ ".SourceProfile.variablesIgnored"
     kind := "sourceVariables", direction := "typedOmissionPreservesInitialization"
     expectedType := SourceProfiles.variablesIgnoredType lib },
   { name := lib ++ ".SourceProfile.primitiveRepresentations"
     kind := "primitiveRepresentation", direction := "legalSourceCodecs"
     expectedType := SourceProfiles.primitiveType lib },
   { name := lib ++ ".Environment.initEqOk"
     kind := "tableInitialization", direction := "checkedInitialization"
     expectedType := s!"Interp_al.Ctx.init {lib}.spec = .ok {lib}.Environment.global" },
   { name := lib ++ ".Environment.holdsSpec"
     kind := "tableInitialization", direction := "completeSourceLookups"
     expectedType := s!"Refine.HoldsSpec {lib}.spec {lib}.Environment.global" },
   { name := lib ++ ".Environment.localFenvEmpty"
     kind := "tableInitialization", direction := "noLocalOverrides"
     expectedType := s!"{lib}.Environment.ctx.local.fenv = []" },
   { name := lib ++ ".Environment.initialized"
     kind := "initialization", direction := "certificateEnvironment"
     expectedType := Initialization.initializedType lib spec }]

/-- Recompute coverage through the production planner, without claiming compilation. -/
def coverage (lib exportPath : String) (spec : Lang.Al.spec)
    (representation : Representation := {}) : Except String Coverage.Report := do
  let env := { Env.ofSpec lib spec with representation }
  let (_, _, refinement) ← plan env spec
  pure {
    library := lib, input := exportPath, definitions := refinement.coverage
    representations := refinement.representations
    profiles := if certified env then profileClaims lib spec else [] }


/-- Generate every output file of a library. -/
def generate (lib exportPath : String) (spec : Lang.Al.spec)
    (representation : Representation := {}) : Except String (List Output) := do
  let env := { Env.ofSpec lib spec with representation }
  let certified := certified env
  let (units, files, refinement) ← plan env spec
  let used := (units.map (·.file)).eraseDups.mergeSort (· ≤ ·)
  let specRoot := Names.specRoot files
  let mut outs : List Output := []
  let mut prev : Option String := none
  let mut modules : List String := []
  for i in used do
    let file := files.getD i ""
    let components := Names.moduleComponents file specRoot
    let module := ".".intercalate components
    -- the file path uses the unquoted components: Lake maps `«3.2-bits»` to `3.2-bits.lean`
    let path := "/".intercalate (components.map fun c =>
      if c.startsWith "«" then String.ofList (c.toList.drop 1 |>.dropLast) else c)
    let body := units.filter (·.file == i)
    let declarations := render (joinDecls (body.map (·.decls)))
    let monotonicityImport := if declarations.contains "codegen_monotonicity" then
      "import P4SpecTec.Tactic.Monotonicity\n" else ""
    let proofImports := if certified then
      "import P4SpecTec.Tactic.RunSound\nimport P4SpecTec.Tactic.Audit\n" ++
        "import P4SpecTec.Tactic.Det\n"
      else ""
    let imports := "import P4SpecTec.Prelude\n" ++ proofImports ++
      "import P4SpecTec.Refine.Quote\n" ++ monotonicityImport ++ (match prev with
      | some p => s!"import {lib}.{p}\n"
      | none => "")
    let text := headerLine lib exportPath file ++ "\n" ++ imports ++ "\n" ++
      preamble lib module file ++ declarations ++ s!"\n\nend {lib}\n"
    outs := outs ++ [{ path := s!"{lib}/{path}.lean", text }]
    prev := some module
    modules := modules ++ [module]
  -- the refinement theorems, after every spec file
  let specSupportImports : List String := ["P4SpecTec.Prelude", "P4SpecTec.Refine.Quote"]
  let proofSupportImports := forwardProofImports ++ ["P4SpecTec.Tactic.Realize"]
  let refOptions := String.join [
    "set_option linter.missingDocs false\nset_option linter.unusedVariables false\n",
    "set_option autoImplicit false\n",
    s!"set_option maxHeartbeats {certificateHeartbeats}\n",
    "-- the quoted spec is one deep `::` chain\nset_option maxRecDepth 8192\n\n",
    "open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine\n\n",
    s!"namespace {lib}\n\n"]
  let rung3 := "Rung 3, design section 5.1."
  let refModule (name what : String) (supportImports imports : List String)
      (body : Format) (place : String := rung3) : Output :=
    { path := s!"{lib}/Refinement/{name.replace "." "/"}.lean",
      text := headerLine lib exportPath what ++ "\n" ++
        String.join (supportImports.map fun m => s!"import {m}\n") ++
        String.join (imports.map fun m => s!"import {lib}.{m}\n") ++ "\n" ++
        s!"/-! # {lib}.Refinement.{name}\n\n" ++ "Generated: " ++ what ++
        ".\n" ++ place ++ "\n-/\n\n" ++ refOptions ++
        "\n".intercalate (((render body).splitOn "\n").map (·.trimAsciiEnd.toString)) ++
        s!"\n\nend {lib}\n" }
  outs := outs ++ [refModule "Spec" "the quoted specification as a list" specSupportImports
    prev.toList refinement.spec]
  modules := modules ++ ["Refinement.Spec"]
  -- the shared certificate modules every group imports
  let mut shared : List String := ["Refinement.Spec"]
  if certified then
    if refinement.groups.any (·.name == "Environment") then
      throw "certificate group name Environment conflicts with the initialization module"
    outs := outs ++ [refModule "Environment" "checked reference table initialization"
      ["P4SpecTec.Refine.Environment", "P4SpecTec.Refine.Init"] ["Refinement.Spec"]
      (Initialization.declarations lib spec)]
    if refinement.groups.any (·.name == "SourceProfile") then
      throw "certificate group name SourceProfile conflicts with the source profile module"
    outs := outs ++ [refModule "SourceProfile" "typed schematic source declarations"
      SourceProfiles.supportImports ["Refinement.Spec"]
      (SourceProfiles.declarations spec ++ Format.text "\n\n" ++
        SourceProfiles.primitiveDeclarations lib)]
    if refinement.groups.any (·.name == "Equality") then
      throw "certificate group name Equality conflicts with the equality module"
    let bridgeCanon := (pairsOfSpec env spec).map fun (s, t) => subtypeCanonTheorem env s t
    outs := outs ++ [refModule "Equality" "canonical equality of generated type dictionaries"
      ["P4SpecTec.Refine.Representation.Equality", "P4SpecTec.Refine.ValueShape",
        "P4SpecTec.Tactic.Encoding"]
      ["Refinement.Spec"] (joinDecls (EqualityCertificates.declarations env spec :: bridgeCanon))]
    shared := shared ++ ["Refinement.Environment", "Refinement.SourceProfile",
      "Refinement.Equality"]
    modules := modules ++ shared.drop 1
  for g in refinement.groups do
    let deps := ["Refinement.Spec"] ++ (if certified then ["Refinement.Equality"] else []) ++
      g.deps.map (s!"Refinement.{·}")
    let what := g.what.getD s!"refinement theorems, group {g.name}"
    outs := outs ++ [refModule g.name what
      (g.supportImports.getD proofSupportImports) deps g.decls
      (if g.name.startsWith "Relation." then "Definitions without a theorem, design section 4.1."
        else if g.name.startsWith "RunSound." then "Design section 4.1."
        else rung3)]
    modules := modules ++ [s!"Refinement.{g.name}"]
  let refImports := String.join ((shared ++
    refinement.groups.map (s!"Refinement.{·.name}")).map fun m => s!"import {lib}.{m}\n")
  let refText := headerLine lib exportPath "every file (rung 3)" ++ "\n" ++ refImports ++ "\n" ++
    String.join (if certified then [
      s!"/-! # {lib}.Refinement\n\nThe refinement theorems of rung 3 (design section 5.1), ",
      "one module per\nrecursion group under `Refinement/`, and the definitions without ",
      "a theorem, with\nthe reason. Generated.\n-/\n\n"] else [
      s!"/-! # {lib}.Refinement\n\nThe quoted specification, the state-indexed logical ",
      "relations (one module per\nrecursion group under `Refinement/Relation/`) and the ",
      "state run-soundness theorems\nunder `Refinement/RunSound/`. No AL correspondence ",
      "theorem is generated for an\nexplicit-state specification: every definition is ",
      "listed below without one, with the\nreason; `coverage.json` records the ",
      "run-soundness claims and exclusions. Generated.\n-/\n\n"]) ++
    render refinement.summary ++ "\n"
  outs := outs ++ [{ path := s!"{lib}/Refinement.lean", text := refText }]
  modules := modules ++ ["Refinement"]
  let root := headerLine lib exportPath "all files" ++ "\n" ++
    String.join (modules.map fun m => s!"import {lib}.{m}\n") ++
    s!"\n/-!\n# {lib}\n\nThe rendering of the specification exported to `{exportPath}`, " ++
    "one module\nper spec file, generated by `lake exe p4spectec-gen`. Never hand-edited.\n-/\n"
  let report : Coverage.Report :=
    { library := lib, input := exportPath, definitions := refinement.coverage
      representations := refinement.representations
      profiles := if certified then profileClaims lib spec else [] }
  outs := outs ++ [{ path := s!"{lib}.lean", text := root },
    { path := s!"{lib}/coverage.json", text := report.render }]
  pure (outs.map fun o =>
    if o.path.endsWith ".lean" then { o with text := hoistAudits o.text } else o)

end P4SpecTec.Codegen.Emit
