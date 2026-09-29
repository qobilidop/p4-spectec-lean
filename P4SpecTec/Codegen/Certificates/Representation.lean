import P4SpecTec.Codegen.Certificates.RepresentationAlias
import P4SpecTec.Codegen.Certificates.RepresentationContainer
import P4SpecTec.Codegen.Certificates.RepresentationExtern
import P4SpecTec.Codegen.Certificates.RepresentationMap
import P4SpecTec.Codegen.Certificates.RepresentationMixedVariant
import P4SpecTec.Codegen.Certificates.RepresentationRecord
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveCodec
import P4SpecTec.Codegen.Certificates.RepresentationRecursiveTotality
import P4SpecTec.Codegen.Certificates.RepresentationTotal
import P4SpecTec.Codegen.Certificates.RepresentationVariant
import P4SpecTec.Codegen.Types

/-!
Source-grammar representation certificates for checked atomic variants, aliases,
one-field variants and polymorphic containers. Actual source signatures define the
domains; unsupported source shapes remain explicit gaps.
-/

namespace P4SpecTec.Codegen.RepresentationCertificates

open Std (Format)
open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Codegen.Types

/-- Check the complete source family before emitting an atomic-variant codec. -/
def checkSupport (env : Env) (d : Lang.Al.def) : Except String (List typcase) := do
  let .TypD name [] definition _ := d.it
    | throw "representation codec needs a monomorphic source type declaration"
  if env.representation.hasRawExtern name.it then
    throw "representation codec needs separate source/runtime admission"
  let .VariantT cases := definition.it | throw "representation codec needs a variant"
  if cases.isEmpty then throw "representation codec needs a nonempty variant"
  for c in cases do
    let .Atom _ := c.nottyp.it | throw "representation codec needs atomic source constructors"
  for c in cases do
    if (cases.filter fun other => Mixfix.eq_mixop c.nottyp.it other.nottyp.it).length != 1 then
      throw "representation codec needs distinct source constructors"
  return cases

/-- Proof-support imports for the supported source-grammar certificate family. -/
def supportImports : List String :=
  ["P4SpecTec.Refine.Representation.Delay", "P4SpecTec.Refine.Representation.Source",
   "P4SpecTec.Refine.Representation.SourceAlias",
   "P4SpecTec.Refine.Representation.SourceAtomic",
   "P4SpecTec.Refine.Representation.SourceRecord",
   "P4SpecTec.Refine.Representation.SourceCodec",
   "P4SpecTec.Refine.Representation.SourceTuple",
   "P4SpecTec.Refine.Representation.SourceExtern",
   "P4SpecTec.Refine.Representation.SourceVariant", "P4SpecTec.Tactic.Audit",
   "P4SpecTec.Tactic.CarrierInduction"]

private def plainAlias (d : Lang.Al.def) : Bool :=
  match d.it with
  | .TypD _ _ definition _ => match definition.it with | .PlainT _ => true | _ => false
  | _ => false

/-- The exact source grammar predicate, read from the actual compiled quotation. -/
def sourceName (d : Lang.Al.def) : String := Names.typeName d.it.id.it ++ ".source"

/-- The exact representation obligation over the actual generated carrier and decoder. -/
private def atomicCodecType (env : Env) (d : Lang.Al.def) : Except String Format := do
  let _ ← checkSupport env d
  let name := env.q (Names.typeName d.it.id.it)
  pure (Format.text (s!"@Refine.Representation.Codec {name} ⟨{name}.toValue⟩ " ++
    s!"⟨{name}.ofValue⟩ " ++ env.q (sourceName d) ++ s!" (fun _ : {name} => True)"))

private def proofTemplate : String :=
  "  encodingValid x _ := by\n" ++
  "    cases x <;> simp [SOURCE_PREDICATE, Representation.Source.atomVariant,\n" ++
  "      Representation.Source.atomKinds, SOURCE_AL, ENCODER,\n" ++
  "      ToValue.toValue, Runtime.Value.Make.case, Runtime.Value.Make.mk, Prelude.Value.atom,\n" ++
  "      Q.d, Q.dt, Q.tc, Q.a, Lang.Il.typcase.nottyp]\n" ++
  "  decoder.sound fuel v x hv hd := by\n" ++
  "    obtain ⟨a, hs, ha⟩ := hv\n" ++
  "    simp only [Representation.Source.atomKinds, SOURCE_AL,\n" ++
  "      Q.d, Q.dt, Q.tc, Q.a, Lang.Il.typcase.nottyp, List.filterMap,\n" ++
  "      List.mem_cons, List.not_mem_nil, or_false] at ha\n" ++
  "    CASE_SPLIT <;>\n" ++
  "      cases fuel with\n" ++
  "      | zero => simp [OfValue.ofValue, DECODER] at hd\n" ++
  "      | succ fuel =>\n" ++
  "        simp [OfValue.ofValue, DECODER, hs, Prelude.Value.caseArgs,\n" ++
  "          Domain.Mixfix.eq_mixop, Domain.Mixfix.eq, Domain.Atom.eq,\n" ++
  "          Domain.Atom.compare, Domain.Atom.tag, ha,\n" ++
  "          Prelude.Value.atom, Domain.Mixfix.args] at hd\n" ++
  "        SOUND_ELIM\n" ++
  "        constructor\n" ++
  "        · trivial\n" ++
  "        · simp [Rel, canon, canon', canonMixfix, hs, ha,\n" ++
  "            ToValue.toValue, ENCODER, Runtime.Value.Make.case,\n" ++
  "            Runtime.Value.Make.mk, Prelude.Value.atom]\n" ++
  "  decoder.sufficient v hv := by\n" ++
  "    obtain ⟨a, hs, ha⟩ := hv\n" ++
  "    simp only [Representation.Source.atomKinds, SOURCE_AL,\n" ++
  "      Q.d, Q.dt, Q.tc, Q.a, Lang.Il.typcase.nottyp, List.filterMap,\n" ++
  "      List.mem_cons, List.not_mem_nil, or_false] at ha\n"

private def witnessTemplate : String :=
  "    · refine ⟨WITNESS, 1, ?_⟩\n" ++
  "      intro fuel hf\n" ++
  "      cases fuel with\n" ++
  "      | zero => omega\n" ++
  "      | succ fuel =>\n" ++
  "        simp [OfValue.ofValue, DECODER, hs, Prelude.Value.caseArgs,\n" ++
  "          Domain.Mixfix.eq_mixop, Domain.Mixfix.eq, Domain.Atom.eq,\n" ++
  "          Domain.Atom.compare, Domain.Atom.tag, ha, Prelude.Value.atom, Domain.Mixfix.args]\n"

/-- Emit encoding validity and actual OfValue soundness and stable sufficient fuel. -/
private def atomicDeclarations (env : Env) (d : Lang.Al.def) : Except String Format := do
  let cases ← checkSupport env d
  let name := Names.typeName d.it.id.it
  let qualified := env.q name
  let source := sourceName d
  let split := "rcases ha with " ++ " | ".intercalate (List.replicate cases.length "ha")
  let witnesses := String.join ((ctorNames cases).map fun constructor =>
    witnessTemplate.replace "WITNESS" (qualified ++ "." ++ constructor))
  let proof := (proofTemplate ++ "    " ++ split ++ "\n" ++ witnesses)
    |>.replace "SOURCE_AL" (qualified ++ ".al")
    |>.replace "ENCODER" (qualified ++ ".toValue")
    |>.replace "DECODER" (qualified ++ ".ofValue")
    |>.replace "SOURCE_PREDICATE" source
    |>.replace "CASE_SPLIT" split
    |>.replace "SOUND_ELIM" (if cases.length == 1 then "cases x" else "subst x")
  let tags := cases.filterMap fun c => match c.nottyp.it with
    | .Atom a => some (Atom.tag a.it)
    | _ => none
  let proof := if tags.eraseDups.length == 1 then
      proof.replace "Domain.Atom.tag, " ""
    else proof
  let text := "/-- The complete atomic source grammar from the actual quoted declaration. -/\n" ++
    s!"def {source} : Lang.Il.value → Prop :=\n" ++
    s!"  Refine.Representation.Source.atomVariant {qualified}.al\n\n" ++
    "/-- Every source value has a faithful sufficient decode; admitted encodings are valid. -/\n" ++
    s!"theorem {name}.codec : " ++ (← atomicCodecType env d).pretty ++ " where\n" ++ proof ++
    s!"\n#audit_axioms {qualified}.codec"
  let .TypD sourceId [] definition _ := d.it | throw "expected checked atomic type"
  let sourceId := (Reify.str sourceId.it).fmt.pretty
  let definitionText := (Reify.deftyp definition).arg.pretty
  let casesText := (Reify.lst (cases.map fun c =>
    let (origin, args) := match c.typorigin.it with | .mk origin args => (origin, args)
    Term.call "Q.tc" [Reify.mixfix c.nottyp.it Reify.typ,
      Reify.str origin.it, Reify.lst (args.map Reify.typ)])).arg.pretty
  let members := " | ".intercalate (List.replicate cases.length "rfl")
  let bridge := "\n\n/-- The atomic codec also inhabits the complete finite source grammar. -/\n" ++
    s!"theorem {name}.sourceCodec : @Representation.Codec {qualified} " ++
    s!"⟨{qualified}.toValue⟩ ⟨{qualified}.ofValue⟩\n" ++
    s!"    (Representation.Source.Valid {env.lib}.spec Representation.Source.externDomain " ++
    s!"(Q.varT {sourceId} [])) (fun _ => True) := by\n" ++
    "  apply Representation.Codec.sourceIff (source := " ++ qualified ++ ".source) ?_ " ++
    qualified ++ ".codec\n" ++
    "  intro v\n" ++
    s!"  exact (Representation.Source.atomicIff {qualified}.al (Q.i {sourceId})\n" ++
    s!"    {definitionText} {casesText} rfl rfl (by rfl) (by\n" ++
    "      intro c member\n" ++
    "      simp only [List.mem_cons, List.not_mem_nil, or_false] at member\n" ++
    s!"      rcases member with {members}\n" ++
    "      all_goals exact ⟨_, rfl⟩) v).symm\n\n" ++
    s!"#audit_axioms {qualified}.sourceCodec"
  pure (Format.text (boundedLines (text ++ bridge)))

/-- One complete source representation certificate and its actual import dependencies. -/
structure Plan where
  /-- Exact kernel type checked by the compiled coverage inventory. -/
  type : Format
  /-- Source declarations and their audited proofs. -/
  declarations : Format
  /-- Other nominal codec sidecars required by the proof. -/
  dependencies : List String := []
  /-- A monomorphic complete `Source.Valid` codec available to parent fields. -/
  nominal : Option RepresentationFields.NominalContract := none
  /-- A checked total-admission theorem for a monomorphic family, when available. -/
  total : Option String := none

/-- Plan one full source codec using independently completed nominal dependencies. -/
def planWithKnown (env : Env) (d : Lang.Al.def)
    (known : String → Option RepresentationFields.NominalContract) : Except String Plan := do
  let name := d.it.id.it
  let qualified := env.q (Names.typeName name)
  let codec := qualified ++ "." ++ env.part "codec"
  let admitted := qualified ++ "." ++ env.part "admitted"
  if env.runtimeProfile then
    -- Only the families whose generators state the selected profile.
    if (RepresentationExterns.checkSupport d).isOk || (checkSupport env d).isOk ||
        (plainAlias d && (RepresentationAliases.checkSupport env d).isOk) ||
        (RepresentationVariants.checkSupport env d known).isOk then
      throw "runtime profile codec is not implemented for this source family"
  if (RepresentationExterns.checkSupport d).isOk then
    return { type := ← RepresentationExterns.codecType env d
             declarations := ← RepresentationExterns.declarations env d
             nominal := some ⟨qualified ++ ".codec", "fun _ => True"⟩ }
  if (checkSupport env d).isOk then
    return { type := ← atomicCodecType env d, declarations := ← atomicDeclarations env d
             nominal := some ⟨qualified ++ ".sourceCodec", "fun _ => True"⟩ }
  if (RepresentationMaps.checkSupport env d).isOk then
    return { type := ← RepresentationMaps.codecType env d
             declarations := ← RepresentationMaps.declarations env d
             dependencies := ← RepresentationMaps.dependencies env d }
  if (RepresentationContainers.codecType env d).isOk then
    return { type := ← RepresentationContainers.codecType env d
             declarations := ← RepresentationContainers.declarations env d }
  if (RepresentationRecursive.groupOf env name).isOk then
    let recursive ← RepresentationRecursive.derive env known name
    let some leader := recursive.members.head? | throw "recursive codec group is empty"
    let declarations ← if name == leader then
        pure (joinDecls (← RepresentationRecursive.declarations env recursive
          (Names.typeName (env.bundle leader))))
      else pure (Format.text "")
    return { type := RepresentationRecursive.memberCodecType env name, declarations
             dependencies := if name == leader then recursive.dependencies else [leader]
             nominal := some ⟨codec, admitted⟩ }
  if plainAlias d then
    if (RepresentationAliases.checkSupport env d).isOk then
      return { type := ← RepresentationAliases.codecType env d
               declarations := ← RepresentationAliases.declarations env d
               nominal := some ⟨qualified ++ ".codec", "fun _ => True"⟩ }
    let (_, field) ← RepresentationAliases.fieldSupport env known d
    return { type := ← RepresentationAliases.fieldCodecType env known d
             declarations := ← RepresentationAliases.fieldDeclarations env known d
             dependencies := field.dependencies
             nominal := some ⟨codec, admitted⟩ }
  if (RepresentationVariants.checkSupport env d known).isOk then
    let (_, _, field) ← RepresentationVariants.checkSupport env d known
    return { type := ← RepresentationVariants.codecType env d known
             declarations := ← RepresentationVariants.declarations env d known
             dependencies := field.dependencies
             nominal := some ⟨qualified ++ ".codec", qualified ++ ".admitted"⟩ }
  if (RepresentationMixedVariants.checkSupport env d known).isOk then
    let constructors ← RepresentationMixedVariants.checkSupport env d known
    return { type := ← RepresentationMixedVariants.codecType env d known
             declarations := ← RepresentationMixedVariants.declarations env d known
             dependencies := (constructors.flatMap fun constructor =>
               constructor.fields.flatMap (fun (_, field) => field.dependencies)).eraseDups
             nominal := some ⟨codec, admitted⟩ }
  let fields ← RepresentationRecords.checkSupport env known d
  return { type := ← RepresentationRecords.codecType env known d
           declarations := ← RepresentationRecords.declarations env known d
           dependencies := (fields.flatMap (fun (_, field) => field.dependencies)).eraseDups
           nominal := some ⟨codec, admitted⟩ }

/-- Resolve a single requested codec recursively for standalone clients and fixtures. -/
partial def plan (env : Env) (d : Lang.Al.def) (seen : List String := []) : Except String Plan := do
  let name := d.it.id.it
  if seen.contains name then throw s!"source codec {name} needs recursive group composition"
  planWithKnown env d fun child => do
    let declaration ← env.defs.find? (fun d => match d.it with
      | .TypD name .. | .ExternTypD name .. => name.it == child
      | _ => false)
    (← (plan env declaration (name :: seen)).toOption).nominal

/-- Build each selected codec once, in actual declaration dependency/SCC order. Parents can
use only complete prior plans, or a `fallback` plan of a type outside the selection; failures
retain their concrete exclusion reason. -/
private def catalogWith (env : Env) (selected : String → Bool)
    (fallback : String → Option Plan) : Std.HashMap String (Except String Plan) := Id.run do
  let definitions := env.defs.filter fun d => match d.it with
    | .TypD .. | .ExternTypD .. => true
    | _ => false
  let dependencies := fun name => match env.types[name]? with
    | some info => match info.deftyp with
      | some body => (Env.deftypRefs body).eraseDups.filter fun dependency =>
        !info.tparams.contains dependency && env.types.contains dependency
      | none => []
    | none => []
  let mut completed : Std.HashMap String (Except String Plan) := {}
  for group in Graph.sccs (definitions.map (·.it.id.it)) dependencies do
    let prior := fun name => match completed[name]? with
      | some plan => plan.toOption
      | none => fallback name
    let known := fun name => do (← prior name).nominal
    let totals := fun child => do
      let parent ← prior child
      pure { nominal := ← parent.nominal, proof := ← parent.total :
        RepresentationTotals.TotalContract }
    -- A complete recursive group shares one native induction bundle at its codec leader.
    let recursiveTotal := do
      let requested ← group.head?
      let _ ← (RepresentationRecursive.groupOf env requested).toOption
      let recursive ← (RepresentationRecursive.derive env known requested).toOption
      let leader ← recursive.members.head?
      let proof ← (RepresentationRecursive.totalityDeclarations env recursive
        (Names.typeName (env.bundle leader)) totals).toOption
      pure (leader, proof)
    for name in group do
      if !selected name then continue
      if let some d := definitions.find? (·.it.id.it == name) then
        let candidate := planWithKnown env d known
        let candidate := candidate.map fun representation => Id.run do
          if let some (leader, proof) := recursiveTotal then
            return { representation with
              declarations := if name == leader then
                joinDecls [representation.declarations, proof] else representation.declarations
              total := representation.nominal.map fun _ =>
                env.q (Names.typeName name) ++ "." ++ env.part "admittedAll" }
          let admitted := representation.nominal.map (·.admitted) |>.getD ""
          match RepresentationTotals.declarations env d admitted totals with
          | .error _ => return representation
          | .ok proof => return { representation with
              declarations := joinDecls [representation.declarations, proof]
              dependencies := (representation.dependencies ++
                (dependencies name).filter (fun child => (totals child).isSome)).eraseDups
              total := representation.nominal.map fun _ =>
                env.q (Names.typeName name) ++ "." ++ env.part "admittedAll" }
        completed := completed.insert name candidate
  return completed

/-- Build each source codec once, in actual declaration dependency/SCC order.
Parents can use only complete prior plans; failures retain their concrete exclusion reason. -/
def catalog (env : Env) : Std.HashMap String (Except String Plan) :=
  catalogWith env (fun _ => true) (fun _ => none)

/-- The declared types whose values can contain an explicitly runtime-extended carrier. -/
def runtimeClosure (env : Env) : List String :=
  (env.defs.filterMap fun d => match d.it with
    | .TypD name .. => if env.runtimeAffected (.VarT name []) then some name.it else none
    | _ => none).eraseDups

/-- The polymorphic containers, whose runtime codecs take runtime-profile parameter codecs. -/
def runtimeContainers (env : Env) : List String :=
  env.defs.filterMap fun d => match d.it with
    | .TypD name (_ :: _) .. =>
      if (RepresentationMaps.checkSupport env d).isOk ||
          (RepresentationContainers.codecType env d).isOk then some name.it else none
    | _ => none

/-- The runtime-profile codecs of the runtime closure and of the polymorphic containers.
Every other type contributes its source codec, lifted by the checked closure certificate. -/
def runtimeCatalog (env : Env) (source : Std.HashMap String (Except String Plan)) :
    Std.HashMap String (Except String Plan) :=
  let closure := runtimeClosure env
  if closure.isEmpty then {} else
  let runtime := { env with runtimeProfile := true }
  let selected := closure ++ runtimeContainers env
  catalogWith runtime selected.contains fun name =>
    if closure.contains name then none else do
      let plan ← (← source[name]?).toOption
      let qualified := env.q (Names.typeName name)
      let lift := runtime.liftRuntime qualified (qualified ++ ".toValue") (qualified ++ ".ofValue")
      pure { plan with nominal := plan.nominal.map fun nominal =>
        { nominal with codec := lift nominal.codec } }

/-- The checked certificate that the runtime profile adds no alternative within the declared
closure of any type outside the runtime closure, which lifts their source codecs. -/
def runtimeClosedDeclarations (env : Env) : Format :=
  let runtime := { env with runtimeProfile := true }
  let closure := runtimeClosure env
  let names := (env.defs.filterMap fun d => match d.it with
    | .TypD name .. | .ExternTypD name .. =>
      if closure.contains name.it then none else some name.it
    | _ => none).eraseDups
  let list := "[" ++ ", ".intercalate (names.map fun n => (Reify.str n).fmt.pretty) ++ "]"
  Format.text (boundedLines (
    "/-- The runtime profile adds no alternative within the declared closure of any type\n" ++
    "outside the runtime closure, so their source codecs are runtime codecs. -/\n" ++
    "theorem runtimeClosed : Representation.Source.ClosedAvoiding " ++ env.lib ++ ".spec\n" ++
    "    " ++ runtime.domainTerm ++ "\n    " ++ list ++ " :=\n" ++
    "  Representation.Source.closedCheckSound (by closure_check)\n\n" ++
    s!"#audit_axioms {runtime.runtimeClosedName}"))

/-- Exact compiled obligation for a complete source-family certificate. -/
def codecType (env : Env) (d : Lang.Al.def) : Except String Format := do
  return (← plan env d).type

/-- Emit one complete source-family certificate with checked nominal dependencies. -/
def declarations (env : Env) (d : Lang.Al.def) : Except String Format := do
  return (← plan env d).declarations

/-- Nominal codec sidecars required by a supported complete representation contract. -/
def dependencies (env : Env) (d : Lang.Al.def) : Except String (List String) := do
  return (← plan env d).dependencies

end P4SpecTec.Codegen.RepresentationCertificates
