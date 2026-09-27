import P4SpecTec.Codegen.Certificates.Representation
import P4SpecTec.Codegen.Certificates.Reverse

/-!
Lift paired invocation certificates to independently specified source input domains.
Coverage supplies generated witnesses for every source input, without asking callers
to supply a successful decode or an already related generated value. Invocation
certificates still retain their exact configuration and environment hypotheses.
-/

namespace P4SpecTec.Codegen.SourceEntry

open P4SpecTec.Lang.Il P4SpecTec.Domain
open RepresentationFields

/-- The source input phrases in actual invocation order. -/
def inputTypes (d : Lang.Al.def) : Except String (List typ) := do
  match d.it with
  | .FuncDecD _ [] parameters .. | .TableDecD _ parameters .. =>
    parameters.mapM fun parameter => match parameter.it with
      | .ExpP type => pure type
      | _ => throw "source entry needs first-order input parameters"
  | .RelD _ nottyp inputs .. =>
    let fields := Mixfix.args nottyp.it
    pure (Exp.splitArgs (inputs.map (·.toNat)) fields).1
  | _ => throw "source entry needs a monomorphic defined callable"

/-- Checked source codecs for every declared input, including nested field occurrences. -/
def contracts (env : Env) (d : Lang.Al.def)
    (available : Option (String → Option NominalContract) := none) :
    Except String (List (typ × Contract)) := do
  let fallback : String → Option NominalContract := fun name => do
    let declaration ← env.defs.find? fun d => match d.it with
      | .TypD identifier .. => identifier.it == name
      | _ => false
    (← (RepresentationCertificates.plan env declaration).toOption).nominal
  let known := available.getD fallback
  (← inputTypes d).mapM fun type => do
    pure (type, ← resolve env known type)

private def assumptions (env : Env) (m : Props.Member)
    (fields : List (typ × Contract)) : String :=
  "(cfg : Interp_al.Interp.Config) (ctx : Interp_al.Ctx.t) (internal : Bool)\n" ++
  "    (hguard : cfg.guard = false) " ++
  (if m.printHints then "(hhints : cfg.printHints = []) " else "") ++
  "(hfenv : ctx.local.fenv = [])\n" ++
  s!"    (hspec : HoldsSpec {env.lib}.spec ctx.global)" ++
  String.join (m.typeFreshness.zipIdx.map fun (name, index) =>
    s!"\n    (ht{index} : ctx.global.tdtbl.get? {name.quote} = none)") ++
  String.join (fields.zipIdx.map fun ((type, _), index) =>
    s!"\n    (v{index} : Lang.Il.value) (hv{index} : ({source env type}) v{index})")

private def result (m : Props.Member) (fields : List (typ × Contract)) : String :=
  String.join (fields.zipIdx.map fun ((_, contract), index) =>
    s!"∃ p{index} : {contract.carrier}, ") ++
  String.join (fields.zipIdx.map fun ((_, contract), index) =>
    s!"({contract.admitted}) p{index} ∧ Rel v{index} p{index} ∧ ") ++
  "(∀ fuel : Nat, " ++ (Validate.conclusion m).pretty 1000000 ++ ") ∧\n" ++
  "      " ++ (Reverse.conclusion m).pretty 1000000

/-- Exact full-source entry obligation, checked independently of the emitted proof. -/
def theoremType (env : Env) (d : Lang.Al.def) (m : Props.Member)
    (available : Option (String → Option NominalContract) := none) : Except String String := do
  let fields ← contracts env d available
  if !m.tparams.isEmpty || fields.length != m.params.length then
    throw "source entry input signature differs from its invocation certificate"
  pure ("∀ " ++ assumptions env m fields ++ ", " ++ result m fields)

/-- Emit a full-domain entry theorem from actual codecs and both invocation directions. -/
def declarations (env : Env) (d : Lang.Al.def) (m : Props.Member)
    (available : Option (String → Option NominalContract) := none) : Except String Std.Format := do
  let _ ← theoremType env d m available
  let fields ← contracts env d available
  let owner := m.localName.replace ".run" ""
  let qualified := m.defName.replace ".run" ""
  let mut proof := ""
  for ((type, contract), index) in fields.zipIdx do
    proof := proof ++ s!"  obtain ⟨p{index}, admitted{index}, h{index}⟩ :=\n" ++
      s!"    (@Representation.Codec.adequate ({contract.carrier}) ⟨{contract.encoder}⟩ " ++
      s!"⟨{contract.decoder}⟩ ({source env type}) ({contract.admitted}) " ++
      s!"({contract.codec})).coverage v{index} hv{index}\n"
  let indices := List.range fields.length
  let witnesses := indices.map (fun index => s!"p{index}") ++
    indices.flatMap (fun index => [s!"admitted{index}", s!"h{index}"]) ++ ["?_", "?_"]
  let arguments := ["cfg", "ctx", "internal", "hguard"] ++
    (if m.printHints then ["hhints"] else []) ++ ["hfenv", "hspec"] ++
    (List.range m.typeFreshness.length).map (fun index => s!"ht{index}") ++
    indices.map (fun index => s!"v{index}") ++ indices.map (fun index => s!"p{index}") ++
    indices.map (fun index => s!"h{index}")
  proof := proof ++ "  refine ⟨" ++ ", ".intercalate witnesses ++ "⟩\n" ++
    "  · intro fuel\n" ++ s!"    exact {qualified}.refines fuel " ++
    " ".intercalate arguments ++ "\n" ++
    s!"  · exact {qualified}.realizes " ++ " ".intercalate arguments ++ "\n"
  pure (Std.Format.text (boundedLines (
    "/-- Every declared source input has admitted witnesses with both execution directions. -/\n" ++
    s!"theorem {owner}.sourceCorrespondence\n    " ++ assumptions env m fields ++ " :\n" ++
    "    " ++ result m fields ++ " := by\n" ++ proof ++
    s!"\n#audit_axioms {qualified}.sourceCorrespondence")))

end P4SpecTec.Codegen.SourceEntry
