import Lean.Elab.Command
import P4SpecTec.Codegen.Emit
import P4SpecTec.Prelude

/-!
Runtime-only variant alternatives preserve source cases, explicit subchecks and
refutable matching. The checks elaborate the production emitter's declarations.
-/

namespace P4SpecTecTest.RuntimeExtension

open P4SpecTec P4SpecTec.Util.Source P4SpecTec.Lang.Il P4SpecTec.Domain
open P4SpecTec.Codegen

private def varT (id : String) : typ' := .VarT (mkPhrase id) []
private def shape : Mixfix.mixop := .Atom (mkPhrase (.Tag "C"))
private def sourceCase : typcase :=
  .mk (mkPhrase (.Atom (mkPhrase (.Tag "C")))) (mkPhrase (.mk (mkPhrase "fixture") [])) []
private def variant (id : String) (params : List String := []) : Lang.Al.def :=
  mkPhrase (.TypD (mkPhrase id) (params.map mkPhrase)
    (mkPhrase (.VariantT [sourceCase])) [])
private def alias : Lang.Al.def :=
  mkPhrase (.TypD (mkPhrase "Alias") []
    (mkPhrase (.PlainT (mkPhrase (.IterT (mkPhrase (varT "Wide")) .List)))) [])
private def spec : Lang.Al.spec :=
  [variant "Small", variant "Wide", variant "Poly" ["X"], alias]
private def collision : Lang.Al.def :=
  let c : typcase := .mk (mkPhrase (.Atom (mkPhrase (.Keyword "runtimeExtern"))))
    (mkPhrase (.mk (mkPhrase "fixture") [])) []
  mkPhrase (.TypD (mkPhrase "Clash") [] (mkPhrase (.VariantT [c])) [])
private def env : Env :=
  { Env.ofSpec "P4SpecTecTest.RuntimeExtension" spec with
    representation.rawExternTypes := ["Wide"] }

#guard (Types.validateRepresentation env).isOk
#guard !(Types.validateRepresentation
  { env with representation.rawExternTypes := ["Missing"] }).isOk
#guard !(Types.validateRepresentation
  { env with representation.rawExternTypes := ["Poly"] }).isOk
#guard !(Types.validateRepresentation
  { env with representation.rawExternTypes := ["Wide", "Wide"] }).isOk
#guard (env.variantCases "Wide" []).map List.length == some 1
#guard env.runtimeAffected (varT "Wide")
#guard !env.runtimeAffected (varT "Small")
#guard env.runtimeAffected (varT "Alias")
#guard env.runtimeAffected (.TupleT [mkPhrase (varT "Alias")])
#guard !(Types.validateRepresentation
  { Env.ofSpec "Collision" [collision] with representation.rawExternTypes := ["Clash"] }).isOk
#guard !(Types.validateRepresentation
  { env with representation.rawExternTypes := ["Alias"] }).isOk
#guard (Exp.run { env } (Exp.ctorFor (varT "Wide") shape)).toOption.map Prod.snd == some true
#guard !(Exp.run { env }
  (Exp.runtimeSubcheck (varT "Wide") (.RecurseSC (mkPhrase (varT "Wide")))
    (.atom "x"))).isOk
#guard !(Types.subtypeDecls env (varT "Wide") (varT "Small")).isOk

open Lean Elab Command in
run_cmd do
  let group := [("Wide", [], deftyp'.VariantT [sourceCase]),
    ("Small", [], deftyp'.VariantT [sourceCase])]
  let mut sources := group.map fun (tid, ps, dt) =>
    Codegen.render (Types.typeDecl env [] tid ps dt)
  for member in group do
    sources := sources ++ (Codegen.render (Types.toValueDecls env [member])).splitOn "\n\n" ++
      (Codegen.render (Types.ofValueDecls env [member])).splitOn "\n\n"
  let bridge ← match Types.subtypeDecls env (varT "Small") (varT "Wide") with
    | .ok f => pure (Codegen.render f)
    | .error e => throwError "{e}"
  sources := sources ++ bridge.splitOn "\n\n"
  let term (m : Exp.CgM Codegen.Term) : CommandElabM String := do
    match Exp.run { env } m with
    | .ok t => pure (Codegen.render t.fmt)
    | .error e => throwError "{e}"
  let raw := "(Wide.runtimeExtern ⟨Lean.Json.null⟩)"
  let mixop ← term (Exp.runtimeSubcheck (varT "Wide") (.MixopSC [shape]) (.atom raw))
  let skip ← term (Exp.runtimeSubcheck (varT "Wide") .SkipSC (.atom raw))
  let up ← term (Exp.castUp (varT "Wide") (varT "Wide") (.atom raw))
  let down ← term (Exp.castDown (varT "Wide") (varT "Wide") (.atom raw))
  let checks := [
    s!"#guard !({mixop})",
    s!"#guard {skip}",
    s!"#guard !Wide.is_Small {raw}",
    s!"#guard (Wide.of_Small {raw}).isNone",
    s!"#guard match P4SpecTec.Prelude.ToValue.toValue {up} with " ++
      "| ⟨.ExternV .null, _, _⟩ => true | _ => false",
    s!"#guard match {down} with " ++
      "| some (.runtimeExtern _) => true | _ => false",
    "#guard match Wide.ofValue 1 (P4SpecTec.Runtime.Value.Make.extern .TextT .null) with " ++
      "| some (.runtimeExtern _) => true | _ => false",
    "#guard match Wide.ofValue 1 (Wide.toValue Wide._C) with " ++
      "| some ._C => true | _ => false",
    "#guard Wide.is_Small Wide._C"]
  sources := sources.flatMap fun source =>
    (source.splitOn "\ninstance").mapIdx fun i s => if i == 0 then s else "instance" ++ s
  for source in ["open P4SpecTec P4SpecTec.Prelude"] ++ sources ++ checks do
    let stx ← match Lean.Parser.runParserCategory (← getEnv) `command source with
      | .ok stx => pure stx
      | .error e => throwError "{source}\n{e}"
    Lean.Elab.Command.elabCommand stx

end P4SpecTecTest.RuntimeExtension
