import P4SpecTec.Codegen.Certificates.RepresentationMixedVariant
import P4SpecTec.Codegen.Certificates.RepresentationRecord
import P4SpecTec.Codegen.Certificates.RepresentationVariant

/-!
Total admission for acyclic source codecs, built from complete constructor fields and
previously proved child admissions. Conditional container theorems retain their parameter
admission hypotheses. Runtime-only extern alternatives are deliberately rejected.
-/

namespace P4SpecTec.Codegen.RepresentationTotals

open Std (Format)
open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Codegen.Types

/-- An exact nominal codec admission and a checked theorem admitting its entire carrier. -/
structure TotalContract where
  /-- The actual codec and admission predicate supplied by the source-codec plan. -/
  nominal : RepresentationFields.NominalContract
  /-- A term proving `∀ x, nominal.admitted x`, checked again in the emitted proof. -/
  proof : String

private def indent (s : String) : String := "  " ++ s.replace "\n" "\n  "

private def conjunction (xs : List String) : String :=
  "⟨" ++ ", ".intercalate (xs ++ ["trivial"]) ++ "⟩"

private def declaration (env : Env) (name : String) : Except String Lang.Al.def :=
  match env.defs.find? (fun d => match d.it with
      | .TypD identifier .. | .ExternTypD identifier .. => identifier.it == name | _ => false) with
  | some d => pure d
  | none => throw s!"total admission needs source declaration {name}"

private def acyclic (env : Env) (d : Lang.Al.def) : Except String Unit := do
  let .TypD name _ definition _ := d.it | return ()
  let edges := Std.HashMap.ofList (env.defs.filterMap fun d => match d.it with
    | .TypD identifier _ body _ => some (identifier.it, Env.deftypRefs body.it) | _ => none)
  if (Env.deftypRefs definition.it).any (fun child =>
      (Graph.reachable edges child).contains name.it) then
    throw "total admission needs an acyclic source family"

/-- Resolve an exact field-admission totality proof from actual codec metadata and child totals. -/
partial def fieldProof (env : Env) (known : String → Option TotalContract)
    (t : typ) : Except String String := do
  let nominal := fun name => (known name).map (·.nominal)
  let contract ← RepresentationFields.resolve env nominal t
  let proof ← match t.it with
  | .BoolT | .NumT .NatT | .NumT .IntT | .TextT => pure "(fun _ => True.intro)"
  | .TupleT [] => pure "(fun _ => True.intro)"
  | .TupleT [left, right] =>
    let a ← fieldProof env known left
    let b ← fieldProof env known right
    pure s!"(fun p => ⟨({a}) p.1, ({b}) p.2⟩)"
  | .IterT child _ =>
    let proof ← fieldProof env known child
    pure s!"(fun xs x _ => ({proof}) x)"
  | .VarT name [] =>
    if !env.runtimeProfile && env.representation.hasRawExtern name.it then
      throw "total admission rejects runtime extern alternatives"
    let d ← declaration env name.it
    if let .ExternTypD .. := d.it then
      return s!"(show ∀ x : ({contract.carrier}), ({contract.admitted}) x from fun _ => True.intro)"
    let some total := known name.it | throw s!"unproved child total admission {name.it}"
    pure total.proof
  | .VarT name args =>
    if !env.runtimeProfile && env.representation.hasRawExtern name.it then
      throw "total admission rejects runtime extern alternatives"
    let d ← declaration env name.it
    let children ← args.mapM (fieldProof env known)
    if (RepresentationContainers.pairShape env d).isOk then
      return s!"(show ∀ x : ({contract.carrier}), ({contract.admitted}) x from " ++
        s!"fun x => {env.q (Names.typeName name.it)}.casesOn x " ++
        s!"(fun a b => ⟨({children[0]!}) a, ({children[1]!}) b⟩))"
    if (RepresentationContainers.listShape env d).isOk then
      return s!"(show ∀ x : ({contract.carrier}), ({contract.admitted}) x from " ++
        s!"fun x => {env.q (Names.typeName name.it)}.casesOn x " ++
        s!"(fun xs a _ => ({children[0]!}) a))"
    let (_, _, outer, inner) ← RepresentationMaps.checkSupport env d
    let outerD ← declaration env outer.it
    let innerD ← declaration env inner.it
    let _ ← RepresentationContainers.listShape env outerD
    let _ ← RepresentationContainers.pairShape env innerD
    pure (s!"(fun x => {env.q (Names.typeName outer.it)}.casesOn x " ++
      s!"(fun xs p _ => {env.q (Names.typeName inner.it)}.casesOn p " ++
      s!"(fun a b => ⟨({children[0]!}) a, ({children[1]!}) b⟩)))")
  | _ => throw "total admission has no field proof for this source shape"
  pure s!"(show ∀ x : ({contract.carrier}), ({contract.admitted}) x from {proof})"

private def conditional (env : Env) (d : Lang.Al.def) : Except String String := do
  let name := Names.typeName d.it.id.it
  let qualified := env.q name
  if let .ok (_, _, constructor) := RepresentationContainers.pairShape env d then
    let ctor := (ctorNames [constructor]).head!
    return s!"theorem {name}.admittedAll \{α β : Type} (left : α → Prop) (right : β → Prop)\n" ++
      "    (hl : ∀ x, left x) (hr : ∀ x, right x) :\n" ++
      s!"    ∀ x : {qualified} α β, {qualified}.admitted left right x := by\n" ++
      s!"  intro x; cases x with | {ctor} a b => exact ⟨hl a, hr b⟩"
  if let .ok (_, constructor) := RepresentationContainers.listShape env d then
    let ctor := (ctorNames [constructor]).head!
    return s!"theorem {name}.admittedAll \{α : Type} (accepted : α → Prop)\n" ++
      "    (all : ∀ x, accepted x) :\n" ++
      s!"    ∀ x : {qualified} α, {qualified}.admitted accepted x := by\n" ++
      s!"  intro x; cases x with | {ctor} xs => intro a ha; exact all a"
  let (_, _, outer, inner) ← RepresentationMaps.checkSupport env d
  let outerD ← declaration env outer.it
  let innerD ← declaration env inner.it
  let (_, outerC) ← RepresentationContainers.listShape env outerD
  let (_, _, innerC) ← RepresentationContainers.pairShape env innerD
  let outerName := env.q (Names.typeName outer.it)
  let innerName := env.q (Names.typeName inner.it)
  let outerCtor := (ctorNames [outerC]).head!
  let innerCtor := (ctorNames [innerC]).head!
  return s!"theorem {name}.admittedAll \{α β : Type} (left : α → Prop) (right : β → Prop)\n" ++
    "    (hl : ∀ x, left x) (hr : ∀ x, right x) :\n" ++
    s!"    ∀ x : {qualified} α β, {outerName}.admitted " ++
    s!"({innerName}.admitted left right) x := by\n" ++
    s!"  intro x; cases x with | {outerCtor} xs =>\n" ++
    s!"    intro p hp; cases p with | {innerCtor} a b => exact ⟨hl a, hr b⟩"

/-- Emit total admission from actual codec metadata and previously proved child totals.
Parameterized containers keep explicit totality hypotheses; monomorphic declarations reject
cycles and runtime alternatives even if a callback supplies an alleged totality proof. -/
def declarations (env : Env) (d : Lang.Al.def) (admitted : String)
    (known : String → Option TotalContract := fun _ => none) : Except String Format := do
  let name := Names.typeName d.it.id.it
  let qualified := env.q name
  if env.representation.hasRawExtern d.it.id.it then
    throw "total admission rejects runtime extern alternatives"
  acyclic env d
  let nominal := fun name => (known name).map (·.nominal)
  let text ← match d.it with
    | .TypD _ (_ :: _) .. =>
      if env.runtimeProfile then
        throw "runtime container codecs reuse the source profile's admission and totality"
      conditional env d
    | .ExternTypD .. =>
      if admitted != "fun _ => True" then throw "external admission must be the exact True plan"
      pure (s!"theorem {name}.admittedAll : ∀ x : {qualified}, ({admitted}) x := by\n" ++
        "  intro x; trivial")
    | .TypD _ [] definition _ => do
      let body ← match definition.it with
        | .PlainT t =>
          let proof ← fieldProof env known t
          pure s!"intro x\nexact ({proof}) x"
        | .StructT _ =>
          let fields ← RepresentationRecords.checkSupport env nominal d
          let proofs ← fields.mapM fun ((label, t), _) => do
            let proof ← fieldProof env known t
            pure s!"({proof}) (x.{Names.fieldName label.it})"
          pure ("intro x\nexact " ++ conjunction proofs)
        | .VariantT cases =>
          if admitted == "fun _ => True" then
            if cases.isEmpty || cases.any (fun c => !(Mixfix.args c.nottyp.it).isEmpty) then
              throw "atomic total admission needs complete nullary source constructors"
            pure "intro x; trivial"
          else if let .ok (constructor, t, _) :=
              RepresentationVariants.checkSupport env d nominal then
            let proof ← fieldProof env known t
            let ctor := (ctorNames [constructor]).head!
            pure s!"intro x\ncases x with\n| {ctor} a =>\n  exact ({proof}) a"
          else
            let constructors ← RepresentationMixedVariants.checkSupport env d nominal
            let ctors := ctorNames (constructors.map (·.source))
            let mut body := "intro x\ncases x with\n"
            for (constructor, ctor) in constructors.zip ctors do
              let vars := (List.range constructor.fields.length).map fun i => s!"x{i}"
              let proofs ← constructor.fields.zipIdx.mapM fun ((t, _), i) => do
                let proof ← fieldProof env known t
                pure s!"({proof}) x{i}"
              body := body ++ "| " ++ " ".intercalate (ctor :: vars) ++ " =>\n" ++
                indent (if proofs.isEmpty then "trivial" else
                  "exact " ++ conjunction proofs) ++ "\n"
            pure body
      pure (s!"theorem {name}.{env.part "admittedAll"} : " ++
        s!"∀ x : {qualified}, ({admitted}) x := by\n" ++ indent body)
    | _ => throw "total admission needs a supported source type declaration"
  pure (Format.text (boundedLines
    ("/-- Every carrier value is admitted under the stated child totals. -/\n" ++
      text ++ s!"\n\n#audit_axioms {qualified}.{env.part "admittedAll"}")))

end P4SpecTec.Codegen.RepresentationTotals
