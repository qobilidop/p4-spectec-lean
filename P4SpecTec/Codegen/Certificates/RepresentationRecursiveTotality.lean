import P4SpecTec.Codegen.Certificates.RepresentationRecursiveCodec
import P4SpecTec.Codegen.Certificates.RepresentationTotal

/-!
Complete native-carrier admission for recursive source groups without runtime extensions.
The actual native recursor supplies recursive induction, including nested containers;
independent leaf totality proofs supply every nonrecursive carrier. No codec success,
encoder range, or source derivation is used to establish native admission.
-/

namespace P4SpecTec.Codegen.RepresentationRecursive

open P4SpecTec.Lang.Il

private def structural (family : Family) : Bool :=
  family.leaf.isNone && (match family.source.it, family.body with
    | .IterT _ .List, _ | .IterT _ .Opt, _ | _, some (.VariantT _) => true
    | _, _ => false)

private def totalProof (index : Nat) (proof : String) : String :=
  "/-- Every native value is admitted, from its actual carrier structure. -/\n" ++
    s!"private theorem total{index} (x : Carrier .f{index}) : admitted .f{index} x := by\n" ++
    proof ++ s!"\n\n#audit_axioms total{index}"

private def finish (indices : List Nat) : String :=
  "  all_goals repeat first\n    | assumption\n" ++
    String.join (indices.map fun index => s!"    | exact total{index} _\n") ++
    "    | constructor"

/-- Emit admission totality using actual native recursors and exact independent leaf totals.
Reachable runtime-only constructors and unsupported carrier shapes fail closed. -/
def totalityDeclarations (env : Env) (plan : Plan) (namespaceName : String)
    (known : String → Option RepresentationTotals.TotalContract) : Except String Std.Format := do
  if plan.families.any (·.runtimeExtended) then
    throw "recursive totality rejects reachable runtime-only constructors"
  let mut commands := []
  let mut completed := []
  for family in plan.families, index in List.range plan.families.size do
    if let some contract := family.leaf then
      let proof ← RepresentationTotals.fieldProof env known family.source
      commands := commands ++ [totalProof index
        (s!"  change ({contract.admitted}) x\n  exact ({proof}) x")]
      completed := completed ++ [index]
  let predicates := plan.families.toList.zipIdx.filterMap fun (family, index) =>
    if structural family then some s!"admitted .f{index}" else none
  for (name, index) in plan.roots do
    let some family := plan.families[index]? | throw "recursive root is absent"
    if let some (.VariantT _) := family.body then
      let proof := s!"  carrier_induction {env.q (Names.typeName name)}.rec\n" ++
        "    [" ++ ", ".intercalate predicates ++ "]\n" ++
        "  all_goals intros\n  all_goals dsimp only [admitted] at *\n" ++ finish completed
      commands := commands ++ [totalProof index proof]
      completed := completed ++ [index]
  while completed.length < plan.families.size do
    let mut progress := false
    for family in plan.families, index in List.range plan.families.size do
      if !completed.contains index && family.children.all completed.contains then
        let proof ← match family.source.it, family.body with
          | .IterT _ .List, _ => pure ("  induction x\n" ++ finish completed)
          | .IterT _ .Opt, _ | _, some (.VariantT _) =>
            pure ("  cases x\n" ++ finish completed)
          | _, some (.PlainT _) => pure ("  constructor\n" ++ finish completed)
          | _, _ => throw "recursive totality needs a supported structural carrier"
        commands := commands ++ [totalProof index proof]
        completed := completed ++ [index]
        progress := true
    unless progress do throw "recursive totality carrier dependencies did not close"
  let helper := s!"namespace {namespaceName}\n\n" ++ "\n\n".intercalate commands ++
    s!"\n\nend {namespaceName}"
  let wrappers := plan.roots.map fun (name, index) =>
    let localName := Names.typeName name
    "/-- All native values of this complete source carrier are admitted. -/\n" ++
      s!"theorem {localName}.admittedAll (x : {env.q localName}) : " ++
      s!"{localName}.admitted x := {namespaceName}.total{index} x\n\n" ++
      s!"#audit_axioms {localName}.admittedAll"
  pure (Std.Format.text (boundedLines (helper ++ "\n\n" ++ "\n\n".intercalate wrappers)))

end P4SpecTec.Codegen.RepresentationRecursive
