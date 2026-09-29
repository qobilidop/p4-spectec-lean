import P4SpecTec.Codegen.Emit
import P4SpecTec.Refine.Quote

/-! Coverage planner regressions: direct blockers, dependency closure and SCCs. -/

namespace P4SpecTecTest.Coverage

open P4SpecTec P4SpecTec.Codegen P4SpecTec.Refine

def bool : Lang.Il.exp := Q.e (.BoolE true) .BoolT

def call (name : String) : Lang.Il.exp := Q.e (.CallE (Q.i name) [] []) .BoolT

def func (name : String) (body : Lang.Il.exp) : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i name) [] [] (Q.t .BoolT) [Q.cl [] body []] none [])

-- Indexing outside a list is executable, but outside the forward proof fragment.
def blocked : Lang.Il.exp :=
  Q.e (.IdxE bool bool) .BoolT

def fixture : Lang.Al.spec :=
  [func "leaf" bool, func "caller" (call "leaf"), func "blocked" blocked,
    func "dependent" (call "blocked"), func "cycleA" (call "cycleB"),
    func "cycleB" (Q.e (.BinE .AndOp .BoolT (call "cycleA") blocked) .BoolT)]

def report : Except String Codegen.Coverage.Report := Emit.coverage "Fixture" "test.json" fixture

private def groups (spec : Lang.Al.spec) : Option (List Emit.RefGroup) := do
  let (_, _, refinement) ← (Emit.plan (Env.ofSpec "Fixture" spec) spec).toOption
  pure refinement.groups

private def groupNamed (spec : Lang.Al.spec) (name : String) : Option Emit.RefGroup := do
  (← groups spec).find? (·.name == name)

-- Invocation directions have independent callee chains; the old module is an aggregate.
#guard (groupNamed fixture "Forward.caller").any (·.deps == ["Forward.leaf"])
#guard (groupNamed fixture "Reverse.caller").any (·.deps == ["Reverse.leaf"])
#guard (groupNamed fixture "caller").any (·.deps ==
  ["Forward.caller", "Reverse.caller"])
#guard (groupNamed fixture "Forward.leaf").isSome
#guard (groupNamed fixture "Reverse.leaf").isSome
#guard (groupNamed fixture "Forward.blocked").isNone
#guard (groupNamed fixture "Reverse.blocked").isNone

private def emittedDirections : Except String (List Emit.Output) :=
  Emit.generate "Fixture" "test.json" [func "leaf" bool, func "caller" (call "leaf")]

#guard emittedDirections.toOption.any fun outputs =>
  let source (path : String) := (outputs.find? (·.path == path)).map (·.text)
  (source "Fixture/Refinement/Forward/caller.lean").any
    (fun body => body.contains "import Fixture.Refinement.Forward.leaf\n" &&
      !(body.contains "import P4SpecTec.Tactic.Realize\n")) &&
  (source "Fixture/Refinement/Reverse/caller.lean").any
    (fun body => body.contains "import Fixture.Refinement.Reverse.leaf\n" &&
      body.contains "import P4SpecTec.Tactic.Realize\n") &&
  (source "Fixture/Refinement/caller.lean").any fun body =>
    body.contains "import Fixture.Refinement.Forward.caller\n" &&
      body.contains "import Fixture.Refinement.Reverse.caller\n" &&
      !(body.contains "theorem caller.refines") && !(body.contains "theorem caller.realizes")

def entry (name : String) : Except String Codegen.Coverage.Entry := do
  let r ← report
  match r.definitions.find? (·.id == name) with
  | some e => pure e
  | none => throw s!"missing entry {name}"

#guard report.isOk
#guard (entry "leaf").toOption.any (·.hasForwardRefinement)
#guard (entry "caller").toOption.any (·.hasForwardRefinement)
#guard (entry "leaf").toOption.any (·.hasReverseRefinement)
#guard (entry "caller").toOption.any (·.hasReverseRefinement)
#guard (entry "blocked").toOption.any fun e => !e.hasForwardRefinement &&
  e.exclusions.any (·.reason == "indexing")
#guard (entry "dependent").toOption.any fun e => !e.hasForwardRefinement &&
  e.exclusions.any (·.dependency == some "blocked")
#guard (entry "cycleA").toOption.any fun e => e.recursive && !e.hasForwardRefinement &&
  e.group == ["cycleA", "cycleB"] &&
  e.exclusions.any fun r => r.definition == "cycleB" && r.reason == "indexing"
#guard (report >>= fun r => Codegen.Coverage.closure r "cycleA").toOption.any (·.length == 2)
#guard (report >>= fun r => Codegen.Coverage.closure r "dependent").toOption.any fun es =>
  es.map (·.id) == ["dependent", "blocked"]
#guard !(report >>= fun r => Codegen.Coverage.closure r "missing").isOk
#guard (report >>= fun r => Lean.Json.parse r.render >>= Lean.fromJson?).toOption == report.toOption

-- Opposite-direction claims must never count as a forward certificate.
def reverseOnly : Codegen.Coverage.Entry := {
  id := "f", kind := "function", source := "fixture", group := ["f"], recursive := false
  dependencies := [], exclusions := []
  claims := [{
    name := "Fixture.f.realizes", kind := "refinement"
    direction := "generatedToReference", expectedType := "True" }] }

#guard reverseOnly.hasReverseRefinement && !reverseOnly.hasForwardRefinement

def coveredCycle : Lang.Al.spec := [func "a" (call "b"), func "b" (call "a")]

-- Joint recursive induction stays in one module for each direction.
#guard (groups coveredCycle).any fun modules =>
  (modules.filter (·.name.startsWith "Forward.")).length == 1 &&
  (modules.filter (·.name.startsWith "Reverse.")).length == 1 &&
  (modules.filter (fun g => ((render g.decls).splitOn "refines_group").length > 1)).length == 1 &&
  (modules.filter (fun g => ((render g.decls).splitOn "realizes_group").length > 1)).length == 1

-- A mutual recursive group is certified in both directions, and so are its callers.
#guard (Emit.coverage "Fixture" "test.json" coveredCycle).toOption.any fun r =>
  r.definitions.length == 2 && r.definitions.all fun e => e.recursive &&
    e.hasForwardRefinement && e.hasReverseRefinement

def cycleCaller : Lang.Al.spec := coveredCycle ++ [func "caller" (call "a")]

#guard (Emit.coverage "Fixture" "test.json" cycleCaller).toOption.any fun r =>
  r.definitions.all fun e => e.hasForwardRefinement && e.hasReverseRefinement

def builtinFixture : Lang.Al.spec :=
  [Q.d (.BuiltinDecD (Q.i "print_") [] [Q.pm (.ExpP (Q.t .TextT))] (Q.t .TextT) []),
    Q.d (.FuncDecD (Q.i "printer") [] [] (Q.t .TextT)
      [Q.cl [] (Q.e (.CallE (Q.i "print_") []
        [Q.ar (.ExpA (Q.e (.TextE (ByteText.ofString "x")) .TextT))]) .TextT) []]
      none [])]

#guard (Emit.coverage "Fixture" "test.json" builtinFixture).toOption.any fun r =>
  (r.definitions.filter (·.isBodied)).length == 1 &&
  r.definitions.all (fun e => !e.hasForwardRefinement) &&
  r.definitions.any fun e => e.id == "printer" &&
    e.exclusions.any (·.reason == "calls a builtin")

-- Actual supported signatures get checked dispatch and both invocation directions,
-- while remaining outside the bodied-definition denominator and caller frontier.
def supportedBuiltin : Lang.Al.spec :=
  [Q.d (.BuiltinDecD (Q.i "print_") [Q.i "A"]
    [Q.pm (.ExpP (Q.t (.VarT (Q.i "A") [])))] (Q.t .TextT) [])]

#guard (Emit.coverage "Fixture" "test.json" supportedBuiltin).toOption.any fun r =>
  r.definitions.length == 1 && r.definitions.all fun e =>
    !e.isBodied && e.hasBuiltinContract && e.hasForwardRefinement && e.hasReverseRefinement &&
      e.claims.length == 4 && e.exclusions.isEmpty &&
      e.claims.any (fun c => c.kind == "sourceDomain" && c.direction == "sourceInputsAndOutput")

def externFixture : Lang.Al.spec :=
  [Q.d (.ExternDecD (Q.i "outside") [] [] (Q.t .BoolT) []),
    func "externalCaller" (call "outside"), func "transitive" (call "externalCaller")]

#guard (Emit.coverage "Fixture" "test.json" externFixture).toOption.any fun r =>
  (r.definitions.filter (·.isBodied)).length == 2 &&
  r.definitions.all (fun e => !e.hasForwardRefinement) &&
  (Codegen.Coverage.closure r "transitive").toOption.any (·.length == 3)

-- Production full-P4 generation remains gated even when metadata is requested.
def stateful : Lang.Al.spec :=
  [Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] (Q.t .TextT) [])]

#guard match Emit.coverage "Fixture" "test.json" stateful with
  | .error e =>
    e == "stateful generation requires structural propositions and run-soundness support"
  | .ok _ => false

-- Long transitive blocker diagnostics remain comments within the generated line limit.
#guard ((Codegen.Coverage.summary [{ reverseOnly with claims := [], exclusions := [{
  definition := "a_long_recursive_group_member", kind := "refinement",
  reason := "recursive function subtype or registration-freshness proof is not implemented" }] }]
  ).splitOn "\n").all (fun line => line.length ≤ 100)

end P4SpecTecTest.Coverage
