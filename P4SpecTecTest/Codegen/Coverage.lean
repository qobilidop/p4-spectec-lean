import P4SpecTec.Codegen.Emit
import P4SpecTec.Refine.Quote

/-! Coverage planner regressions: direct blockers, dependency closure and SCCs. -/

namespace P4SpecTecTest.Coverage

open P4SpecTec P4SpecTec.Codegen P4SpecTec.Refine

def bool : Lang.Il.exp := Q.e (.BoolE true) .BoolT

def call (name : String) : Lang.Il.exp := Q.e (.CallE (Q.i name) [] []) .BoolT

def func (name : String) (body : Lang.Il.exp) : Lang.Al.def :=
  Q.d (.FuncDecD (Q.i name) [] [] (Q.t .BoolT) [Q.cl [] body []] none [])

-- Membership is executable, but outside the forward proof fragment.
def blocked : Lang.Il.exp :=
  Q.e (.MemE bool (Q.e (.ListE [bool]) (.IterT (Q.t .BoolT) .List))) .BoolT

def fixture : Lang.Al.spec :=
  [func "leaf" bool, func "caller" (call "leaf"), func "blocked" blocked,
    func "dependent" (call "blocked"), func "cycleA" (call "cycleB"),
    func "cycleB" (Q.e (.BinE .AndOp .BoolT (call "cycleA") blocked) .BoolT)]

def report : Except String Codegen.Coverage.Report := Emit.coverage "Fixture" "test.json" fixture

def entry (name : String) : Except String Codegen.Coverage.Entry := do
  let r ← report
  match r.definitions.find? (·.id == name) with
  | some e => pure e
  | none => throw s!"missing entry {name}"

#guard report.isOk
#guard (entry "leaf").toOption.any (·.hasRefinement)
#guard (entry "caller").toOption.any (·.hasRefinement)
#guard (entry "blocked").toOption.any fun e => !e.hasRefinement &&
  e.exclusions.any (·.reason == "membership")
#guard (entry "dependent").toOption.any fun e => !e.hasRefinement &&
  e.exclusions.any (·.dependency == some "blocked")
#guard (entry "cycleA").toOption.any fun e => e.recursive && !e.hasRefinement &&
  e.group == ["cycleA", "cycleB"] &&
  e.exclusions.any fun r => r.definition == "cycleB" && r.reason == "membership"
#guard (report >>= fun r => Codegen.Coverage.closure r "cycleA").toOption.any (·.length == 2)
#guard (report >>= fun r => Codegen.Coverage.closure r "dependent").toOption.any fun es =>
  es.map (·.id) == ["dependent", "blocked"]
#guard !(report >>= fun r => Codegen.Coverage.closure r "missing").isOk
#guard (report >>= fun r => Lean.Json.parse r.render >>= Lean.fromJson?).toOption == report.toOption

def coveredCycle : Lang.Al.spec := [func "a" (call "b"), func "b" (call "a")]

#guard (Emit.coverage "Fixture" "test.json" coveredCycle).toOption.any fun r =>
  r.definitions.length == 2 && r.definitions.all fun e => e.recursive && e.hasRefinement &&
    e.claims.all (·.direction == "referenceToGenerated")

def builtinFixture : Lang.Al.spec :=
  [Q.d (.BuiltinDecD (Q.i "print_") [] [Q.pm (.ExpP (Q.t .TextT))] (Q.t .TextT) []),
    Q.d (.FuncDecD (Q.i "printer") [] [] (Q.t .TextT)
      [Q.cl [] (Q.e (.CallE (Q.i "print_") []
        [Q.ar (.ExpA (Q.e (.TextE (ByteText.ofString "x")) .TextT))]) .TextT) []]
      none [])]

#guard (Emit.coverage "Fixture" "test.json" builtinFixture).toOption.any fun r =>
  (r.definitions.filter (·.isBodied)).length == 1 &&
  r.definitions.all (fun e => !e.hasRefinement) &&
  r.definitions.any fun e => e.id == "printer" &&
    e.exclusions.any (·.reason == "calls a builtin")

def externFixture : Lang.Al.spec :=
  [Q.d (.ExternDecD (Q.i "outside") [] [] (Q.t .BoolT) []),
    func "externalCaller" (call "outside"), func "transitive" (call "externalCaller")]

#guard (Emit.coverage "Fixture" "test.json" externFixture).toOption.any fun r =>
  (r.definitions.filter (·.isBodied)).length == 2 &&
  r.definitions.all (fun e => !e.hasRefinement) &&
  (Codegen.Coverage.closure r "transitive").toOption.any (·.length == 3)

-- Production full-P4 generation remains gated even when metadata is requested.
def stateful : Lang.Al.spec :=
  [Q.d (.BuiltinDecD (Q.i "fresh_typeId") [] [] (Q.t .TextT) [])]

#guard match Emit.coverage "Fixture" "test.json" stateful with
  | .error e =>
    e == "stateful generation requires structural propositions and run-soundness support"
  | .ok _ => false

end P4SpecTecTest.Coverage
