import P4SpecTec.Codegen.Funcs
import P4SpecTec.Refine.Quote

/-! Consumer reachability preserves source order and excludes recursive peers. -/

namespace P4SpecTecTest.Monotonicity

open P4SpecTec P4SpecTec.Codegen P4SpecTec.Refine

-- This bounded reference saturates paths independently of the work-list traversal.
def closure (edges : List (String × List String)) (start : String) : List String :=
  (List.range edges.length).foldl (init := [start]) fun seen _ =>
    edges.foldl (init := seen) fun reached (name, deps) =>
      if reached.contains name then (reached ++ deps).eraseDups else reached

def call (name : String) : Lang.Il.exp := Q.e (.CallE (Q.i name) [] []) .BoolT

def func (name : String) (deps : List String) (callback : Bool := true) : Lang.Al.def :=
  let params := if callback then [Q.pm (.DefP (Q.i "callback") [] [] (Q.t .BoolT))] else []
  let body := deps.foldr (fun dep acc => Q.e (.BinE .AndOp .BoolT (call dep) acc) .BoolT)
    (Q.e (.BoolE true) .BoolT)
  Q.d (.FuncDecD (Q.i name) [] params (Q.t .BoolT) [Q.cl [] body []] none [])

def nodes : List String := ["a", "b", "c"]

def edgesOf (mask : Nat) : List (String × List String) :=
  nodes.zipIdx.map fun (name, i) =>
    (name, nodes.zipIdx.filterMap fun (dep, j) =>
      if mask / 2 ^ (3 * i + j) % 2 == 1 then some dep else none)

def agrees (edges : List (String × List String)) : Bool :=
  let env := Env.ofSpec "Fixture" (edges.map fun (name, deps) => func name deps)
  let adjacency := Std.HashMap.ofList edges
  nodes.all fun start =>
    let forward := closure edges start
    let expected := edges.filterMap fun (name, _) =>
      if forward.contains name && !(closure edges name).contains start then
        some (env.q (Names.funcName name)) else none
    nodes.all (fun name => (Graph.reachable adjacency start).contains name ==
      forward.contains name) && Funcs.monotonicityConsumers env start == expected

-- Every directed graph on three vertices: self loops, cycles, forks and disconnected nodes.
#guard (List.range 512).all (agrees ∘ edgesOf)

-- Missing adjacency entries are leaves and duplicate edges do not duplicate traversal.
#guard (Graph.reachable (Std.HashMap.ofList [("a", ["outside", "outside"])]) "a").size == 2
#guard (Graph.reachable {} "outside").contains "outside"

-- Retain source order, exclude the caller's SCC, and return nothing without a callback consumer.
def ordered : Lang.Al.spec :=
  [func "later" [], func "a" ["b", "later", "earlier"],
    func "earlier" [], func "b" ["a"]]
#guard Funcs.monotonicityConsumers (Env.ofSpec "Fixture" ordered) "a" ==
  ["Fixture.«$later»", "Fixture.«$earlier»"]
#guard Funcs.monotonicityConsumers
  (Env.ofSpec "Fixture" [func "plain" [] false, func "caller" ["plain"]]) "caller" == []

-- Repeated names contribute every body; callback gating retains plain consumers and duplicates.
def duplicateNames : Lang.Al.spec :=
  [func "plain" [] false, func "plain" [] false, func "callback" [],
    func "a" ["plain"], func "a" ["callback"], func "unused" []]
#guard Funcs.monotonicityConsumers (Env.ofSpec "Fixture" duplicateNames) "a" ==
  ["Fixture.«$plain»", "Fixture.«$plain»", "Fixture.«$callback»"]

end P4SpecTecTest.Monotonicity
