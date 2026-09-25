import Std.Data.HashMap
import Std.Data.HashSet

/-!
Strongly connected components of a dependency graph over names, in a
topological order of the condensation that follows the input order where
it can: the recursion groups the generator turns into `mutual` blocks.
-/

namespace P4SpecTec.Codegen.Graph

/-- The strongly connected components of the graph whose nodes are `nodes`
(in order) and whose edges are `deps n` restricted to `nodes`. Tarjan's
algorithm; components come out in reverse topological order and are
reversed, so every component's dependencies precede it. Within a
component, nodes keep their input order. -/
def sccs (nodes : List String) (deps : String → List String) : List (List String) := Id.run do
  let nodeSet : Std.HashSet String := Std.HashSet.ofList nodes
  let position : Std.HashMap String Nat :=
    Std.HashMap.ofList (nodes.zipIdx.map fun (n, i) => (n, i))
  let mut index : Std.HashMap String Nat := {}
  let mut low : Std.HashMap String Nat := {}
  let mut onStack : Std.HashSet String := {}
  let mut stack : List String := []
  let mut counter := 0
  let mut out : List (List String) := []
  -- explicit work list instead of recursion
  for start in nodes do
    if index.contains start then continue
    let mut work : List (String × List String) := [(start, (deps start).filter nodeSet.contains)]
    index := index.insert start counter; low := low.insert start counter; counter := counter + 1
    stack := start :: stack; onStack := onStack.insert start
    while !work.isEmpty do
      match work with
      | [] => pure ()
      | (v, succs) :: rest =>
        match succs with
        | w :: succs' =>
          work := (v, succs') :: rest
          if !index.contains w then
            index := index.insert w counter; low := low.insert w counter; counter := counter + 1
            stack := w :: stack; onStack := onStack.insert w
            work := (w, (deps w).filter nodeSet.contains) :: work
          else if onStack.contains w then
            low := low.insert v (min (low.getD v 0) (index.getD w 0))
        | [] =>
          work := rest
          match rest with
          | (u, _) :: _ => low := low.insert u (min (low.getD u 0) (low.getD v 0))
          | [] => pure ()
          if low.getD v 0 == index.getD v 0 then
            let mut comp : List String := []
            let mut go := true
            while go do
              match stack with
              | w :: stack' =>
                stack := stack'; onStack := onStack.erase w; comp := w :: comp
                if w == v then go := false
              | [] => go := false
            out := (comp.mergeSort fun a b => position.getD a 0 ≤ position.getD b 0) :: out
  pure out.reverse

/-- Whether a component is recursive: more than one node, or a self edge. -/
def isRecursive (comp : List String) (deps : String → List String) : Bool :=
  match comp with
  | [n] => (deps n).contains n
  | _ => true

end P4SpecTec.Codegen.Graph
