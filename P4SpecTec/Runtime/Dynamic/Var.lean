import P4SpecTec.Lang.Il.Ast

/-!
Variables of the interpreter's environments: an identifier with its
iteration dimensions. Mirrors `p4spec/lib/runtime/dynamic/var.ml`.
-/

namespace P4SpecTec.Runtime.Dynamic.Var

open P4SpecTec.Lang.Il

/-- Mirrors `Var.t = id * iter list`. -/
abbrev t := Lang.Il.id × List iter

/-- Mirrors `to_string`. -/
def to_string (v : t) : String :=
  v.1.it ++ String.join (v.2.map fun | .Opt => "?" | .List => "*")

/-- Mirrors `compare_iter`. -/
def compare_iter : iter → iter → Ordering
  | .Opt, .Opt | .List, .List => .eq
  | .Opt, .List => .lt
  | .List, .Opt => .gt

/-- Mirrors `compare_iters`. -/
def compare_iters : List iter → List iter → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compare_iter a b).then (compare_iters as bs)

/-- Mirrors `compare`: by id, then by dimensions. -/
def compare (a b : t) : Ordering :=
  (Ord.compare a.1.it b.1.it).then (compare_iters a.2 b.2)

/-- Equality of variables. -/
def eq (a b : t) : Bool := compare a b == .eq

end P4SpecTec.Runtime.Dynamic.Var
