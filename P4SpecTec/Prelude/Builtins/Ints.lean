/-!
Integer builtins. Mirrors `p4spec/lib/interface/builtin/ints.ml`.
-/

namespace P4SpecTec.Prelude.Builtins.Ints

/-- `dec $sum_int(int*) : int`. -/
def sum_int (is : List Int) : Int := is.foldl (· + ·) 0

/-- `dec $max_int(int*) : int`; zero on the empty list, as upstream. -/
def max_int (is : List Int) : Int := is.foldl max (is.headD 0)

/-- `dec $min_int(int*) : int`; zero on the empty list, as upstream. -/
def min_int (is : List Int) : Int := is.foldl min (is.headD 0)

end P4SpecTec.Prelude.Builtins.Ints
