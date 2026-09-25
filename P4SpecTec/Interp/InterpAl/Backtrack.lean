import P4SpecTec.Prelude.Eval
import P4SpecTec.Util.Source

/-!
Backtracking. Mirrors `p4spec/lib/interp/interp-al/backtrack.ml`,
TRUSTED (design section 5.2). The OCaml's `'a backtrack` (`Ok`, `Err`,
`Unmatch`, each failure with its traces) is `Eval` (`Prelude/Eval.lean`)
here: `Except.ok` is `Ok`, `Except.error Fail.err` is `Err`,
`Except.error Fail.unmatch` is `Unmatch`, and the failure traces are not
kept (deviation, design section 5.3). Its functions are the ones below,
in the OCaml's order; `( let* )` is `do` notation.
-/

namespace P4SpecTec.Interp_al.Backtrack

open P4SpecTec.Util.Source
open P4SpecTec.Prelude

/-- Mirrors `'a backtrack`: `Eval`. -/
abbrev backtrack (α : Type) := Eval α

/-- Mirrors `back_err`. -/
def back_err {α : Type} (_at : region) (_msg : String) : backtrack α := throw .err

/-- Mirrors `back_unmatch_silent`. -/
def back_unmatch_silent {α : Type} : backtrack α := throw .unmatch

/-- Mirrors `back_unmatch`. -/
def back_unmatch {α : Type} (_at : region) (_msg : String) : backtrack α := throw .unmatch

/-- Mirrors `back_nest`: without traces, the identity. -/
def back_nest {α : Type} (_at : region) (_msg : Unit → String) (b : backtrack α) : backtrack α := b

/-- Mirrors `check_back_err`. -/
def check_back_err (b : Bool) («at» : region) (msg : String) : backtrack Unit :=
  if b then pure () else back_err «at» msg

/-- Mirrors `choose_sequential`: the first alternative that is not
`Unmatch`; an `Err` stops the search. -/
def choose_sequential {α : Type} : List (Unit → backtrack α) → backtrack α
  | [] => back_unmatch_silent
  | f :: fs => Eval.orElse (f ()) (choose_sequential fs)

end P4SpecTec.Interp_al.Backtrack
