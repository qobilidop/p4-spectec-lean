import P4SpecTec.Runtime.Value.Value

/-!
The default value printer. Mirrors `pp_value` and its helpers of
`p4spec/lib/interface/p4/unparse.ml` for a spec that declares no `print`
hint (the hint environment is empty); the namespace is upstream's module
name `P4.Unparse`: a case is rendered by `Mixfix.render`
with its atoms lower-cased and tags silent, a list by its elements
space-separated, an option by its content. The `print_` builtin uses it.
-/

namespace P4SpecTec.P4.Unparse

open P4SpecTec.Lang.Xl
open P4SpecTec.Domain
open P4SpecTec.Lang.Il

/-- Mirrors OCaml's `String.escaped`, which `pp_text_v` applies: backslash,
double quote, newline, tab and carriage return by their escapes, other
non-printable bytes as `\\ddd`. -/
def escaped (s : String) : String :=
  String.join (s.toList.map fun c =>
    match c with
    | '\\' => "\\\\" | '"' => "\\\"" | '\n' => "\\n" | '\t' => "\\t" | '\r' => "\\r"
    | c =>
      if c.toNat < 32 || c.toNat = 127 then
        let d := c.toNat
        "\\" ++ toString (d / 100) ++ toString (d / 10 % 10) ++ toString (d % 10)
      else String.singleton c)

/-- Mirrors `pp_num`. -/
def ppNum : Num.t → String
  | .Nat n => toString n
  | .Int i => (if i ≥ 0 then "" else "-") ++ toString i.natAbs

/-- Mirrors `pp_atom`: tags print as nothing, other atoms lower-cased. -/
def ppAtom (a : Atom.t) : String :=
  match a with
  | .Tag _ => ""
  | a => (Mixfix.to_string.render a).toLower

/-- Join the non-empty pieces with spaces, as `Mixfix.assemble` does. -/
def join (pieces : List String) : String :=
  " ".intercalate (pieces.filter (· ≠ ""))

mutual

/-- Mirrors `pp_value` without hints. -/
def print : value → String
  | ⟨v, _, _⟩ => print' v

/-- `print` on the payload. -/
def print' : value' → String
  | .BoolV b => toString b
  | .NumV n => ppNum n
  | .TextV s => escaped s
  | .StructV _ => "<struct>"
  | .CaseV c => printMixfix c
  | .TupleV vs => "(" ++ ", ".intercalate (printList vs) ++ ")"
  | .OptV (some v) => print v
  | .OptV none => ""
  | .ListV vs => " ".intercalate (printList vs)
  | .FuncV i => "$" ++ i.it
  | .ExternV j => j.compress

/-- `pp_value` over a list. -/
def printList : List value → List String
  | [] => []
  | v :: vs => print v :: printList vs

/-- Mirrors `pp_default_case_v`: `Mixfix.render` with `pp_atom`. -/
def printMixfix : Mixfix.t value → String
  | .Arg v => print v
  | .Atom a => ppAtom a.it
  | .Brack l m r => join [ppAtom l.it, printMixfix m, ppAtom r.it]
  | .Infix l a r => join [printMixfix l, ppAtom a.it, printMixfix r]
  | .Seq ms => join (printMixfixes ms)

/-- `pp_default_case_v` over a sequence. -/
def printMixfixes : List (Mixfix.t value) → List String
  | [] => []
  | m :: ms => printMixfix m :: printMixfixes ms

end

end P4SpecTec.P4.Unparse
