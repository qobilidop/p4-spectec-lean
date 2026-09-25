import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Lang.Al.Ast
import P4SpecTec.Lang.Hints.AlterJson

/-!
The P4 value printer and AL hint environment. Mirrors `pp_value` and its
helpers of `p4spec/lib/interface/p4/unparse.ml`: `printWithHints` selects
alternation policies by runtime type identifier and case mixop, or falls
back to ordinary mixfix rendering. Unsupported value shapes return errors
instead of OCaml exceptions. Builtins use this checked entry point; the
older `print` entry point retains its hint-free placeholder behavior.
Text escapes operate on UTF-8 bytes and atom case conversion is ASCII-only,
as in OCaml. Hints preserve empty positions, unlike default mixfix assembly.
-/

namespace P4SpecTec.P4.Unparse

open P4SpecTec.Lang.Xl
open P4SpecTec.Domain
open P4SpecTec.Lang.Il
open P4SpecTec.Util.Source

/-- Mirrors `HEnv`: print policies keyed by type identifier and mixop.
Newest entries are first, matching upstream environment replacement. -/
abbrev HEnv := List (String × Mixfix.mixop × Lang.Hints.Alter.t)

/-- The hint name consumed by the value printer. -/
def hintid : String := "print"

/-- Look up a case's policy without consulting unrelated type families. -/
def find_hint (henv : HEnv) (tid : String) (mixop : Mixfix.mixop) :
    Option Lang.Hints.Alter.t :=
  (henv.find? fun (name, op, _) => name == tid && Mixfix.eq_mixop op mixop).map (·.2.2)

/-- Mirrors `hints_of_typcase`: take the first print hint, decode its
supported alternation syntax and reject invalid placeholder indices. -/
def hints_of_typcase (henv : HEnv) (tid : id) (c : typcase) : Except String HEnv := do
  let .mk n _ hs := c
  for h in hs do
    let body ← Util.Yojson.field h "it"
    let name ← Util.Yojson.str (← Util.Yojson.field (← Util.Yojson.field body "hintid") "it")
    if name == hintid then
      let policy ← Lang.Hints.AlterJson.decode (← Util.Yojson.field body "hintexp")
      match Lang.Hints.Alter.validate policy (Mixfix.arity n.it) with
      | .error e => throw s!"invalid print hint on {tid.it} at {string_of_region n.at}: \
          placeholder index {e.index} outside arity {e.arity}"
      | .ok () => pure ()
      return (tid.it, Mixfix.to_mixop n.it, policy) :: henv
  pure henv

/-- Mirrors `hints_of_typcases`, preserving specification insertion order. -/
def hints_of_typcases (henv : HEnv) (tid : id) (cs : List typcase) : Except String HEnv :=
  cs.foldlM (fun env c => hints_of_typcase env tid c) henv

/-- Mirrors `hints_of_deftyp`: only variant cases select value printers. -/
def hints_of_deftyp (henv : HEnv) (tid : id) (dt : deftyp) : Except String HEnv :=
  match dt.it with
  | .VariantT cs => hints_of_typcases henv tid cs
  | _ => pure henv

/-- Mirrors `hints_of_def_al`. -/
def hints_of_def_al (henv : HEnv) (d : Lang.Al.def) : Except String HEnv :=
  match d.it with
  | .TypD i _ dt _ => hints_of_deftyp henv i dt
  | _ => pure henv

/-- Mirrors `hints_of_spec_al`; unsupported hint forms fail explicitly. -/
def hints_of_spec_al (spec : Lang.Al.spec) : Except String HEnv :=
  spec.foldlM hints_of_def_al []

/-- Mirrors OCaml's `String.escaped`, which `pp_text_v` applies: backslash,
double quote, newline, tab and carriage return by their escapes, other
non-printable bytes as `\\ddd`. -/
def escaped (s : String) : String :=
  String.join (s.toUTF8.toList.map fun b =>
    match b.toNat with
    | 92 => "\\\\" | 34 => "\\\"" | 10 => "\\n" | 9 => "\\t" | 13 => "\\r" | 8 => "\\b"
    | d =>
      if d < 32 || d ≥ 127 then
        "\\" ++ toString (d / 100) ++ toString (d / 10 % 10) ++ toString (d % 10)
      else String.singleton (Char.ofNat d))

/-- Mirrors `pp_num`. -/
def ppNum : Num.t → String
  | .Nat n => toString n
  | .Int i => (if i ≥ 0 then "" else "-") ++ toString i.natAbs

/-- Mirrors `pp_atom`: tags print as nothing, other atoms lower-cased. -/
def ppAtom (a : Atom.t) : String :=
  match a with
  | .Tag _ => ""
  | a => (Mixfix.to_string.render a).map fun c =>
      if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

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

/-- Sequence only the documents actually selected by an alternation.
Unlike default mixfix assembly, an empty document keeps its position. -/
def joinDocs (separator : String) (docs : List (Except String String)) : Except String String := do
  pure (separator.intercalate (← docs.mapM fun d => d))

/-- Mirrors `pp_hint_case_v` on pre-rendered argument results. Keeping
results separate avoids propagating errors from unused placeholders. -/
def printHint (hint : Lang.Hints.Alter.t) (args : List (Except String String)) :
    Except String String := do
  let result ← Lang.Hints.Alter.alternate (.ok "")
    (fun s => if s == "" then none else some (.ok s))
    (fun a => .ok (ppAtom a.it)) (joinDocs " ")
    (fun l r => do pure ((← l) ++ (← r))) hint (fun d => d) args
  result

mutual

/-- The note-aware upstream value printer. Unsupported value shapes and
invalid alternations are errors, not invented printable placeholders. -/
def printWithHints (henv : HEnv) : value → Except String String
  | ⟨v, note, _⟩ =>
    match v with
    | .BoolV b => pure (toString b)
    | .NumV n => pure (ppNum n)
    | .TextV s => pure (escaped s)
    | .CaseV c =>
      let policy := match note.typ with
        | .VarT i _ => find_hint henv i.it (Mixfix.to_mixop c)
        | _ => none
      match policy with
      | some hint => printHint hint (printArgs henv c)
      | none => printMixfixWithHints henv c
    | .TupleV vs => do pure ("(" ++ (← joinDocs ", " (printDocs henv vs)) ++ ")")
    | .OptV (some v) => printWithHints henv v
    | .OptV none => pure ""
    | .ListV vs => joinDocs " " (printDocs henv vs)
    | .StructV _ => throw "pp_value: StructV not implemented"
    | .FuncV _ | .ExternV _ => throw "pp_value: unsupported value"

/-- Value printing over a list, without sequencing failures prematurely. -/
def printDocs (henv : HEnv) : List value → List (Except String String)
  | [] => []
  | v :: vs => printWithHints henv v :: printDocs henv vs

/-- Render case arguments in mixfix order, preserving unused failures as
data for the hint's placeholder selection. -/
def printArgs (henv : HEnv) : Mixfix.t value → List (Except String String)
  | .Arg v => [printWithHints henv v]
  | .Atom _ => []
  | .Brack _ m _ => printArgs henv m
  | .Infix l _ r => printArgs henv l ++ printArgs henv r
  | .Seq ms => printArgsList henv ms

/-- Case argument rendering over a sequence. -/
def printArgsList (henv : HEnv) : List (Mixfix.t value) → List (Except String String)
  | [] => []
  | m :: ms => printArgs henv m ++ printArgsList henv ms

/-- Mirrors `pp_default_case_v` with recursive note-aware argument printing. -/
def printMixfixWithHints (henv : HEnv) : Mixfix.t value → Except String String
  | .Arg v => printWithHints henv v
  | .Atom a => pure (ppAtom a.it)
  | .Brack l m r => do pure (join [ppAtom l.it, ← printMixfixWithHints henv m, ppAtom r.it])
  | .Infix l a r => do
    pure (join [← printMixfixWithHints henv l, ppAtom a.it, ← printMixfixWithHints henv r])
  | .Seq ms => do pure (join (← printMixfixDocs henv ms))

/-- Default mixfix rendering over a sequence. -/
def printMixfixDocs (henv : HEnv) : List (Mixfix.t value) → Except String (List String)
  | [] => pure []
  | m :: ms => do pure ((← printMixfixWithHints henv m) :: (← printMixfixDocs henv ms))

end

end P4SpecTec.P4.Unparse
