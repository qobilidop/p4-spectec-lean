import P4SpecTec.BackendSim.Stf.Ast

/-!
Port of `p4spec/lib/stf/transform.ml` and the string helpers `make.ml` applies to STF
statements: the case-insensitive name rewriting of `Transform.Name`, the `$valid$`
rewriting of `Transform.Match`, `Stf.Print.convert_dollar_to_brackets`, OCaml's
`String.escaped`, `String.uppercase_ascii` and `int_of_string`.
-/

namespace P4SpecTec.BackendSim.Stf.Transform

/-- ASCII lowercase, as `Core.String.lowercase`. -/
def lowerAscii (s : String) : String := s.map Char.toLower

/-- Mirrors `Core.String.Caseless.is_substring`. -/
def isSubstringCaseless (s substring : String) : Bool :=
  (lowerAscii substring).isPrefixOf (lowerAscii s) ||
    ((lowerAscii s).splitOn (lowerAscii substring)).length > 1

/-- Mirrors `Transform.Name.rewrite_substring`: when the first dotted component contains
one of the substrings, case-insensitively, it is replaced as a whole. -/
def rewrite_substring (substrings : List String) (replacement : String) (name : String) :
    String :=
  match name.splitOn "." with
  | [] => name
  | hd :: tl =>
    let hd := if substrings.any (isSubstringCaseless hd) then replacement else hd
    ".".intercalate (hd :: tl)

/-- Mirrors `Core.String.Caseless.substr_replace_first`: the first case-insensitive
occurrence of the pattern, which must occur, is replaced. -/
def replaceFirstCaseless (s pattern replacement : String) : String :=
  match (lowerAscii s).splitOn (lowerAscii pattern) with
  | [] | [_] => s
  | before :: _ =>
    let chars := s.toList
    String.ofList (chars.take before.length) ++ replacement ++
      String.ofList (chars.drop (before.length + pattern.length))

/-- Mirrors `Transform.Name.replace_substring`: for each substring in turn, when the name
contains it case-insensitively, its first occurrence is replaced. -/
def replace_substring (substrings : List String) (replacement : String) (name : String) :
    String :=
  substrings.foldl (fun name substring =>
    if isSubstringCaseless name substring then replaceFirstCaseless name substring replacement
    else name) name

/-- Mirrors `Transform.Action.into_unqualified`: the last dotted component of the name. -/
def into_unqualified (action : Ast.action) : Ast.action :=
  (((action.1.splitOn ".").getLast?.getD action.1), action.2)

/-- Mirrors `Transform.Match.rewrite_valid`: every `$valid$` becomes `isValid()`. -/
def rewrite_valid (m : Ast.mtch) : Ast.mtch :=
  ("isValid()".intercalate (m.1.splitOn "$valid$"), m.2)

/-- Mirrors `Stf.Print.convert_dollar_to_brackets`: `$N` becomes `[N]` for every decimal
`N`, as `Str.global_replace "\\$\\([0-9]+\\)" "[\\1]"` does. -/
def convert_dollar_to_brackets (s : String) : String := Id.run do
  let chars := s.toList.toArray
  let mut out := ""
  let mut i := 0
  while i < chars.size do
    let c := chars[i]!
    if c == '$' then
      let mut j := i + 1
      while j < chars.size && chars[j]!.isDigit do j := j + 1
      if j > i + 1 then
        out := out ++ "[" ++ String.ofList (chars.extract (i + 1) j).toList ++ "]"
        i := j
      else
        out := out.push c
        i := i + 1
    else
      out := out.push c
      i := i + 1
  pure out

/-- Mirrors OCaml's `String.escaped` on ASCII text: quotes, backslashes and the named
control characters get a backslash, other non-printable bytes a decimal escape. -/
def escaped (s : String) : String := Id.run do
  let mut out := ""
  for c in s.toList do
    let n := c.toNat
    if c == '"' then out := out ++ "\\\""
    else if c == '\\' then out := out ++ "\\\\"
    else if c == '\n' then out := out ++ "\\n"
    else if c == '\t' then out := out ++ "\\t"
    else if c == '\r' then out := out ++ "\\r"
    else if n == 8 then out := out ++ "\\b"
    else if 32 ≤ n && n ≤ 126 then out := out.push c
    else if n < 256 then
      out := out ++ "\\" ++ (if n < 100 then "0" else "") ++ (if n < 10 then "0" else "") ++
        toString n
    else out := out.push c
  pure out

/-- Mirrors `String.uppercase_ascii`. -/
def upperAscii (s : String) : String := s.map Char.toUpper

/-- Digits of a radix, with OCaml's `_` separators allowed. -/
private def digitsOf (radix : Nat) (s : List Char) : Option Nat := do
  let mut n := 0
  let mut any := false
  for c in s do
    if c == '_' then continue
    let d ← if c.isDigit then some (c.toNat - 48)
      else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 97 + 10)
      else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 65 + 10)
      else none
    if d ≥ radix then none
    n := n * radix + d
    any := true
  if any then some n else none

/-- Mirrors OCaml's `int_of_string`: an optional sign, then decimal, or `0x`, `0o`, `0b`
prefixed digits; anything else fails. The 63-bit range is not checked. -/
def int_of_string (s : String) : Option Int := do
  let chars := s.toList
  let (negative, rest) := match chars with
    | '-' :: rest => (true, rest)
    | '+' :: rest => (false, rest)
    | rest => (false, rest)
  let magnitude ← match rest with
    | '0' :: c :: digits =>
      if c == 'x' || c == 'X' then digitsOf 16 digits
      else if c == 'o' || c == 'O' then digitsOf 8 digits
      else if c == 'b' || c == 'B' then digitsOf 2 digits
      else if c == 'u' || c == 'U' then digitsOf 10 digits
      else digitsOf 10 rest
    | _ => digitsOf 10 rest
  pure (if negative then -(magnitude : Int) else magnitude)

end P4SpecTec.BackendSim.Stf.Transform
