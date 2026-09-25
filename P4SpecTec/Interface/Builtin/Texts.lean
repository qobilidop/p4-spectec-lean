import P4SpecTec.Prelude.Value

/-!
Text builtins. Mirrors `p4spec/lib/interface/builtin/texts.ml`, function
for function, on `String`.
-/

namespace P4SpecTec.Builtin.Texts

/-- `dec $text_to_int(text) : int`; `none` where `Bigint.of_string` raises. -/
def text_to_int (s : String) : Option Int := s.toInt?

/-- `dec $int_to_text(int) : text` (`Num.string_of_num`, with a sign). -/
def int_to_text (i : Int) : String := (if i ≥ 0 then "+" else "-") ++ toString i.natAbs

/-- `dec $split_text(text, text) : text*`; the separator is one character. -/
def split_text (s sep : String) : Option (List String) :=
  if sep.length == 1 then some (s.splitOn sep) else none

/-- `dec $strip_prefix(text, text) : text`. -/
def strip_prefix (s prefix_ : String) : Option String :=
  if s.startsWith prefix_ then some (String.ofList (s.toList.drop prefix_.length)) else none

/-- `dec $strip_suffix(text, text) : text`. -/
def strip_suffix (s suffix : String) : Option String :=
  if s.endsWith suffix then some (String.ofList (s.toList.take (s.length - suffix.length)))
  else none

/-- `dec $strip_all_whitespace(text) : text`: removes spaces. -/
def strip_all_whitespace (s : String) : String := "".intercalate (s.splitOn " ")

end P4SpecTec.Builtin.Texts
