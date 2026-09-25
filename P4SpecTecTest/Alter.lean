import P4SpecTec.Lang.Hints.AlterJson

/-! Tests for exported alteration JSON and upstream's cursor semantics. -/

namespace P4SpecTecTest.Alter

open Lean (Json)
open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Hints

def loc : Json :=
  ((Json.parse ("{\"left\":{\"file\":\"fixture\",\"line\":1,\"column\":0}," ++
    "\"right\":{\"file\":\"fixture\",\"line\":1,\"column\":1}}")).toOption).getD .null

def phraseJson (it : Json) : Json := Json.mkObj [
  ("it", it), ("note", .null), ("at", loc)]

def textJson (s : String) : Json := phraseJson (.arr #[.str "TextE", .str s])

def atomJson (a : Json) : Json := phraseJson (.arr #[.str "AtomE", phraseJson a])

def holeJson (h : Json) : Json := phraseJson (.arr #[.str "HoleE", h])

def exported : Json := phraseJson (.arr #[.str "SeqE", .arr #[
  textJson "pre",
  atomJson (.arr #[.str "Keyword", .str "K"]),
  phraseJson (.arr #[.str "BrackE",
    phraseJson (.arr #[.str "LParen"]),
    holeJson (.arr #[.str "Next"]),
    phraseJson (.arr #[.str "RParen"])]),
  phraseJson (.arr #[.str "FuseE",
    textJson "x", loc, holeJson (.arr #[.str "Num", .num 1])])]])

def decoded : Except String Alter.t := AlterJson.decode exported

-- A literal excerpt in the shape emitted by `ppx_deriving_yojson`.
def literalHole : Except String Alter.t := do
  let j ← Json.parse ("{\"it\":[\"HoleE\",[\"Next\"]],\"note\":null," ++
    "\"at\":{\"left\":{\"file\":\"fixture\",\"line\":1,\"column\":0}," ++
    "\"right\":{\"file\":\"fixture\",\"line\":1,\"column\":1}}}")
  AlterJson.decode j

#guard decoded.isOk
#guard literalHole.isOk
#guard (AlterJson.ofHint (Json.mkObj [("hintid", phraseJson (.str "print")),
  ("hintexp", exported)])).isOk
#guard !(AlterJson.decode (phraseJson (.arr #[.str "VarE", phraseJson (.str "x")]))).isOk
#guard !(AlterJson.decode (holeJson (.arr #[.str "Rest"]))).isOk
#guard !(AlterJson.decode (holeJson (.arr #[.str "None"]))).isOk
#guard !(AlterJson.decode (phraseJson (.arr #[.str "TextE"]))).isOk
#guard !(AlterJson.decode (.arr #[.str "TextE", .str "x"])).isOk

def next : Alter.t := .HoleH (mkPhrase .Next)
def num (i : Int) : Alter.t := .HoleH (mkPhrase (.Num i))

def render (hint : Alter.t) (items : List String) : Except String String :=
  Alter.alternate "" (fun s => if s.isEmpty then none else some s)
    (fun a => Atom.string_of_atom a.it) (" ".intercalate ·)
    (· ++ ·) hint id items

-- An explicit position does not advance the implicit cursor.
#guard (render (.SeqH [num 1, next, next]) ["a", "b"]).toOption == some "b a b"
#guard (Alter.validate' 0 (.SeqH [num 1, next, next]) 2).toOption == some 2
#guard (Alter.validate (.SeqH [num 1, next, next]) 2).isOk
#guard !(Alter.validate (.SeqH [next, next, next]) 2).isOk
#guard !(Alter.validate (num (-1)) 2).isOk
#guard !(Alter.validate (num 2) 2).isOk

def invalidIndex (result : Except Alter.invalid_oob Unit) : Option Int :=
  match result with
  | .error e => some e.index
  | .ok _ => none

#guard invalidIndex (Alter.validate (.SeqH [next, next, next]) 2) == some 2
#guard invalidIndex (Alter.validate (num (-1)) 2) == some (-1)
#guard (render (.FuseH next next) ["a", "b"]).toOption == some "ab"
#guard (render (.SeqH []) []).toOption == some ""
#guard (render (.SeqH [.TextH "", .TextH "x"]) []).toOption == some " x"
def bracketEmpty : Except String String :=
  render (.BrackH (mkPhrase .LParen) (.TextH "") (mkPhrase .RParen)) []

#guard bracketEmpty.toOption == some "`( `)"
#guard (render (.FuseH (.TextH "") (.TextH "x")) []).toOption == some "x"
#guard !(render next []).isOk
#guard !(render (num (-1)) ["a"]).isOk
#guard !(render (.OtherH .null) []).isOk

def moved : region := { left := ⟨"other", 10, 2⟩, right := ⟨"other", 10, 4⟩ }

#guard Alter.policyEq next (.HoleH (mkPhrase .Next moved))
#guard Alter.policyEq (.AtomH (mkPhrase (.Keyword "K")))
  (.AtomH (mkPhrase (.Keyword "K") moved))
#guard !Alter.policyEq next (num 0)

end P4SpecTecTest.Alter
