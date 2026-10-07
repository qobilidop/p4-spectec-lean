import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Prelude.Value

/-!
Port of `p4spec/lib/backend-sim/spec_impl/pack.ml`: the three packers upstream defines
(an arbitrary-precision integer, a fixed-width bit string and an enum member), each an IL
value of the P4 `value` type with the mixop upstream's `Value.Make` parses from its string.
The atom spellings are those of the generated encoder of `value`.
-/

namespace P4SpecTec.BackendSim.SpecImpl.Pack

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Domain P4SpecTec.Prelude.Value

/-- A keyword atom in a mixfix. -/
def kw (s : String) : Mixfix.t value := .Atom (atom (.Keyword s))

/-- A tag atom (`_NAME`) in a mixfix. -/
def tag (s : String) : Mixfix.t value := .Atom (atom (.Tag s))

/-- An operator atom in a mixfix. -/
def op (s : String) : Mixfix.t value := .Atom (atom (.Operator s))

/-- Mirrors `pack_p4_arbitraryInt`: `D int`. -/
def pack_p4_arbitraryInt (i : Int) : value :=
  Value.Make.case (varT "value") (.Seq [kw "D", .Arg (Value.Make.int i)])

/-- Mirrors `pack_p4_fixedBit`: `nat W int`. -/
def pack_p4_fixedBit (width : Nat) (i : Int) : value :=
  Value.Make.case (varT "value")
    (.Seq [.Arg (Value.Make.nat width), kw "W", .Arg (Value.Make.int i)])

/-- Mirrors `pack_p4_enum`: `tid '.' id`. -/
def pack_p4_enum (type_id name : ByteText) : value :=
  Value.Make.case (varT "value")
    (.Seq [.Arg (Value.Make.text type_id), op ".", .Arg (Value.Make.text name)])

/-- The void call result every extern returns: `RETURN value?` with no value. -/
def returnVoid : value :=
  let typ : typ' := .IterT (Util.Source.mkPhrase (varT "value")) .Opt
  Value.Make.case (varT "returnResult") (.Seq [kw "RETURN", .Arg (Value.Make.opt typ none)])

/-- A call result returning a value: `RETURN value?` with the value. -/
def returnValue (v : value) : value :=
  let typ : typ' := .IterT (Util.Source.mkPhrase (varT "value")) .Opt
  Value.Make.case (varT "returnResult") (.Seq [kw "RETURN", .Arg (Value.Make.opt typ (some v))])

/-- A parser rejection with a named error: `REJECT errorValue` of `ERROR '.' nameIR`. -/
def rejectError (name : String) : value :=
  let err := Value.Make.case (varT "errorValue")
    (.Seq [kw "ERROR", op ".", .Arg (Value.Make.text (ByteText.ofString name))])
  Value.Make.case (varT "rejectTransitionResult") (.Seq [kw "REJECT", .Arg err])

/-- The `GLOBAL` cursor. -/
def cursorGlobal : value := Value.Make.case (varT "cursor") (.Atom (atom (.Keyword "GLOBAL")))

/-- The `LOCAL` cursor. -/
def cursorLocal : value := Value.Make.case (varT "cursor") (.Atom (atom (.Keyword "LOCAL")))

/-- A bare prefixed name, `_BARE nameIR`, under the type `prefixedNameIR`. -/
def bareName (name : ByteText) : value :=
  Value.Make.case (varT "prefixedNameIR") (.Seq [tag "BARE", .Arg (Value.Make.text name)])

/-- A member access, `storageReference '.' nameIR`. -/
def dotReference (base : value) (member : ByteText) : value :=
  Value.Make.case (varT "storageReference")
    (.Seq [.Arg base, op ".", .Arg (Value.Make.text member)])

/-- An object identifier, a list of names. -/
def objectId (names : List ByteText) : value :=
  Value.Make.list (.IterT (Util.Source.mkPhrase (varT "id")) .List) (names.map Value.Make.text)

/-- An object identifier from ASCII names. -/
def objectIdOf (names : List String) : value := objectId (names.map ByteText.ofString)

/-- An extern state value under the type `objectState`. -/
def objectState (json : Lean.Json) : value := Value.Make.extern (varT "objectState") json

/-- An architecture state value under the type `archState`. -/
def archState (json : Lean.Json) : value := Value.Make.extern (varT "archState") json

end P4SpecTec.BackendSim.SpecImpl.Pack
