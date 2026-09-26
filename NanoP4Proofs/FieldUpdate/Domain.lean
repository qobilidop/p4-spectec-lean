import P4SpecTec.Refine.Value

/-!
# Field-update source domain

The four scalar forms below are selected directly from the pinned Nano source
`3.0-value.watsup`: unsigned/signed integer literals, booleans, and match kinds.
They do not depend on the generated Nano types or encoders. Widths are natural
numbers and integer payloads use AL's `Num.Int` representation; this is a shape
profile, not a bit-range or program-typing theorem. Names are arbitrary bytes.

Finite field lists may be empty and may contain duplicate names. Notes and
regions are not observations; field order, names, scalar tags and payloads are.
Nested records, packet/table objects, printing and source parsing are outside
this example. The correspondence profile disables dynamic guards.
-/

namespace NanoP4Proofs.FieldUpdate

open P4SpecTec P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.Prelude

/-- The independent scalar grammar of the selected source profile. -/
inductive Scalar where
  /-- Unsigned integer-literal syntax; not a proof of a width bound. -/
  | unsigned (width : Nat) (payload : Int)
  /-- Signed integer-literal syntax; not a proof of a width bound. -/
  | signed (width : Nat) (payload : Int)
  /-- Boolean values. -/
  | boolean (payload : Bool)
  /-- Match-kind names, with exact byte contents. -/
  | matchKind (name : ByteText)
  deriving DecidableEq

/-- Independent AL encoding, transcribed from the four source mixops. -/
def Scalar.source : Scalar → value
  | .unsigned w i => Runtime.Value.Make.case .TextT
      (.Seq [.Arg (Runtime.Value.Make.nat w), .Atom (Value.atom (.Keyword "W")),
        .Arg (Runtime.Value.Make.int i)])
  | .signed w i => Runtime.Value.Make.case .TextT
      (.Seq [.Arg (Runtime.Value.Make.nat w), .Atom (Value.atom (.Keyword "S")),
        .Arg (Runtime.Value.Make.int i)])
  | .boolean b => Runtime.Value.Make.case .TextT
      (.Seq [.Atom (Value.atom (.Tag "B")), .Arg (Runtime.Value.Make.bool b)])
  | .matchKind n => Runtime.Value.Make.case .TextT
      (.Seq [.Atom (Value.atom (.Keyword "MATCH_KIND")),
        .Atom (Value.atom (.Operator ".")), .Arg (Runtime.Value.Make.text n)])

/-- A field in the independent scalar source profile. -/
structure Field where
  /-- Stored scalar payload. -/
  payload : Scalar
  /-- Exact field name. -/
  name : ByteText
  deriving DecidableEq

/-- Independent AL field encoding: payload, name, then semicolon. -/
def Field.source (f : Field) : value := Runtime.Value.Make.case .TextT
  (.Seq [.Arg f.payload.source, .Arg (Runtime.Value.Make.text f.name),
    .Atom (Value.atom (.Operator ";"))])

/-- The source field-list encoding, preserving duplicates and order. -/
def sourceFields (fs : List Field) : value :=
  Runtime.Value.Make.list .TextT (fs.map Field.source)

/-- A supported scalar source value, allowing irrelevant notes and regions. -/
def SourceScalar (v : value) : Prop :=
  ∃ s : Scalar, Refine.canon v = Refine.canon s.source

/-- A supported source list, independent of generated constructors or encoders. -/
def SourceFields (v : value) : Prop :=
  ∃ fs : List Field, Refine.canon v = Refine.canon (sourceFields fs)

end NanoP4Proofs.FieldUpdate
