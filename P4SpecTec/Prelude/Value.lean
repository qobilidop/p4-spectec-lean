import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Interface.P4.Unparse

/-!
Values for generated code: the `ToValue` class every generated type
instantiates (its IL value), the `OfValue` decoder class, equality and
ordering through values as upstream's `Value.eq` and `Value.compare`, and
small helpers on cases. The runtime's own value operations are in
`P4SpecTec.Runtime.Value`, which mirrors upstream.
-/

namespace P4SpecTec.Prelude

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Il

namespace Value

/-- The type `id<targs>` as a note. -/
def varT (tid : String) (targs : List typ' := []) : typ' :=
  .VarT (mkPhrase tid) (targs.map mkPhrase)

/-- An atom phrase for a mixfix. -/
def atom (a : Atom.t) : Mixfix.atom := mkPhrase a

/-- Mirrors `Mixfix.eq_mixop` on a case's mixfix against a mixop. -/
def hasMixop (c : Mixfix.t value) (m : Mixfix.mixop) : Bool := Mixfix.eq_mixop c m

/-- The arguments of a case when its mixop is `m`. -/
def caseArgs (c : Mixfix.t value) (m : Mixfix.mixop) : Option (List value) :=
  if Mixfix.eq_mixop c m then some (Mixfix.args c) else none

end Value

/-- Conversion of a generated Lean value to the IL value it renders. Every
generated type gets an instance; equality on generated types is equality
of the values, as in upstream. -/
class ToValue (α : Type) where
  /-- The IL value. -/
  toValue : α → value

export ToValue (toValue)

instance : ToValue Bool := ⟨Runtime.Value.Make.bool⟩
instance : ToValue Nat := ⟨Runtime.Value.Make.nat⟩
instance : ToValue Int := ⟨Runtime.Value.Make.int⟩
instance : ToValue String := ⟨Runtime.Value.Make.text⟩
instance : ToValue value := ⟨id⟩

instance {α : Type} [ToValue α] : ToValue (List α) :=
  ⟨fun xs => Runtime.Value.Make.list .TextT (xs.map toValue)⟩

instance {α : Type} [ToValue α] : ToValue (Option α) :=
  ⟨fun x => Runtime.Value.Make.opt .TextT (x.map toValue)⟩

/-- Decoding of an IL value into a generated Lean type, with fuel: `none`
when the value has another shape or the fuel runs out. Every generated
type gets an instance. -/
class OfValue (α : Type) where
  /-- Decode with fuel. -/
  ofValue : Nat → value → Option α

instance : OfValue Bool := ⟨fun _ v => match v.it with | .BoolV b => some b | _ => none⟩
instance : OfValue Nat := ⟨fun _ v => match v.it with | .NumV (.Nat n) => some n | _ => none⟩
instance : OfValue Int :=
  ⟨fun _ v => match v.it with | .NumV (.Int i) => some i | .NumV (.Nat n) => some n | _ => none⟩
instance : OfValue String := ⟨fun _ v => match v.it with | .TextV s => some s | _ => none⟩
instance : OfValue value := ⟨fun _ v => some v⟩

instance {α : Type} [OfValue α] : OfValue (List α) :=
  ⟨fun fuel v => match v.it with | .ListV vs => vs.mapM (OfValue.ofValue fuel) | _ => none⟩

instance {α : Type} [OfValue α] : OfValue (Option α) :=
  ⟨fun fuel v => match v.it with
    | .OptV none => some none
    | .OptV (some x) => (OfValue.ofValue fuel x).map some
    | _ => none⟩

/-- Equality of generated values through their IL values (mirrors `Value.eq`
on the interpreter side). -/
def valueEq {α : Type} [ToValue α] (a b : α) : Bool := Runtime.Value.eq (toValue a) (toValue b)

/-- Comparison of generated values through their IL values. -/
def valueCompare {α : Type} [ToValue α] (a b : α) : Ordering :=
  Runtime.Value.compare (toValue a) (toValue b)

end P4SpecTec.Prelude
