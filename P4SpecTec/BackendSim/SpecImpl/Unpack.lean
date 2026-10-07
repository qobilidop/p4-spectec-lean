import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Prelude.Value

/-!
Port of `p4spec/lib/backend-sim/spec_impl/unpack.ml`: the unpackers of P4 values into
host data. An optional result replaces the raising runtime getters; callers map `none` to
a hard error, as upstream's uncaught exception is. `unpack_p4_precision_numberValue` keeps
upstream's order of attempts. Widths and integers are `Int`, as upstream's `Bigint`.
-/

namespace P4SpecTec.BackendSim.SpecImpl.Unpack

open P4SpecTec.Lang.Il P4SpecTec.Lang.Xl P4SpecTec.Runtime P4SpecTec.Domain

/-- Mirrors `assoc_args`: pair parameter names with arguments; `List.combine` raises on a
length mismatch, which is `none` here. -/
def assoc_args (value_ids value_args : value) : Option (List (ByteText × value)) := do
  let ids ← (← Value.Get.list value_ids).mapM Value.Get.text
  let args ← Value.Get.list value_args
  unless ids.length == args.length do none
  pure (ids.zip args)

/-- Look up a named argument, as `List.assoc` does. -/
def assoc (args : List (ByteText × value)) (name : String) : Option value :=
  (args.find? fun (param, _) => param == ByteText.ofString name).map (·.2)

/-- Require exactly the pinned `_B bool` mixop followed by a Boolean payload. -/
def unpack_p4_bool (v : value) : Option Bool := do
  let .CaseV (.Seq [.Atom a, .Arg b]) := v.it | none
  unless a.it == .Tag "B" do none
  Value.Get.bool b

/-- Mirrors `unpack_p4_string`: `'"' text '"'`. -/
def unpack_p4_string (v : value) : Option ByteText := do
  let .CaseV (.Seq [.Atom l, .Arg s, .Atom r]) := v.it | none
  unless l.it == .Operator "\"" && r.it == .Operator "\"" do none
  Value.Get.text s

/-- Mirrors `unpack_p4_fixedBit`: `nat W int` as (width, int). -/
def unpack_p4_fixedBit (v : value) : Option (Int × Int) := do
  let .CaseV (.Seq [.Arg w, .Atom a, .Arg i]) := v.it | none
  unless a.it == .Keyword "W" do none
  pure (Num.to_int (← Value.Get.num w), Num.to_int (← Value.Get.num i))

/-- Mirrors `unpack_p4_fixedInt`: `nat S int` as (width, int). -/
def unpack_p4_fixedInt (v : value) : Option (Int × Int) := do
  let .CaseV (.Seq [.Arg w, .Atom a, .Arg i]) := v.it | none
  unless a.it == .Keyword "S" do none
  pure (Num.to_int (← Value.Get.num w), Num.to_int (← Value.Get.num i))

/-- Mirrors `unpack_p4_variableBit`: `nat '.' nat V int` as (max width, width, int). -/
def unpack_p4_variableBit (v : value) : Option (Int × Int × Int) := do
  let .CaseV (.Seq [.Arg wmax, .Atom dot, .Arg w, .Atom a, .Arg i]) := v.it | none
  unless dot.it == .Operator "." && a.it == .Keyword "V" do none
  pure (Num.to_int (← Value.Get.num wmax), Num.to_int (← Value.Get.num w),
    Num.to_int (← Value.Get.num i))

/-- Mirrors `unpack_p4_precision_numberValue`: a fixed bit string, else a fixed integer,
else a variable bit string's width and value. -/
def unpack_p4_precision_numberValue (v : value) : Option (Int × Int) :=
  unpack_p4_fixedBit v <|> unpack_p4_fixedInt v <|>
    (unpack_p4_variableBit v).map fun (_, w, i) => (w, i)

/-- The payload of a bracketed list case: `KEYWORD `( value* `)`-shaped values. -/
private def bracketed (keyword : String) (l r : Atom.t) (v : value) : Option (List value) := do
  let .CaseV (.Seq [.Atom k, .Brack lb (.Arg vs) rb]) := v.it | none
  unless k.it == .Keyword keyword && lb.it == l && rb.it == r do none
  Value.Get.list vs

/-- Mirrors `unpack_p4_tuple`: `TUPLE `( value* `)`. -/
def unpack_p4_tuple (v : value) : Option (List value) := bracketed "TUPLE" .LParen .RParen v

/-- Mirrors `unpack_p4_sequence`: `SEQ `( value* `)`. -/
def unpack_p4_sequence (v : value) : Option (List value) := bracketed "SEQ" .LParen .RParen v

/-- Mirrors `unpack_p4_enum`: `tid '.' id` as (type, member). -/
def unpack_p4_enum (v : value) : Option (ByteText × ByteText) := do
  let .CaseV (.Seq [.Arg tid, .Atom dot, .Arg member]) := v.it | none
  unless dot.it == .Operator "." do none
  pure (← Value.Get.text tid, ← Value.Get.text member)

end P4SpecTec.BackendSim.SpecImpl.Unpack
