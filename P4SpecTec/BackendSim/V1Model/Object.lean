import P4SpecTec.BackendSim.V1Model.Arch

/-!
Port of `p4spec/lib/backend-sim/v1model/object.ml`: the v1model extern objects (counter,
register, direct counter, direct meter) with their constructors and methods, over the
spec trampolines. Counts are `Int`, as upstream's `Bigint`, and serialized as decimal
strings as `Util.Json.bigint_to_yojson` does; a register keeps IL values. Every upstream
exception (an unknown enum member, a malformed argument, a missing constructor argument)
is the hard error `Fail.err`.
-/

namespace P4SpecTec.BackendSim.V1Model.Object

open P4SpecTec.Lang.Il P4SpecTec.Runtime P4SpecTec.Prelude P4SpecTec.BackendSim.SpecImpl
open P4SpecTec.BackendSim.Core.Object (Error)
open P4SpecTec.BackendSim.V1Model.Packet (fieldOf)

variable {m : Type → Type} [Monad m] [MonadExceptOf Fail m]

/-- Mirrors `Util.Json.bigint_to_yojson`. -/
def bigint_to_yojson (i : Int) : Lean.Json := .str (toString i)

/-- Mirrors `Util.Json.bigint_of_yojson`: a decimal string or an integer. -/
def bigint_of_yojson : Lean.Json → Except Error Int
  | .str s => match s.toInt? with | some i => pure i | none => throw .decode
  | .num n => (Lean.Json.num n).getInt?.mapError fun _ => .decode
  | _ => throw .decode

/-- The constructor arguments of an object, paired with their parameter names. -/
def arguments (value_ids value_args : value) : m (List (ByteText × value)) :=
  Func.required (Unpack.assoc_args value_ids value_args)

/-- The enum member of a constructor argument, as (type, member). -/
def enumArgument (args : List (ByteText × value)) (name : String) : m (ByteText × ByteText) := do
  Func.required (Unpack.unpack_p4_enum (← Func.required (Unpack.assoc args name)))

/-- The `index` argument of a method as a host integer. -/
def indexArgument (spec : Make.Spec m) (value_ctx : value) : m Int := do
  let value_index ← Func.find_var_e_local spec.func value_ctx "index"
  let (_, index) ← Func.required (Unpack.unpack_p4_fixedBit value_index)
  pure index

/-- Mirrors a method's four results: the object, the context, the architecture and the
void call result. -/
abbrev Outcome (α : Type) := α × value × value × value

/-! Mirrors `Counter`. -/
namespace Counter

/-- Mirrors `t`. -/
inductive t where
  /-- Packet counts. -/
  | Packets (counts : List Int)
  /-- Byte counts. -/
  | Bytes (counts : List Int)
  /-- Packet and byte counts. -/
  | PacketsAndBytes (counts : List (Int × Int))
  deriving BEq, Repr

/-- Mirrors `to_yojson`. -/
def to_yojson : t → Lean.Json
  | .Packets counts => .arr #[.str "Packets", .arr (counts.map bigint_to_yojson).toArray]
  | .Bytes counts => .arr #[.str "Bytes", .arr (counts.map bigint_to_yojson).toArray]
  | .PacketsAndBytes counts => .arr #[.str "PacketsAndBytes", .arr (counts.map fun (p, b) =>
      .arr #[bigint_to_yojson p, bigint_to_yojson b]).toArray]

/-- Decode a list of big integers. -/
private def bigints (json : Lean.Json) : Except Error (List Int) := do
  (← json.getArr?.mapError fun _ => .decode).toList.mapM bigint_of_yojson

/-- Mirrors `of_yojson`. -/
def of_yojson : Lean.Json → Except Error t
  | .arr #[.str "Packets", counts] => .Packets <$> bigints counts
  | .arr #[.str "Bytes", counts] => .Bytes <$> bigints counts
  | .arr #[.str "PacketsAndBytes", counts] => do
    .PacketsAndBytes <$> (← counts.getArr?.mapError fun _ => .decode).toList.mapM fun pair =>
      match pair with
      | .arr #[p, b] => do pure (← bigint_of_yojson p, ← bigint_of_yojson b)
      | _ => throw .decode
  | _ => throw .decode

/-- Mirrors `init`: `counter(bit<32> size, CounterType type)`. -/
def init (_value_type_args value_ids value_args : value) : m t := do
  let args ← arguments value_ids value_args
  let value_size ← Func.required (Unpack.assoc args "size")
  let (_, size) ← Func.required (Unpack.unpack_p4_fixedBit value_size)
  unless Core.Object.hostInt size && size ≥ 0 do throw .err
  let (id_enum, id_type) ← enumArgument args "type"
  unless id_enum == ByteText.ofString "CounterType" do throw .err
  if id_type == ByteText.ofString "packets" then pure (.Packets (List.replicate size.toNat 0))
  else if id_type == ByteText.ofString "bytes" then pure (.Bytes (List.replicate size.toNat 0))
  else if id_type == ByteText.ofString "packets_and_bytes" then
    pure (.PacketsAndBytes (List.replicate size.toNat (0, 0)))
  else throw .err

/-- Update the count at an index; another index is unchanged. -/
private def at_ {α : Type} (target : Int) (f : α → α) (counts : List α) : List α :=
  counts.zipIdx.map fun (count, index) => if (index : Int) == target then f count else count

/-- Mirrors `count`: `void count(in bit<32> index)`, with the packet's length in bits. -/
def count (spec : Make.Spec m) (value_ctx value_arch : value) (packet_in : Core.Object.PacketIn.t)
    (counter : t) : m (Outcome t) := do
  let index_target ← indexArgument spec value_ctx
  let len := packet_in.len
  let counter := match counter with
    | .Packets counts => .Packets (at_ index_target (· + 1) counts)
    | .Bytes counts => .Bytes (at_ index_target (· + len) counts)
    | .PacketsAndBytes counts =>
      .PacketsAndBytes (at_ index_target (fun (p, b) => (p + 1, b + len)) counts)
  pure (counter, value_ctx, value_arch, Pack.returnVoid)

end Counter

/-! Mirrors `Register`. -/
namespace Register

/-- Mirrors `t`: the element type and the elements, as IL values. -/
structure t where
  /-- The element type. -/
  typ : value
  /-- The elements. -/
  values : List value

/-- Mirrors `to_yojson`. -/
def to_yojson (reg : t) : Lean.Json := Lean.Json.mkObj
  [("typ", Lang.Il.Encode.value reg.typ),
   ("values", .arr (reg.values.map Lang.Il.Encode.value).toArray)]

/-- Mirrors `of_yojson`. -/
def of_yojson (json : Lean.Json) : Except Error t := do
  let decode := fun j => (Lang.Il.Json.value j).mapError fun _ => Error.decode
  pure { typ := ← decode (← fieldOf json "typ"),
         values := ← (← (← fieldOf json "values").getArr?.mapError fun _ => .decode).toList.mapM
           decode }

/-- Mirrors `init`: `register(bit<32> size)` with one type argument. -/
def init (spec : Make.Spec m) (value_type_args value_ids value_args : value) : m t := do
  let [value_type] ← Func.required (Value.Get.list value_type_args) | throw .err
  let args ← arguments value_ids value_args
  let value_size ← Func.required (Unpack.assoc args "size")
  let value_default ← Func.default spec.func value_type
  let (_, size) ← Func.required (Unpack.unpack_p4_fixedBit value_size)
  unless Core.Object.hostInt size && size ≥ 0 do throw .err
  pure { typ := value_type, values := List.replicate size.toNat value_default }

/-- Mirrors `read`: `void read(out T result, in bit<32> index)`; an index past the end
reads the type's default. -/
def read (spec : Make.Spec m) (value_ctx value_arch : value) (reg : t) : m (Outcome t) := do
  let index_target ← indexArgument spec value_ctx
  let value ← if 0 ≤ index_target && index_target < reg.values.length then
      Func.required reg.values[index_target.toNat]?
    else Func.default spec.func reg.typ
  let value_ctx ← Rel.lvalue_write_var_local spec.rel value_ctx value_arch
    (ByteText.ofString "result") value
  pure (reg, value_ctx, value_arch, Pack.returnVoid)

/-- Mirrors `write`: `void write(in bit<32> index, in T value)`. -/
def write (spec : Make.Spec m) (value_ctx value_arch : value) (reg : t) : m (Outcome t) := do
  let index_target ← indexArgument spec value_ctx
  let value_target ← Func.find_var_e_local spec.func value_ctx "value"
  let values := reg.values.zipIdx.map fun (v, index) =>
    if (index : Int) == index_target then value_target else v
  pure ({ reg with values }, value_ctx, value_arch, Pack.returnVoid)

end Register

/-! Mirrors `DirectCounter`. -/
namespace DirectCounter

/-- Mirrors `t`. -/
inductive t where
  /-- A packet count. -/
  | Packets (count : Int)
  /-- A byte count. -/
  | Bytes (count : Int)
  /-- Both counts. -/
  | PacketsAndBytes (packets bytes : Int)
  deriving BEq, Repr

/-- Mirrors `to_yojson`. -/
def to_yojson : t → Lean.Json
  | .Packets n => .arr #[.str "Packets", bigint_to_yojson n]
  | .Bytes n => .arr #[.str "Bytes", bigint_to_yojson n]
  | .PacketsAndBytes p b =>
    .arr #[.str "PacketsAndBytes", .arr #[bigint_to_yojson p, bigint_to_yojson b]]

/-- Mirrors `of_yojson`. -/
def of_yojson : Lean.Json → Except Error t
  | .arr #[.str "Packets", n] => .Packets <$> bigint_of_yojson n
  | .arr #[.str "Bytes", n] => .Bytes <$> bigint_of_yojson n
  | .arr #[.str "PacketsAndBytes", .arr #[p, b]] => do
    pure (.PacketsAndBytes (← bigint_of_yojson p) (← bigint_of_yojson b))
  | _ => throw .decode

/-- Mirrors `init`: `direct_counter(CounterType type)`. -/
def init (_value_type_args value_ids value_args : value) : m t := do
  let args ← arguments value_ids value_args
  let (id_enum, id_type) ← enumArgument args "type"
  unless id_enum == ByteText.ofString "CounterType" do throw .err
  if id_type == ByteText.ofString "packets" then pure (.Packets 0)
  else if id_type == ByteText.ofString "bytes" then pure (.Bytes 0)
  else if id_type == ByteText.ofString "packets_and_bytes" then pure (.PacketsAndBytes 0 0)
  else throw .err

/-- Mirrors `count`: `void count()`. -/
def count (value_ctx value_arch : value) (packet_in : Core.Object.PacketIn.t) (counter : t) :
    m (Outcome t) := do
  let len := packet_in.len
  let counter := match counter with
    | .Packets n => .Packets (n + 1)
    | .Bytes n => .Bytes (n + len)
    | .PacketsAndBytes p b => .PacketsAndBytes (p + 1) (b + len)
  pure (counter, value_ctx, value_arch, Pack.returnVoid)

end DirectCounter

/-! Mirrors `DirectMeter`. -/
namespace DirectMeter

/-- Mirrors `t`. -/
inductive t where
  /-- Metering by packets. -/
  | Packets (count : Int)
  /-- Metering by bytes. -/
  | Bytes (count : Int)
  deriving BEq, Repr

/-- Mirrors `to_yojson`. -/
def to_yojson : t → Lean.Json
  | .Packets n => .arr #[.str "Packets", bigint_to_yojson n]
  | .Bytes n => .arr #[.str "Bytes", bigint_to_yojson n]

/-- Mirrors `of_yojson`. -/
def of_yojson : Lean.Json → Except Error t
  | .arr #[.str "Packets", n] => .Packets <$> bigint_of_yojson n
  | .arr #[.str "Bytes", n] => .Bytes <$> bigint_of_yojson n
  | _ => throw .decode

/-- Mirrors `init`: `direct_meter(MeterType type)`. -/
def init (_value_type_args value_ids value_args : value) : m t := do
  let args ← arguments value_ids value_args
  let (id_enum, id_type) ← enumArgument args "type"
  unless id_enum == ByteText.ofString "MeterType" do throw .err
  if id_type == ByteText.ofString "packets" then pure (.Packets 0)
  else if id_type == ByteText.ofString "bytes" then pure (.Bytes 0)
  else throw .err

/-- Mirrors `read`: `void read(out T result)`, always GREEN (zero) at the width of `T`. -/
def read (spec : Make.Spec m) (value_ctx value_arch : value) (_packet_in : Core.Object.PacketIn.t)
    (meter : t) : m (Outcome t) := do
  let value_typ ← Func.find_type_e_local spec.func value_ctx (ByteText.ofString "T")
  let size ← Func.sizeof_maxSizeInBits' spec.func
    (← Func.subst_type_e_local spec.func value_ctx value_typ)
  unless size ≥ 0 do throw .err
  let value := Pack.pack_p4_fixedBit size.toNat 0
  let value_ctx ← Rel.lvalue_write_var_local spec.rel value_ctx value_arch
    (ByteText.ofString "result") value
  pure (meter, value_ctx, value_arch, Pack.returnVoid)

end DirectMeter

end P4SpecTec.BackendSim.V1Model.Object
