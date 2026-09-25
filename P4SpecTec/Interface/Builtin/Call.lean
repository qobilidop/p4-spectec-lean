import P4SpecTec.Prelude.Value
import P4SpecTec.Interface.Builtin.Texts
import P4SpecTec.Interface.Builtin.Lists
import P4SpecTec.Interface.Builtin.Sets
import P4SpecTec.Interface.Builtin.Maps
import P4SpecTec.Interface.Builtin.Nats
import P4SpecTec.Interface.Builtin.Ints
import P4SpecTec.Interface.Builtin.Numerics
import P4SpecTec.Interface.P4.Unparse

/-!
The builtin dispatcher on IL values, for the interpreter. Mirrors
`p4spec/lib/interface/builtin/call.ml`: the same table of names, each
entry decoding its arguments as the OCaml builtin does (`Value.Get`,
`bigint_of_value`, `set_of_value`, `map_of_value`, `bits_of_value`),
calling the port of the same file under `Interface/Builtin/`, and
encoding the result (`Value.Make`, `value_of_set`, ...). A failure the
OCaml reports as a `BuiltinError`, an `error` or an assertion is `none`.
The `add` callback that registers fresh values upstream and `fresh_typeId`
(stateful) are not mirrored; of the interface-specific extension entries,
`print_` (Nano-P4's and P4's printer, `Interface/P4/Unparse.lean`) is.
-/

namespace P4SpecTec.Builtin.Call

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il
open P4SpecTec.Prelude
open P4SpecTec.Runtime.Value

/-- `mixop_set`: `` `{ k `} ``. -/
def mixop_set : Mixfix.mixop := .Brack (Value.atom .LBrace) (.Arg ()) (Value.atom .RBrace)

/-- `mixop_pair`: `k ':' v`. -/
def mixop_pair : Mixfix.mixop := .Seq [.Arg (), .Atom (Value.atom (.Operator ":")), .Arg ()]

/-- Mirrors `Sets.set_of_value`: the element list of a `set<K>` value. -/
def set_of_value (v : value) : Option (List value) := do
  let c ← Get.case v
  let [elems] ← Value.caseArgs c mixop_set | none
  Get.list elems

/-- Mirrors `Sets.value_of_set`: the elements sorted and distinct. -/
def value_of_set (typ_key : typ) (elems : List value) : value :=
  let elems := Sets.normalize elems
  let value_elements := Make.list (.IterT typ_key .List) elems
  match Mixfix.fill mixop_set [value_elements] with
  | some c => Make.case (.VarT (mkPhrase "set") [typ_key]) c
  | none => value_elements

/-- Mirrors `Maps.map_of_value`: the pair list of a `map<K, V>` value. -/
def map_of_value (v : value) : Option (List value) := do
  let c ← Get.case v
  let [pairs] ← Value.caseArgs c mixop_set | none
  Get.list pairs

/-- A pair value as a key and a value. -/
def pair_of_value (v : value) : Option (value × value) := do
  let c ← Get.case v
  let [k, v] ← Value.caseArgs c mixop_pair | none
  pure (k, v)

/-- Mirrors `Maps.make_pair`. -/
def make_pair (typ_key typ_value : typ) (key val : value) : value :=
  match Mixfix.fill mixop_pair [key, val] with
  | some c => Make.case (.VarT (mkPhrase "pair") [typ_key, typ_value]) c
  | none => Make.tuple .TextT [key, val]

/-- Mirrors `Maps.value_of_map`. -/
def value_of_map (typ_key typ_value : typ) (pairs : List value) : value :=
  let typ_pair : typ := mkPhrase (.VarT (mkPhrase "pair") [typ_key, typ_value])
  let value_pairs := Make.list (.IterT typ_pair .List) pairs
  match Mixfix.fill mixop_set [value_pairs] with
  | some c => Make.case (.VarT (mkPhrase "map") [typ_key, typ_value]) c
  | none => value_pairs

/-- Mirrors `bigint_of_value`: the integer of a number. -/
def int_of_value (v : value) : Option Int := (Get.num v).map Num.to_int

/-- A natural from a number (`Num.to_int` then `Make.nat`, as `Nats` does). -/
def nat_of_value (v : value) : Option Nat := (int_of_value v).map Int.toNat

/-- Mirrors `Numerics.bits_of_value`. -/
def bits_of_value (v : value) : Option (List Bool) := do (← Get.list v).mapM Get.bool

/-- Mirrors `Numerics.value_of_bits`. -/
def value_of_bits (bits : List Bool) : value :=
  Make.list (.VarT (mkPhrase "bit") []) (bits.map Make.bool)

/-- A tuple value of two components. -/
def pair2 (v : value) : Option (value × value) := do
  let [a, b] ← Get.tuple v | none
  pure (a, b)

/-- Mirrors `invoke`: the builtin `id` on type arguments and values;
`none` for a failure or a missing implementation. -/
def invoke (id : String) (targs : List typ) (args : List value) : Option value := do
  match id, targs, args with
  -- the extension entry of the P4 interfaces
  | "print_", _, [v] => pure (Make.text (P4.Unparse.print v))
  -- Nats
  | "sum_nat", _, [v] => do pure (Make.nat (Nats.sum_nat (← (← Get.list v).mapM nat_of_value)))
  | "max_nat", _, [v] => do pure (Make.nat (← Nats.max_nat (← (← Get.list v).mapM nat_of_value)))
  | "min_nat", _, [v] => do pure (Make.nat (← Nats.min_nat (← (← Get.list v).mapM nat_of_value)))
  -- Ints
  | "sum_int", _, [v] => do pure (Make.int (Ints.sum_int (← (← Get.list v).mapM int_of_value)))
  | "max_int", _, [v] => do pure (Make.int (Ints.max_int (← (← Get.list v).mapM int_of_value)))
  | "min_int", _, [v] => do pure (Make.int (Ints.min_int (← (← Get.list v).mapM int_of_value)))
  -- Texts
  | "text_to_int", _, [v] => do pure (Make.int (← Texts.text_to_int (← Get.text v)))
  | "int_to_text", _, [v] => do pure (Make.text (Num.string_of_num (← Get.num v)))
  | "split_text", _, [s, sep] => do
    let parts ← Texts.split_text (← Get.text s) (← Get.text sep)
    pure (Make.list (.IterT (mkPhrase .BoolT) .List) (parts.map Make.text))
  | "strip_prefix", _, [s, p] => do pure (Make.text (← Texts.strip_prefix (← Get.text s) (← Get.text p)))
  | "strip_suffix", _, [s, p] => do pure (Make.text (← Texts.strip_suffix (← Get.text s) (← Get.text p)))
  | "strip_all_whitespace", _, [s] => do pure (Make.text (Texts.strip_all_whitespace (← Get.text s)))
  -- Lists
  | "rev_", [typ], [v] => do pure (Make.list (.IterT typ .List) (Lists.rev_ (← Get.list v)))
  | "concat_", [typ], [v] => do
    pure (Make.list (.IterT typ .List) (Lists.concat_ (← (← Get.list v).mapM Get.list)))
  | "distinct_", _, [v] => do pure (Make.bool (Lists.distinct_ (← Get.list v)))
  | "partition_", [typ], [v, n] => do
    let (l, r) := Lists.partition_ (← Get.list v) (← nat_of_value n)
    let t : typ' := .IterT typ .List
    pure (Make.tuple (.TupleT [mkPhrase t, mkPhrase t]) [Make.list t l, Make.list t r])
  | "assoc_", [_, typ_value], [k, v] => do
    let pairs ← (← Get.list v).mapM pair2
    pure (Make.opt (.IterT typ_value .Opt) (Lists.assoc_ k pairs))
  | "sort_", [typ_value], [v] => do
    let pairs ← (← Get.list v).mapM fun p => do
      let (k, x) ← pair2 p
      pure (← nat_of_value k, (k, x))
    let sorted := Lists.sort_ pairs
    let t : typ' := .TupleT [Typ_nat, typ_value]
    pure (Make.list (.IterT (mkPhrase t) .List) (sorted.map fun (_, (k, x)) => Make.tuple t [k, x]))
  | "transpose_", [typ], [v] => do
    let rows ← (← Get.list v).mapM Get.list
    let cols ← Lists.transpose_ rows
    let t : typ' := .IterT typ .List
    pure (Make.list (.IterT (mkPhrase t) .List) (cols.map (Make.list t)))
  -- Sets
  | "intersect_set", [typ_key], [a, b] => do
    pure (value_of_set typ_key (Sets.intersect_set (← set_of_value a) (← set_of_value b)))
  | "union_set", [typ_key], [a, b] => do
    pure (value_of_set typ_key (Sets.union_set (← set_of_value a) (← set_of_value b)))
  | "unions_set", [typ_key], [v] => do
    pure (value_of_set typ_key (Sets.unions_set (← (← Get.list v).mapM set_of_value)))
  | "diff_set", [typ_key], [a, b] => do
    pure (value_of_set typ_key (Sets.diff_set (← set_of_value a) (← set_of_value b)))
  | "sub_set", _, [a, b] => do pure (Make.bool (Sets.sub_set (← set_of_value a) (← set_of_value b)))
  | "eq_set", _, [a, b] => do pure (Make.bool (Sets.eq_set (← set_of_value a) (← set_of_value b)))
  -- Maps
  | "find_map", [_, typ_value], [m, k] => do
    let pairs ← (← map_of_value m).mapM pair_of_value
    pure (Make.opt (.IterT typ_value .Opt) (Maps.find_map pairs k))
  | "find_maps", [_, typ_value], [ms, k] => do
    let maps ← (← Get.list ms).mapM fun m => do (← map_of_value m).mapM pair_of_value
    pure (Make.opt (.IterT typ_value .Opt) (Maps.find_maps maps k))
  | "add_map", [typ_key, typ_value], [m, k, v] => do
    let pairs ← (← map_of_value m).mapM pair_of_value
    let pairs := Maps.add_map pairs k v
    pure (value_of_map typ_key typ_value (pairs.map fun (k, v) => make_pair typ_key typ_value k v))
  | "adds_map", [typ_key, typ_value], [m, ks, vs] => do
    let pairs ← (← map_of_value m).mapM pair_of_value
    let pairs ← Maps.adds_map pairs (← Get.list ks) (← Get.list vs)
    pure (value_of_map typ_key typ_value (pairs.map fun (k, v) => make_pair typ_key typ_value k v))
  | "update_map", [typ_key, typ_value], [m, k, v] => do
    let pairs ← (← map_of_value m).mapM pair_of_value
    let pairs := Maps.update_map pairs k v
    pure (value_of_map typ_key typ_value (pairs.map fun (k, v) => make_pair typ_key typ_value k v))
  -- Numerics
  | "shl", _, [a, b] => do pure (Make.int (← Numerics.shl (← int_of_value a) (← int_of_value b)))
  | "shr", _, [a, b] => do pure (Make.int (← Numerics.shr (← int_of_value a) (← int_of_value b)))
  | "shr_arith", _, [a, b, c] => do
    pure (Make.int (← Numerics.shr_arith (← int_of_value a) (← int_of_value b) (← int_of_value c)))
  | "pow2", _, [a] => do pure (Make.int (Numerics.pow2 (← int_of_value a)))
  | "bitstr_to_int", _, [a, b] => do
    pure (Make.int (← Numerics.bitstr_to_int (← int_of_value a) (← int_of_value b)))
  | "int_to_bitstr", _, [a, b] => do
    pure (Make.int (← Numerics.int_to_bitstr (← int_of_value a) (← int_of_value b)))
  | "bits_to_int_unsigned", _, [a] => do
    pure (Make.int (Numerics.bits_to_int_unsigned (← bits_of_value a)))
  | "bits_to_int_signed", _, [a] => do
    pure (Make.int (← Numerics.bits_to_int_signed (← bits_of_value a)))
  | "int_to_bits_unsigned", _, [a, b] => do
    pure (value_of_bits (← Numerics.int_to_bits_unsigned (← int_of_value a) (← int_of_value b)))
  | "int_to_bits_signed", _, [a, b] => do
    pure (value_of_bits (← Numerics.int_to_bits_signed (← int_of_value a) (← int_of_value b)))
  | "bneg", _, [a] => do pure (Make.int (Numerics.bneg (← int_of_value a)))
  | "band", _, [a, b] => do pure (Make.int (Numerics.band (← int_of_value a) (← int_of_value b)))
  | "bxor", _, [a, b] => do pure (Make.int (Numerics.bxor (← int_of_value a) (← int_of_value b)))
  | "bor", _, [a, b] => do pure (Make.int (Numerics.bor (← int_of_value a) (← int_of_value b)))
  | "bitacc", _, [a, b, c] => do
    pure (Make.int (← Numerics.bitacc (← int_of_value a) (← int_of_value b) (← int_of_value c)))
  | "bitacc_replace", _, [a, b, c, d] => do
    pure (Make.int (Numerics.bitacc_replace (← int_of_value a) (← int_of_value b)
      (← int_of_value c) (← int_of_value d)))
  | _, _, _ => none
where
  /-- The `nat` type. -/
  Typ_nat : typ := mkPhrase (.NumT .NatT)

end P4SpecTec.Builtin.Call
