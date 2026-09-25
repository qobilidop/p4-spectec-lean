import Lean.Data.Json.Printer
import P4SpecTec.Lang.Il.Ast

/-!
Values at runtime: construction, accessors, comparison and equality.
Mirrors `p4spec/lib/runtime/value/value.ml` (`Value.Make`, `Value.Get`,
`Value.compare`, `Value.eq`), under upstream's module name
`Runtime.Value` as the namespace, without the unique-id and hash
shortcuts, which are performance devices (design section 5.3):
comparison is structural. The hashing, the mixop parsing from strings and
the `Get.mtch` tables of the OCaml are not mirrored; an accessor returns
`none` where the OCaml raises.
-/

namespace P4SpecTec.Runtime.Value

open P4SpecTec.Util.Source
open P4SpecTec.Lang.Xl
open P4SpecTec.Domain
open P4SpecTec.Lang.Il

/-! Mirrors `Value.Make`: the constructors. -/
namespace Make

/-- A dummy note: generated code does not allocate ids or hashes (`Make.mk`
allocates both upstream). -/
def note (t : typ') : vnote := .mk 0 t 0

/-- Mirrors `Make.mk`, with a dummy note and no region. -/
def mk (t : typ') (v : value') : value := { it := v, note := note t, «at» := no_region }

/-- Mirrors `Make.bool`. -/
def bool (b : Bool) : value := mk .BoolT (.BoolV b)

/-- Mirrors `Make.nat`. -/
def nat (n : Nat) : value := mk (.NumT .NatT) (.NumV (.Nat n))

/-- Mirrors `Make.int`. -/
def int (i : Int) : value := mk (.NumT .IntT) (.NumV (.Int i))

/-- Mirrors `Make.num`. -/
def num : Num.t → value
  | .Nat n => nat n
  | .Int i => int i

/-- Mirrors `Make.text`. -/
def text (s : ByteText) : value := mk .TextT (.TextV s)

/-- Mirrors `Make.str`. -/
def str (t : typ') (fields : List (String × value)) : value :=
  mk t (.StructV (fields.map fun (a, v) => (mkPhrase (.Keyword a), v)))

/-- Mirrors `Make.case`. -/
def case (t : typ') (c : Mixfix.t value) : value := mk t (.CaseV c)

/-- Mirrors `Make.tuple`. -/
def tuple (t : typ') (vs : List value) : value := mk t (.TupleV vs)

/-- Mirrors `Make.opt`. -/
def opt (t : typ') (v : Option value) : value := mk t (.OptV v)

/-- Mirrors `Make.list`. -/
def list (t : typ') (vs : List value) : value := mk t (.ListV vs)

/-- Mirrors `Make.func`: a function value noted with its type. -/
def func (id : Lang.Il.id) (tparams : List tparam) (typs_params : List typ) (typ : typ) : value :=
  mk (.FuncT tparams typs_params typ) (.FuncV id)

/-- Mirrors `Make.extern`. -/
def extern (t : typ') (json : Lean.Json) : value := mk t (.ExternV json)

end Make

/-! Mirrors `Value.Get`: the accessors, `none` where the OCaml raises. -/
namespace Get

/-- Mirrors `Get.bool`. -/
def bool (v : value) : Option Bool := match v.it with | .BoolV b => some b | _ => none

/-- Mirrors `Get.num`. -/
def num (v : value) : Option Num.t := match v.it with | .NumV n => some n | _ => none

/-- Mirrors `Get.text`. -/
def text (v : value) : Option ByteText := match v.it with | .TextV s => some s | _ => none

/-- Mirrors `Get.str`. -/
def str (v : value) : Option (List valuefield) :=
  match v.it with | .StructV fs => some fs | _ => none

/-- Mirrors `Get.case`. -/
def case (v : value) : Option valuecase := match v.it with | .CaseV c => some c | _ => none

/-- Mirrors `Get.tuple`. -/
def tuple (v : value) : Option (List value) := match v.it with | .TupleV vs => some vs | _ => none

/-- Mirrors `Get.opt`. -/
def opt (v : value) : Option (Option value) := match v.it with | .OptV o => some o | _ => none

/-- Mirrors `Get.list`. -/
def list (v : value) : Option (List value) := match v.it with | .ListV vs => some vs | _ => none

/-- Mirrors `Get.func`. -/
def func (v : value) : Option Lang.Il.id := match v.it with | .FuncV i => some i | _ => none

/-- Mirrors `Get.extern`. -/
def extern (v : value) : Option Lean.Json := match v.it with | .ExternV j => some j | _ => none

end Get

/-- The tag of a value constructor, in declaration order, for `compare`. -/
def tag : value' → Nat
  | .BoolV _ => 0 | .NumV _ => 1 | .TextV _ => 2 | .StructV _ => 3 | .CaseV _ => 4
  | .TupleV _ => 5 | .OptV none => 6 | .OptV _ => 7 | .ListV _ => 8 | .FuncV _ => 9
  | .ExternV _ => 10

/-- Mirrors `Num.compare`: naturals before integers. -/
def compareNum : Num.t → Num.t → Ordering
  | .Nat a, .Nat b => Ord.compare a b
  | .Int a, .Int b => Ord.compare a b
  | .Nat _, .Int _ => .lt
  | .Int _, .Nat _ => .gt

mutual

/-- Mirrors `compare`, structurally. -/
def compare : value → value → Ordering
  | ⟨a, _, _⟩, ⟨b, _, _⟩ => compare' a b

/-- `compare` on the payloads. -/
def compare' : value' → value' → Ordering
  | .BoolV a, .BoolV b => Ord.compare a b
  | .NumV a, .NumV b => compareNum a b
  | .TextV a, .TextV b => Ord.compare a b
  | .StructV fa, .StructV fb => compareFields fa fb
  | .CaseV ca, .CaseV cb => compareMixfix ca cb
  | .TupleV va, .TupleV vb => compares va vb
  | .OptV (some a), .OptV (some b) => compare a b
  | .OptV (some _), .OptV none => .gt
  | .OptV none, .OptV (some _) => .lt
  | .OptV none, .OptV none => .eq
  | .ListV va, .ListV vb => compares va vb
  | .ExternV a, .ExternV b => Ord.compare a.compress b.compress
  | a, b => Ord.compare (tag a) (tag b)

/-- Mirrors `compare_fields`. -/
def compareFields : List (Lang.Il.atom × value) → List (Lang.Il.atom × value) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | (aa, va) :: fa, (ab, vb) :: fb =>
    (Atom.compare aa.it ab.it).then ((compare va vb).then (compareFields fa fb))

/-- Mirrors `compares`. -/
def compares : List value → List value → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compare a b).then (compares as bs)

/-- Mirrors `Mixfix.compare ~compare_arg:compare`. -/
def compareMixfix : Mixfix.t value → Mixfix.t value → Ordering
  | .Arg a, .Arg b => compare a b
  | .Atom a, .Atom b => Atom.compare a.it b.it
  | .Brack la ma ra, .Brack lb mb rb =>
    (Atom.compare la.it lb.it).then ((compareMixfix ma mb).then (Atom.compare ra.it rb.it))
  | .Infix la aa ra, .Infix lb ab rb =>
    (compareMixfix la lb).then ((Atom.compare aa.it ab.it).then (compareMixfix ra rb))
  | .Seq as, .Seq bs => compareMixfixes as bs
  | a, b => Ord.compare (Mixfix.tag a) (Mixfix.tag b)

/-- `Mixfix.compare` over sequences. -/
def compareMixfixes : List (Mixfix.t value) → List (Mixfix.t value) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compareMixfix a b).then (compareMixfixes as bs)

end

/-- Mirrors `eq`. -/
def eq (l r : value) : Bool := compare l r == .eq

instance : BEq value := ⟨eq⟩

instance : Ord value := ⟨compare⟩

end P4SpecTec.Runtime.Value
