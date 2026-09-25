import Lean.Data.Json.Printer
import P4SpecTec.IL.Ast

/-!
Values at runtime: constructors with dummy notes, structural comparison
and equality mirroring `p4spec/lib/runtime/value/value.ml` (without the
unique-id and hash shortcuts, which are performance devices: design
section 5.3), the `ToValue` class every generated type instantiates, and
the default value printer of `p4spec/lib/interface/p4/unparse.ml` that the
`print_` builtin uses when a spec declares no `print` hints.
-/

namespace P4SpecTec.Prelude

open P4SpecTec.Util.Source
open P4SpecTec.Xl
open P4SpecTec.Domain
open P4SpecTec.IL

namespace Value

/-- A dummy note: generated code does not allocate ids or hashes. -/
def note (t : typ') : vnote := .mk 0 t 0

/-- A value with a dummy note and no region. -/
def mk (t : typ') (v : value') : value := { it := v, note := note t, «at» := no_region }

/-- Mirrors `Value.Make.bool`. -/
def bool (b : Bool) : value := mk .BoolT (.BoolV b)

/-- Mirrors `Value.Make.nat`. -/
def nat (n : Nat) : value := mk (.NumT .NatT) (.NumV (.Nat n))

/-- Mirrors `Value.Make.int`. -/
def int (i : Int) : value := mk (.NumT .IntT) (.NumV (.Int i))

/-- Mirrors `Value.Make.text`. -/
def text (s : String) : value := mk .TextT (.TextV s)

/-- The type `id<targs>` as a note. -/
def varT (tid : String) (targs : List typ' := []) : typ' :=
  .VarT (mkPhrase tid) (targs.map mkPhrase)

/-- Mirrors `Value.Make.str`. -/
def str (t : typ') (fields : List (String × value)) : value :=
  mk t (.StructV (fields.map fun (a, v) => (mkPhrase (.Keyword a), v)))

/-- Mirrors `Value.Make.case`. -/
def case (t : typ') (c : Mixfix.t value) : value := mk t (.CaseV c)

/-- Mirrors `Value.Make.tuple`. -/
def tuple (t : typ') (vs : List value) : value := mk t (.TupleV vs)

/-- Mirrors `Value.Make.opt`. -/
def opt (t : typ') (v : Option value) : value := mk t (.OptV v)

/-- Mirrors `Value.Make.list`. -/
def list (t : typ') (vs : List value) : value := mk t (.ListV vs)

/-- An atom phrase for a mixfix. -/
def atom (a : Atom.t) : Mixfix.atom := mkPhrase a

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

/-- Mirrors `Value.compare`, structurally. -/
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
def compareFields : List (IL.atom × value) → List (IL.atom × value) → Ordering
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

/-- Mirrors `Value.eq`. -/
def eq (l r : value) : Bool := compare l r == .eq

instance : BEq value := ⟨eq⟩

instance : Ord value := ⟨compare⟩

/-- Mirrors `Mixfix.eq_mixop` on a case's mixfix against a mixop. -/
def hasMixop (c : Mixfix.t value) (m : Mixfix.mixop) : Bool := Mixfix.eq_mixop c m

/-- The arguments of a case when its mixop is `m`. -/
def caseArgs (c : Mixfix.t value) (m : Mixfix.mixop) : Option (List value) :=
  if Mixfix.eq_mixop c m then some (Mixfix.args c) else none

/-! The default printer of `Interface.P4.Unparse`, used by `print_` when the
spec declares no `print` hint. -/

/-- Mirrors `pp_num`. -/
def ppNum : Num.t → String
  | .Nat n => toString n
  | .Int i => (if i ≥ 0 then "" else "-") ++ toString i.natAbs

/-- Mirrors `pp_atom`: tags print as nothing, other atoms lower-cased. -/
def ppAtom (a : Atom.t) : String :=
  match a with
  | .Tag _ => ""
  | a => (Mixfix.to_string.render a).toLower

/-- Join the non-empty pieces with spaces. -/
def join (pieces : List String) : String :=
  " ".intercalate (pieces.filter (· ≠ ""))

mutual

/-- Mirrors `pp_value` without hints. -/
def print : value → String
  | ⟨v, _, _⟩ => print' v

/-- `print` on the payload. -/
def print' : value' → String
  | .BoolV b => toString b
  | .NumV n => ppNum n
  | .TextV s => s
  | .StructV _ => "<struct>"
  | .CaseV c => printMixfix c
  | .TupleV vs => "(" ++ ", ".intercalate (printList vs) ++ ")"
  | .OptV (some v) => print v
  | .OptV none => ""
  | .ListV vs => " ".intercalate (printList vs)
  | .FuncV i => "$" ++ i.it
  | .ExternV j => j.compress

/-- `pp_value` over a list. -/
def printList : List value → List String
  | [] => []
  | v :: vs => print v :: printList vs

/-- Mirrors `pp_default_case_v`: `Mixfix.render` with `pp_atom`. -/
def printMixfix : Mixfix.t value → String
  | .Arg v => print v
  | .Atom a => ppAtom a.it
  | .Brack l m r => join [ppAtom l.it, printMixfix m, ppAtom r.it]
  | .Infix l a r => join [printMixfix l, ppAtom a.it, printMixfix r]
  | .Seq ms => join (printMixfixes ms)

/-- `pp_default_case_v` over a sequence. -/
def printMixfixes : List (Mixfix.t value) → List String
  | [] => []
  | m :: ms => printMixfix m :: printMixfixes ms

end

end Value

/-- Conversion of a generated Lean value to the IL value it renders. Every
generated type gets an instance; equality on generated types is equality
of the values, as in upstream. -/
class ToValue (α : Type) where
  /-- The IL value. -/
  toValue : α → value

export ToValue (toValue)

instance : ToValue Bool := ⟨Value.bool⟩
instance : ToValue Nat := ⟨Value.nat⟩
instance : ToValue Int := ⟨Value.int⟩
instance : ToValue String := ⟨Value.text⟩
instance : ToValue value := ⟨id⟩

instance {α : Type} [ToValue α] : ToValue (List α) :=
  ⟨fun xs => Value.list .TextT (xs.map toValue)⟩

instance {α : Type} [ToValue α] : ToValue (Option α) :=
  ⟨fun x => Value.opt .TextT (x.map toValue)⟩

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
def valueEq {α : Type} [ToValue α] (a b : α) : Bool := Value.eq (toValue a) (toValue b)

/-- Comparison of generated values through their IL values. -/
def valueCompare {α : Type} [ToValue α] (a b : α) : Ordering :=
  Value.compare (toValue a) (toValue b)

end P4SpecTec.Prelude
