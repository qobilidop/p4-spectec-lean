import P4SpecTec.Runtime.Value.Value
import P4SpecTec.Prelude.Value

/-!
The value relation of rung 3 (design section 5.1): an IL value is related
to a value of a generated type when it equals that value's IL image up to
notes and regions. `canon` erases both (and reduces the two payloads the
interpreter's comparison does not look inside, function ids and extern
JSON, to what it compares); `Rel v x` is `canon v = canon (toValue x)`.
The lemma `eq_iff_canon` says the interpreter's `Value.eq` is exactly
this equality, so the value relation is an equivalence and respects every
operation the interpreter defines through `Value.eq`.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il
open P4SpecTec.Prelude
open P4SpecTec.Runtime.Value

/-- The dummy note of a canonical value. -/
def dummy : vnote := Make.note .TextT

/-- The dummy function id: `compare` orders function values by tag only. -/
def dummyId : Lang.Il.id := mkPhrase ""

mutual

/-- The canonical form of a value: notes and regions erased. -/
def canon (v : value) : value := ⟨canon' v.it, dummy, no_region⟩

/-- `canon` on payloads. -/
def canon' : value' → value'
  | .BoolV b => .BoolV b
  | .NumV n => .NumV n
  | .TextV s => .TextV s
  | .StructV fs => .StructV (canonFields fs)
  | .CaseV c => .CaseV (canonMixfix c)
  | .TupleV vs => .TupleV (canons vs)
  | .OptV none => .OptV none
  | .OptV (some v) => .OptV (some (canon v))
  | .ListV vs => .ListV (canons vs)
  | .FuncV _ => .FuncV dummyId
  | .ExternV j => .ExternV (.str j.compress)

/-- `canon` on struct fields: atoms lose their regions. -/
def canonFields : List (Lang.Il.atom × value) → List (Lang.Il.atom × value)
  | [] => []
  | (a, v) :: fs => (mkPhrase a.it, canon v) :: canonFields fs

/-- `canon` on value lists. -/
def canons : List value → List value
  | [] => []
  | v :: vs => canon v :: canons vs

/-- `canon` on a case's mixfix. -/
def canonMixfix : Mixfix.t value → Mixfix.t value
  | .Arg v => .Arg (canon v)
  | .Atom a => .Atom (mkPhrase a.it)
  | .Brack l m r => .Brack (mkPhrase l.it) (canonMixfix m) (mkPhrase r.it)
  | .Infix l a r => .Infix (canonMixfix l) (mkPhrase a.it) (canonMixfix r)
  | .Seq ms => .Seq (canonMixfixes ms)

/-- `canon` on mixfix sequences. -/
def canonMixfixes : List (Mixfix.t value) → List (Mixfix.t value)
  | [] => []
  | m :: ms => canonMixfix m :: canonMixfixes ms

end

/-- The value relation: `v` is the IL image of `x` up to notes. -/
def Rel {α : Type} [ToValue α] (v : value) (x : α) : Prop := canon v = canon (toValue x)

/-! ## `Value.eq` is canonical equality -/

-- The proofs below are exhaustive case splits closed by one shared simp
-- set; which lemmas a case uses varies, so the unused-argument linter is
-- off for them.
set_option linter.unusedSimpArgs false

/-- `Ordering.then` is `eq` when both parts are. -/
theorem then_eq_iff {a b : Ordering} : a.then b = .eq ↔ a = .eq ∧ b = .eq := by
  cases a <;> cases b <;> simp [Ordering.then]

/-- Comparison of numbers. -/
theorem compareNum_eq_iff {a b : Num.t} : compareNum a b = .eq ↔ a = b := by
  cases a <;> cases b <;> simp [compareNum, Nat.compare_eq_eq, Int.compare_eq_eq]

/-- Comparison of strings. -/
theorem compareString_eq_iff {a b : String} : Ord.compare a b = .eq ↔ a = b := by
  show String.compare a b = .eq ↔ a = b
  unfold String.compare
  exact compareOfLessAndEq_eq_eq String.le_refl String.not_le

/-- Comparison of booleans. -/
theorem compareBool_eq_iff {a b : Bool} : Ord.compare a b = .eq ↔ a = b := by
  cases a <;> cases b <;> decide

/-- Comparison of atoms. -/
theorem Atom.compare_eq_iff {a b : Atom.t} : Atom.compare a b = .eq ↔ a = b := by
  cases a <;> cases b <;> simp [Atom.compare, Atom.tag, compareString_eq_iff, Nat.compare_eq_eq]

/-- Atom phrases with equal atoms are equal up to regions. -/
theorem atom_phrase_eq {a b : Lang.Il.atom} :
    (mkPhrase a.it : Lang.Il.atom) = mkPhrase b.it ↔ a.it = b.it := by
  simp [mkPhrase, info.mk.injEq]

mutual

/-- `compare` is `eq` exactly on canonically equal values. -/
theorem compare_eq_iff : ∀ (a b : value), Runtime.Value.compare a b = .eq ↔ canon a = canon b
  | ⟨a, _, _⟩, ⟨b, _, _⟩ => by
    simp only [Runtime.Value.compare, canon, info.mk.injEq, and_true]
    exact compare'_eq_iff a b

/-- `compare'` on payloads. -/
theorem compare'_eq_iff : ∀ (a b : value'), Runtime.Value.compare' a b = .eq ↔ canon' a = canon' b
  | a, b => by
    rcases a with a | a | a | a | a | a | (_ | a) | a | a | a <;>
    rcases b with b | b | b | b | b | b | (_ | b) | b | b | b <;>
      first
      | (simp [Runtime.Value.compare', canon', Runtime.Value.tag, compareBool_eq_iff,
          compareNum_eq_iff, compareString_eq_iff, ByteText.compare_eq_iff_eq,
          ByteText.instOrd, Nat.compare_eq_eq]; done)
      | (simp [Runtime.Value.compare', canon', compares_eq_iff a b]; done)
      | (simp [Runtime.Value.compare', canon', compareFields_eq_iff a b]; done)
      | (simp [Runtime.Value.compare', canon', compareMixfix_eq_iff a b]; done)
      | (simp [Runtime.Value.compare', canon', compare_eq_iff a b]; done)

/-- `compareFields`. -/
theorem compareFields_eq_iff : ∀ (a b : List (Lang.Il.atom × value)),
    Runtime.Value.compareFields a b = .eq ↔ canonFields a = canonFields b
  | [], [] => by simp [Runtime.Value.compareFields, canonFields]
  | [], _ :: _ => by simp [Runtime.Value.compareFields, canonFields]
  | _ :: _, [] => by simp [Runtime.Value.compareFields, canonFields]
  | (aa, va) :: fa, (ab, vb) :: fb => by
    simp [Runtime.Value.compareFields, canonFields, then_eq_iff, Atom.compare_eq_iff,
      atom_phrase_eq, compare_eq_iff va vb, compareFields_eq_iff fa fb, and_assoc]

/-- `compares`. -/
theorem compares_eq_iff : ∀ (a b : List value),
    Runtime.Value.compares a b = .eq ↔ canons a = canons b
  | [], [] => by simp [Runtime.Value.compares, canons]
  | [], _ :: _ => by simp [Runtime.Value.compares, canons]
  | _ :: _, [] => by simp [Runtime.Value.compares, canons]
  | a :: as, b :: bs => by
    simp [Runtime.Value.compares, canons, then_eq_iff, compare_eq_iff a b, compares_eq_iff as bs]

/-- `compareMixfix`. -/
theorem compareMixfix_eq_iff : ∀ (a b : Mixfix.t value),
    Runtime.Value.compareMixfix a b = .eq ↔ canonMixfix a = canonMixfix b
  | a, b => by
    rcases a with a | a | ⟨la, ma, ra⟩ | ⟨la, aa, ra⟩ | a <;>
    rcases b with b | b | ⟨lb, mb, rb⟩ | ⟨lb, ab, rb⟩ | b <;>
      first
      | (simp [Runtime.Value.compareMixfix, canonMixfix, Mixfix.tag, Nat.compare_eq_eq,
          Atom.compare_eq_iff, atom_phrase_eq]; done)
      | (simp [Runtime.Value.compareMixfix, canonMixfix, compare_eq_iff a b]; done)
      | (simp [Runtime.Value.compareMixfix, canonMixfix, compareMixfixes_eq_iff a b]; done)
      | (simp [Runtime.Value.compareMixfix, canonMixfix, then_eq_iff, Atom.compare_eq_iff,
          atom_phrase_eq, compareMixfix_eq_iff ma mb]; done)
      | (simp [Runtime.Value.compareMixfix, canonMixfix, then_eq_iff, Atom.compare_eq_iff,
          atom_phrase_eq, compareMixfix_eq_iff la lb, compareMixfix_eq_iff ra rb]; done)

/-- `compareMixfixes`. -/
theorem compareMixfixes_eq_iff : ∀ (a b : List (Mixfix.t value)),
    Runtime.Value.compareMixfixes a b = .eq ↔ canonMixfixes a = canonMixfixes b
  | [], [] => by simp [Runtime.Value.compareMixfixes, canonMixfixes]
  | [], _ :: _ => by simp [Runtime.Value.compareMixfixes, canonMixfixes]
  | _ :: _, [] => by simp [Runtime.Value.compareMixfixes, canonMixfixes]
  | a :: as, b :: bs => by
    simp [Runtime.Value.compareMixfixes, canonMixfixes, then_eq_iff, compareMixfix_eq_iff a b,
      compareMixfixes_eq_iff as bs]

end

/-- The interpreter's equality is canonical equality. -/
theorem eq_iff_canon {a b : value} : Runtime.Value.eq a b = true ↔ canon a = canon b := by
  unfold Runtime.Value.eq
  rw [← compare_eq_iff]
  cases Runtime.Value.compare a b <;> simp

/-- `Rel` decides the interpreter's equality against the generated one. -/
theorem eq_of_rel {α β : Type} [ToValue α] [ToValue β] {v w : value} {x : α} {y : β}
    (hv : Rel v x) (hw : Rel w y) :
    Runtime.Value.eq v w = Runtime.Value.eq (toValue x) (toValue y) := by
  unfold Rel at hv hw
  rw [Bool.eq_iff_iff, eq_iff_canon, eq_iff_canon, hv, hw]

end P4SpecTec.Refine
