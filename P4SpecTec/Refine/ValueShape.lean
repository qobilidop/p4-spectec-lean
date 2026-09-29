import P4SpecTec.Refine.Value

/-! Expose runtime constructors through the canonical representation relation. -/

namespace P4SpecTec.Refine

open P4SpecTec.Util.Source
open P4SpecTec.Domain
open P4SpecTec.Lang.Xl
open P4SpecTec.Lang.Il
open P4SpecTec.Prelude
open P4SpecTec.Runtime
/-- The outputs of a relation are related to a tuple's values. -/
def Outs (vs : List value) (ws : List value) : Prop := canons vs = canons ws

/-- `canon` of a literal. -/
@[simp] theorem canon_mk (p : value') (n : vnote) (r : region) :
    canon ⟨p, n, r⟩ = ⟨canon' p, dummy, no_region⟩ := by rw [canon]

/-- The payload of a canonical value. -/
theorem canon_it (v : value) : (canon v).it = canon' v.it := by rw [canon]

/-- A canonical value equal to a literal: its payload. -/
theorem canon_eq_it {v : value} {q : value'} {n : vnote} {r : region} (h : canon v = ⟨q, n, r⟩) :
    canon' v.it = q := by
  rw [← canon_it, h]

/-- Equality of naturals. -/
@[simp] theorem eq_nat (a b : Nat) (n n' : vnote) (r r' : region) :
    Runtime.Value.eq ⟨.NumV (.Nat a), n, r⟩ ⟨.NumV (.Nat b), n', r'⟩ = decide (a = b) := by
  rw [Bool.eq_iff_iff, eq_iff_canon]
  simp [canon_mk, canon']

/-- Equality of integers. -/
@[simp] theorem eq_int (a b : Int) (n n' : vnote) (r r' : region) :
    Runtime.Value.eq ⟨.NumV (.Int a), n, r⟩ ⟨.NumV (.Int b), n', r'⟩ = decide (a = b) := by
  rw [Bool.eq_iff_iff, eq_iff_canon]
  simp [canon_mk, canon']

/-- Equality of booleans. -/
@[simp] theorem eq_bool (a b : Bool) (n n' : vnote) (r r' : region) :
    Runtime.Value.eq ⟨.BoolV a, n, r⟩ ⟨.BoolV b, n', r'⟩ = decide (a = b) := by
  rw [Bool.eq_iff_iff, eq_iff_canon]
  simp [canon_mk, canon']

/-- Equality of texts. -/
@[simp] theorem eq_text (a b : ByteText) (n n' : vnote) (r r' : region) :
    Runtime.Value.eq ⟨.TextV a, n, r⟩ ⟨.TextV b, n', r'⟩ = decide (a = b) := by
  rw [Bool.eq_iff_iff, eq_iff_canon]
  simp [canon_mk, canon']

/-- The interpreter's equality observes only payloads, so known payload shapes decide it
through the literal equalities above. -/
theorem eq_of_its {v w : value} {p q : value'} (hv : v.it = p) (hw : w.it = q) :
    Runtime.Value.eq v w = Runtime.Value.eq ⟨p, dummy, no_region⟩ ⟨q, dummy, no_region⟩ := by
  apply Bool.eq_iff_iff.mpr
  rw [eq_iff_canon, eq_iff_canon, canon_mk, canon_mk, canon, canon, hv, hw]

/-- The interpreter's equality is reflexive. -/
@[simp] theorem eq_refl (v : value) : Runtime.Value.eq v v = true := by
  rw [eq_iff_canon]

/-- An equality test on canonically equal values holds. -/
theorem eq_true_of_canon {v w : value} (h : canon v = canon w) : Runtime.Value.eq v w = true :=
  eq_iff_canon.mpr h

/-- An equality test on canonically different values fails. -/
theorem eq_false_of_canon {v w : value} (h : canon v ≠ canon w) :
    Runtime.Value.eq v w = false := by
  cases hv : Runtime.Value.eq v w
  · rfl
  · exact absurd (eq_iff_canon.mp hv) h

/-- `Value.eq` on values related to generated values. -/
theorem eq_of_canon {v w : value} {x y : value} (hv : canon v = canon x) (hw : canon w = canon y) :
    Runtime.Value.eq v w = Runtime.Value.eq x y := by
  rw [Bool.eq_iff_iff, eq_iff_canon, eq_iff_canon, hv, hw]

/-- A canonical boolean payload. -/
theorem canon'_eq_bool {p : value'} {b : Bool} (h : canon' p = .BoolV b) : p = .BoolV b := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  rw [h]

/-- A canonical number payload. -/
theorem canon'_eq_num {p : value'} {m : Num.t} (h : canon' p = .NumV m) : p = .NumV m := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  rw [h]

/-- A canonical text payload. -/
theorem canon'_eq_text {p : value'} {t : ByteText} (h : canon' p = .TextV t) : p = .TextV t := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  rw [h]

/-- A canonical struct payload. -/
theorem canon'_eq_struct {p : value'} {fs : List (Lang.Il.atom × value)}
    (h : canon' p = .StructV fs) : ∃ fs', p = .StructV fs' ∧ canonFields fs' = fs := by
  rcases p with b' | n | s | fs' | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- A canonical case payload. -/
theorem canon'_eq_case {p : value'} {m : Mixfix.t value} (h : canon' p = .CaseV m) :
    ∃ m', p = .CaseV m' ∧ canonMixfix m' = m := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- A canonical tuple payload. -/
theorem canon'_eq_tuple {p : value'} {vs : List value} (h : canon' p = .TupleV vs) :
    ∃ vs', p = .TupleV vs' ∧ canons vs' = vs := by
  rcases p with b' | n | s | fs | c | vs' | (_ | w) | vs' | i | j <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- A canonical list payload. -/
theorem canon'_eq_list {p : value'} {vs : List value} (h : canon' p = .ListV vs) :
    ∃ vs', p = .ListV vs' ∧ canons vs' = vs := by
  rcases p with b' | n | s | fs | c | vs' | (_ | w) | vs' | i | j <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- A canonical `none` payload. -/
theorem canon'_eq_none {p : value'} (h : canon' p = .OptV none) : p = .OptV none := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j <;> simp [canon'] at h
  rfl

/-- A canonical `some` payload. -/
theorem canon'_eq_some {p : value'} {w : value} (h : canon' p = .OptV (some w)) :
    ∃ w', p = .OptV (some w') ∧ canon w' = w := by
  rcases p with b' | n | s | fs | c | vs | (_ | w') | vs | i | j <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- A canonical extern payload: canonicalization compresses the carried JSON. -/
theorem canon'_eq_extern {p : value'} {j : Lean.Json} (h : canon' p = .ExternV j) :
    ∃ j', p = .ExternV j' ∧ Lean.Json.str j'.compress = j := by
  rcases p with b' | n | s | fs | c | vs | (_ | w) | vs | i | j' <;> simp [canon'] at h
  exact ⟨_, rfl, h⟩

/-- Canonical lists are empty together. -/
theorem canons_eq_nil {vs : List value} (h : canons vs = []) : vs = [] := by
  cases vs <;> simp [canons] at h; rfl

/-- Canonical lists extend together. -/
theorem canons_eq_cons {vs : List value} {w : value} {ws : List value}
    (h : canons vs = w :: ws) : ∃ v' vs', vs = v' :: vs' ∧ canon v' = w ∧ canons vs' = ws := by
  cases vs <;> simp [canons] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

/-- Canonical field lists are empty together. -/
theorem canonFields_eq_nil {fs : List (Lang.Il.atom × value)} (h : canonFields fs = []) :
    fs = [] := by
  cases fs <;> simp [canonFields] at h; rfl

/-- Canonical field lists extend together. -/
theorem canonFields_eq_cons {fs : List (Lang.Il.atom × value)} {a : Lang.Il.atom} {w : value}
    {ws : List (Lang.Il.atom × value)} (h : canonFields fs = (a, w) :: ws) :
    ∃ a' v' fs', fs = (a', v') :: fs' ∧ a'.it = a.it ∧ canon v' = w ∧ canonFields fs' = ws := by
  cases fs with
  | nil => simp [canonFields] at h
  | cons f fs =>
    obtain ⟨a', v'⟩ := f
    simp only [canonFields, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨a', v', fs, rfl, ?_, h2, h3⟩
    have := congrArg (·.it) h1
    simpa [mkPhrase] using this

/-- A canonical argument. -/
theorem canonMixfix_eq_arg {m : Mixfix.t value} {w : value} (h : canonMixfix m = .Arg w) :
    ∃ w', m = .Arg w' ∧ canon w' = w := by
  cases m <;> simp [canonMixfix] at h
  exact ⟨_, rfl, h⟩

/-- A canonical atom. -/
theorem canonMixfix_eq_atom {m : Mixfix.t value} {a : Lang.Il.atom} (h : canonMixfix m = .Atom a) :
    ∃ a', m = .Atom a' ∧ a'.it = a.it := by
  cases m <;> simp [canonMixfix] at h
  refine ⟨_, rfl, ?_⟩
  have := congrArg (·.it) h
  simpa [mkPhrase] using this

/-- A canonical bracket. -/
theorem canonMixfix_eq_brack {m : Mixfix.t value} {l r : Lang.Il.atom} {mi : Mixfix.t value}
    (h : canonMixfix m = .Brack l mi r) :
    ∃ l' mi' r', m = .Brack l' mi' r' ∧ l'.it = l.it ∧ canonMixfix mi' = mi ∧ r'.it = r.it := by
  cases m <;> simp [canonMixfix] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨_, _, _, rfl, ?_, h2, ?_⟩
  · have := congrArg (·.it) h1; simpa [mkPhrase] using this
  · have := congrArg (·.it) h3; simpa [mkPhrase] using this

/-- A canonical infix. -/
theorem canonMixfix_eq_infix {m : Mixfix.t value} {a : Lang.Il.atom} {l r : Mixfix.t value}
    (h : canonMixfix m = .Infix l a r) :
    ∃ l' a' r', m = .Infix l' a' r' ∧ canonMixfix l' = l ∧ a'.it = a.it ∧ canonMixfix r' = r := by
  cases m <;> simp [canonMixfix] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨_, _, _, rfl, h1, ?_, h3⟩
  have := congrArg (·.it) h2; simpa [mkPhrase] using this

/-- A canonical sequence. -/
theorem canonMixfix_eq_seq {m : Mixfix.t value} {ms : List (Mixfix.t value)}
    (h : canonMixfix m = .Seq ms) : ∃ ms', m = .Seq ms' ∧ canonMixfixes ms' = ms := by
  cases m <;> simp [canonMixfix] at h
  exact ⟨_, rfl, h⟩

/-- Canonical sequences are empty together. -/
theorem canonMixfixes_eq_nil {ms : List (Mixfix.t value)} (h : canonMixfixes ms = []) :
    ms = [] := by
  cases ms <;> simp [canonMixfixes] at h; rfl

/-- Canonical sequences extend together. -/
theorem canonMixfixes_eq_cons {ms : List (Mixfix.t value)} {n : Mixfix.t value}
    {ns : List (Mixfix.t value)} (h : canonMixfixes ms = n :: ns) :
    ∃ m' ms', ms = m' :: ms' ∧ canonMixfix m' = n ∧ canonMixfixes ms' = ns := by
  cases ms <;> simp [canonMixfixes] at h
  exact ⟨_, _, rfl, h.1, h.2⟩

/-- `canons` of an append. -/
@[simp] theorem canons_append (a b : List value) : canons (a ++ b) = canons a ++ canons b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [canons, ih]

/-- `canons` of a map is a map. -/
theorem canons_eq_map (vs : List value) : canons vs = vs.map canon := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [canons, ih]

/-- `canons` of a prefix: slicing commutes with canonical erasure. -/
theorem canons_take (n : Nat) (vs : List value) : canons (vs.take n) = (canons vs).take n := by
  rw [canons_eq_map, canons_eq_map, List.map_take]

/-- `canons` of a suffix: slicing commutes with canonical erasure. -/
theorem canons_drop (n : Nat) (vs : List value) : canons (vs.drop n) = (canons vs).drop n := by
  rw [canons_eq_map, canons_eq_map, List.map_drop]

/-- Two encodings of the same list agree canonically when they agree on every element. -/
theorem canons_map_congr {α : Type} {f g : α → value} {xs : List α}
    (h : ∀ x ∈ xs, canon (f x) = canon (g x)) : canons (xs.map f) = canons (xs.map g) := by
  rw [canons_eq_map, canons_eq_map, List.map_map, List.map_map]
  exact List.map_congr_left h

/-- The length of a canonical list. -/
@[simp] theorem canons_length (vs : List value) : (canons vs).length = vs.length := by
  rw [canons_eq_map, List.length_map]

/-- A canonical `Make.mk`. -/
@[simp] theorem canon_make_mk (t : typ') (p : value') :
    canon (Runtime.Value.Make.mk t p) = ⟨canon' p, dummy, no_region⟩ := by rw [canon]; rfl


end P4SpecTec.Refine
