import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Representation
import P4SpecTec.Runtime.Value.Match

/-!
Representation contracts tested independently of generated encoders: legal nested
parameter instances, arbitrarily deep recursive decoder layers, and source/runtime
shape separation. Counterexamples retain the difference between source runtime
membership and a representable constructor profile; none changes the source checker.
-/

namespace P4SpecTecTest.Representation

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Refine.Representation

/-- Arbitrary legal parameters compose through nested option/list fields. -/
theorem nestedParameters {α : Type} [ToValue α] [OfValue α]
    (source : SourceDomain) (admitted : α → Prop) (legal : Codec source admitted) :
    Adequate (Shape.list (Shape.option (Shape.list source)))
      (fun xs : List (Option (List α)) =>
        ∀ x ∈ xs, ∀ ys ∈ x, ∀ y ∈ ys, admitted y) :=
  legal.list.option.list.adequate

/-- info: 'P4SpecTecTest.Representation.nestedParameters' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms nestedParameters
#audit_axioms nestedParameters

/-- A family of fuel-consuming aliases, with no globally fixed maximum nesting depth. -/
def decodeLayers : Nat → Nat → Lang.Il.value → Option Bool
  | 0, fuel, v => OfValue.ofValue fuel v
  | _ + 1, 0, _ => none
  | level + 1, fuel + 1, v => decodeLayers level fuel v

/-- Well-founded recursive composition supplies a stable bound at every depth. -/
theorem recursiveLayers (b : Bool) :
    ∀ level, Decodes (decodeLayers level) (Runtime.Value.Make.bool b) b := by
  apply decodesWellFounded Nat.lt_wfRel.wf
    (fun level => match level with | 0 => [] | n + 1 => [n])
  · intro i j hj
    cases i with
    | zero => simp at hj
    | succ n => have heq : j = n := by simpa using hj
                subst j
                exact Nat.lt_succ_self n
  · intro i fuel ih
    cases i with
    | zero => rfl
    | succ n => exact ih n (by simp)

/-- info: 'P4SpecTecTest.Representation.recursiveLayers' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recursiveLayers
#audit_axioms recursiveLayers

/-- Source `nat` membership is strictly broader than the current natural decoder shape. -/
theorem naturalMembershipCounterexample :
    Runtime.Value.Match.sub_checked (fun _ => none) (fun _ => some (.ok none)) 1
      (Q.t (.NumT .NatT)) (Runtime.Value.Make.int 0) = some (.ok true) ∧
    (∀ fuel, OfValue.ofValue (α := Nat) fuel (Runtime.Value.Make.int 0) = none) ∧
    (∀ n : Nat, ¬Rel (Runtime.Value.Make.int 0) n) := by
  refine ⟨by cbv, fun _ => rfl, ?_⟩
  intro n h
  cases h

/-- info: 'P4SpecTecTest.Representation.naturalMembershipCounterexample' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms naturalMembershipCounterexample
#audit_axioms naturalMembershipCounterexample

/-- An integer decoder can succeed outside the integer-tag profile and change observations. -/
theorem integerDecodeCounterexample :
    OfValue.ofValue (α := Int) 0 (Runtime.Value.Make.nat 0) = some 0 ∧
      ¬Rel (Runtime.Value.Make.nat 0) (0 : Int) := by
  refine ⟨rfl, ?_⟩
  intro h
  cases h

/-- info: 'P4SpecTecTest.Representation.integerDecodeCounterexample' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms integerDecodeCounterexample
#audit_axioms integerDecodeCounterexample

/-- Checked runtime optional membership does not itself enforce an option constructor. -/
theorem optionMembershipCounterexample :
    Runtime.Value.Match.sub_checked (fun _ => none) (fun _ => some (.ok none)) 1
      (Q.t (.IterT (Q.t .BoolT) .Opt)) (Runtime.Value.Make.bool true) = some (.ok true) ∧
      ¬Shape.option Shape.bool (Runtime.Value.Make.bool true) := by
  constructor
  · cbv
  · intro h
    rcases h with h | ⟨v, h, _⟩ <;> cases h

/-- info: 'P4SpecTecTest.Representation.optionMembershipCounterexample' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms optionMembershipCounterexample
#audit_axioms optionMembershipCounterexample

/-- Arbitrary raw target payloads have their own codec and remain outside Boolean source shape. -/
theorem rawRuntimeSeparation (j : Lean.Json) :
    (∃ x : ExternValue, Rel (Runtime.Value.Make.extern .TextT j) x) ∧
      ¬Shape.bool (Runtime.Value.Make.extern .TextT j) := by
  constructor
  · obtain ⟨x, _, hx⟩ := externCodec.adequate.coverage
      (Runtime.Value.Make.extern .TextT j) ⟨j, rfl⟩
    exact ⟨x, hx⟩
  · intro ⟨b, hb⟩
    cases hb

/-- info: 'P4SpecTecTest.Representation.rawRuntimeSeparation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rawRuntimeSeparation
#audit_axioms rawRuntimeSeparation

/-- An independent recursive source grammar, with arbitrary metadata at every layer. -/
inductive LayerShape : Lang.Il.value → Prop where
  | leaf (b : Bool) (note : Lang.Il.vnote) (location : Util.Source.region) :
      LayerShape ⟨.BoolV b, note, location⟩
  | some (v : Lang.Il.value) (note : Lang.Il.vnote) (location : Util.Source.region) :
      LayerShape v → LayerShape ⟨.OptV (some v), note, location⟩

/-- A distinct generated-style carrier for the independent recursive source grammar. -/
inductive Layer where
  | leaf (b : Bool)
  | wrap (inner : Layer)

def Layer.encode : Layer → Lang.Il.value
  | .leaf b => Runtime.Value.Make.bool b
  | .wrap x => Runtime.Value.Make.opt .TextT (some x.encode)

instance : ToValue Layer := ⟨Layer.encode⟩

def Layer.decode : Nat → Lang.Il.value → Option Layer
  | 0, _ => none
  | fuel + 1, v => match v.it with
    | .BoolV b => some (.leaf b)
    | .OptV (some w) => (Layer.decode fuel w).map Layer.wrap
    | _ => none

instance : OfValue Layer := ⟨Layer.decode⟩

/-- The recursive source grammar is covered with one bound for every admitted input. -/
theorem layerCoverage (v : Lang.Il.value) (h : LayerShape v) :
    ∃ x : Layer, Rel v x ∧ Decodes Layer.decode v x := by
  induction h with
  | leaf b note location =>
    refine ⟨.leaf b, rfl, 1, ?_⟩
    intro fuel hf
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | some v note location _ ih =>
    obtain ⟨x, hr, bound, hb⟩ := ih
    refine ⟨.wrap x, ?_, bound + 1, ?_⟩
    · exact relSome hr note location
    · intro fuel hf
      cases fuel with
      | zero => omega
      | succ fuel =>
        change (Layer.decode fuel v).map Layer.wrap = some (.wrap x)
        rw [hb fuel (by omega)]
        rfl

/-- info: 'P4SpecTecTest.Representation.layerCoverage' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms layerCoverage
#audit_axioms layerCoverage

/-- A recursive source grammar, independent carrier validity and actual decoder form a codec. -/
theorem layerCodec : Codec LayerShape (fun _ : Layer => True) where
  encodingValid x _ := by
    induction x with
    | leaf b => exact .leaf b _ _
    | wrap x ih => exact .some (toValue x) _ _ ih
  decoder.sufficient v hv := by
    obtain ⟨x, _, hx⟩ := layerCoverage v hv
    exact ⟨x, hx⟩
  decoder.sound fuel v x hv hd := by
    refine ⟨True.intro, ?_⟩
    change Layer.decode fuel v = some x at hd
    induction hv generalizing fuel x with
    | leaf b note location =>
      cases fuel with
      | zero => cases hd
      | succ fuel => cases hd; rfl
    | some v note location _ ih =>
      cases fuel with
      | zero => cases hd
      | succ fuel =>
        change (Layer.decode fuel v).map Layer.wrap = some x at hd
        cases hc : Layer.decode fuel v with
        | none => simp [hc] at hd
        | some y =>
          have heq : Layer.wrap y = x := by simpa [hc] using hd
          subst x
          exact relSome (ih fuel y hc) note location

/-- info: 'P4SpecTecTest.Representation.layerCodec' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms layerCodec
#audit_axioms layerCodec

end P4SpecTecTest.Representation
