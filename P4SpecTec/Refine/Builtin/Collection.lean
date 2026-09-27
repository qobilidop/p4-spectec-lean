import P4SpecTec.Refine.ValueShape
import P4SpecTec.Interface.Builtin.Call

/-! Representation lemmas for the existing bracketed collection and colon pair constructors. -/

namespace P4SpecTec.Refine.Builtin.Collection

open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine P4SpecTec.Domain

/-- The shared source set/map constructor, retaining the exact ordered element list. -/
def bracketed (xs : List Lang.Il.value) : Lang.Il.value :=
  Runtime.Value.Make.case .TextT
    (.Brack (Value.atom .LBrace) (.Arg (Runtime.Value.Make.list .TextT xs))
      (Value.atom .RBrace))

/-- The source map pair constructor, retaining separate key and value payloads. -/
def colon (key val : Lang.Il.value) : Lang.Il.value :=
  Runtime.Value.Make.case .TextT
    (.Seq [.Arg key, .Atom (Value.atom (.Operator ":")), .Arg val])

/-- Related bracketed collections decode with an unchanged canonical element list. -/
theorem bracketedDecodeOfRel {v : Lang.Il.value} {xs : List Lang.Il.value}
    (h : Rel v (bracketed xs)) :
    ∃ raws, P4SpecTec.Builtin.Call.set_of_value v = some raws ∧
      canons raws = canons xs := by
  have hc : canon' v.it = .CaseV
      (.Brack (Value.atom .LBrace)
        (.Arg (canon (Runtime.Value.Make.list .TextT xs))) (Value.atom .RBrace)) :=
    canon_eq_it h
  obtain ⟨m, hv, hm⟩ := canon'_eq_case hc
  obtain ⟨left, arg, right, rfl, hl, ha, hr⟩ := canonMixfix_eq_brack hm
  obtain ⟨list, rfl, he⟩ := canonMixfix_eq_arg ha
  obtain ⟨raws, hlist, hs⟩ := canon'_eq_list (canon_eq_it he)
  refine ⟨raws, ?_, hs⟩
  cases v with
  | mk payload note region =>
    change payload = .CaseV (.Brack left (.Arg list) right) at hv
    subst payload
    cases list with
    | mk payload note2 region2 =>
      change payload = .ListV raws at hlist
      subst payload
      have hmop : Mixfix.eq_mixop
          (.Brack left (.Arg (⟨.ListV raws, note2, region2⟩ : Lang.Il.value)) right)
          P4SpecTec.Builtin.Call.mixop_set = true := by
        simp only [Mixfix.eq_mixop, Mixfix.eq, P4SpecTec.Builtin.Call.mixop_set, hl, hr]
        rfl
      simp [P4SpecTec.Builtin.Call.set_of_value, Runtime.Value.Get.case,
        Value.caseArgs, hmop, Mixfix.args, Runtime.Value.Get.list]

/-- info: 'P4SpecTec.Refine.Builtin.Collection.bracketedDecodeOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms bracketedDecodeOfRel

/-- Related colon pairs decode into separately related key and value payloads. -/
theorem colonDecodeOfRel {v key val : Lang.Il.value} (h : Rel v (colon key val)) :
    ∃ rawKey rawVal, P4SpecTec.Builtin.Call.pair_of_value v = some (rawKey, rawVal) ∧
      canon rawKey = canon key ∧ canon rawVal = canon val := by
  have hc : canon' v.it = .CaseV
      (.Seq [.Arg (canon key), .Atom (Value.atom (.Operator ":")), .Arg (canon val)]) :=
    canon_eq_it h
  obtain ⟨m, hv, hm⟩ := canon'_eq_case hc
  obtain ⟨ms, rfl, hs⟩ := canonMixfix_eq_seq hm
  obtain ⟨argKey, rest1, rfl, keyArg, tail1⟩ := canonMixfixes_eq_cons hs
  obtain ⟨rawKey, rfl, keyCanon⟩ := canonMixfix_eq_arg keyArg
  obtain ⟨atom, rest2, rfl, atomArg, tail2⟩ := canonMixfixes_eq_cons tail1
  obtain ⟨rawAtom, rfl, atomIt⟩ := canonMixfix_eq_atom atomArg
  obtain ⟨argVal, rest3, rfl, valueArg, tail3⟩ := canonMixfixes_eq_cons tail2
  obtain ⟨rawVal, rfl, valueCanon⟩ := canonMixfix_eq_arg valueArg
  have hn := canonMixfixes_eq_nil tail3
  subst rest3
  refine ⟨rawKey, rawVal, ?_, keyCanon, valueCanon⟩
  cases v with
  | mk payload note region =>
    change payload = .CaseV (.Seq [.Arg rawKey, .Atom rawAtom, .Arg rawVal]) at hv
    subst payload
    have hmop : Mixfix.eq_mixop (.Seq [.Arg rawKey, .Atom rawAtom, .Arg rawVal])
        P4SpecTec.Builtin.Call.mixop_pair = true := by
      simp only [Mixfix.eq_mixop, Mixfix.eq, Mixfix.eq.eqs,
        P4SpecTec.Builtin.Call.mixop_pair, atomIt]
      rfl
    simp [P4SpecTec.Builtin.Call.pair_of_value, Runtime.Value.Get.case,
      Value.caseArgs, hmop, Mixfix.args]

/-- info: 'P4SpecTec.Refine.Builtin.Collection.colonDecodeOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms colonDecodeOfRel

end P4SpecTec.Refine.Builtin.Collection
