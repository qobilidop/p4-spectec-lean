import P4SpecTec.Refine.Value
import P4SpecTec.Interface.P4.Unparse

/-!
Printing congruence for the empty hint environment. Canonical equality erases
type notes, so this result deliberately does not apply to arbitrary hinted
printing. Unsupported runtime payloads remain printer errors.
-/

namespace P4SpecTec.Refine

open P4SpecTec.Lang.Il P4SpecTec.Domain P4SpecTec.P4.Unparse

/-- With no hint table a case always uses its default mixfix printer. -/
theorem printCaseNoHints (c : Mixfix.t value) (note : vnote) (region : Util.Source.region) :
    printWithHints [] ⟨.CaseV c, note, region⟩ = printMixfixWithHints [] c := by
  rw [printWithHints]
  cases note.typ <;> rfl

/-- info: 'P4SpecTec.Refine.printCaseNoHints' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms printCaseNoHints

mutual

/-- Erasing metadata preserves printing when no hint policy can inspect it. -/
theorem printCanon (v : value) : printWithHints [] (canon v) = printWithHints [] v := by
  cases v with
  | mk payload note region =>
    cases payload with
    | BoolV b => simp only [canon, canon', printWithHints]
    | NumV n => simp only [canon, canon', printWithHints]
    | TextV s => simp only [canon, canon', printWithHints]
    | StructV fields => simp only [canon, canon', printWithHints]
    | CaseV c =>
      simp only [canon, canon', printCaseNoHints]
      exact printCanonMixfix c
    | TupleV vs =>
      simp only [canon, canon', printWithHints, printCanonDocs vs]
    | OptV v =>
      cases v with
      | none => simp only [canon, canon', printWithHints]
      | some v =>
        simp only [canon, canon', printWithHints]
        simpa only [canon] using printCanon v
    | ListV vs =>
      simp only [canon, canon', printWithHints, printCanonDocs vs]
    | FuncV fid => simp only [canon, canon', printWithHints]
    | ExternV json => simp only [canon, canon', printWithHints]
termination_by sizeOf v

/-- Canonicalizing a value list preserves its unhinted printing results. -/
theorem printCanonDocs (vs : List value) : printDocs [] (canons vs) = printDocs [] vs := by
  cases vs with
  | nil => rfl
  | cons v vs => simp only [canons, printDocs, printCanon v, printCanonDocs vs]
termination_by sizeOf vs

/-- Canonicalizing mixfix notation preserves unhinted rendering. -/
theorem printCanonMixfix (m : Mixfix.t value) :
    printMixfixWithHints [] (canonMixfix m) = printMixfixWithHints [] m := by
  cases m with
  | Arg v => simp only [canonMixfix, printMixfixWithHints, printCanon v]
  | Atom atom => simp only [canonMixfix, printMixfixWithHints]
  | Brack left m right =>
    simp only [canonMixfix, printMixfixWithHints, printCanonMixfix m]
  | Infix left atom right =>
    simp only [canonMixfix, printMixfixWithHints, printCanonMixfix left, printCanonMixfix right]
  | Seq ms => simp only [canonMixfix, printMixfixWithHints, printCanonMixfixDocs ms]
termination_by sizeOf m

/-- Canonicalizing a mixfix sequence preserves unhinted rendering. -/
theorem printCanonMixfixDocs (ms : List (Mixfix.t value)) :
    printMixfixDocs [] (canonMixfixes ms) = printMixfixDocs [] ms := by
  cases ms with
  | nil => rfl
  | cons m ms =>
    simp only [canonMixfixes, printMixfixDocs, printCanonMixfix m, printCanonMixfixDocs ms]
termination_by sizeOf ms

end

/-- info: 'P4SpecTec.Refine.printCanon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms printCanon
/-- info: 'P4SpecTec.Refine.printCanonDocs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms printCanonDocs
/-- info: 'P4SpecTec.Refine.printCanonMixfix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms printCanonMixfix
/-- info: 'P4SpecTec.Refine.printCanonMixfixDocs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms printCanonMixfixDocs

/-- Canonically equal values have equal unhinted output, including errors. -/
theorem printEqOfCanon {v w : value} (h : canon v = canon w) :
    printWithHints [] v = printWithHints [] w := by
  rw [← printCanon v, h, printCanon]

/-- info: 'P4SpecTec.Refine.printEqOfCanon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms printEqOfCanon

/-- The standard representation relation preserves unhinted printed bytes. -/
theorem printEqOfRel {α : Type} [Prelude.ToValue α] {v : value} {x : α}
    (h : Rel v x) : printWithHints [] v = printWithHints [] (Prelude.toValue x) :=
  printEqOfCanon h

/-- info: 'P4SpecTec.Refine.printEqOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms printEqOfRel

end P4SpecTec.Refine
