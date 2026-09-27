import P4SpecTec.Refine.Environment
import P4SpecTec.Refine.Quote
import P4SpecTec.Refine.Value
import P4SpecTec.Interface.P4.Unparse

/-!
Printing congruence for the empty hint environment. Canonical equality erases
type notes, so this result deliberately does not apply to arbitrary hinted
printing. Unsupported runtime payloads remain printer errors. The dispatch
contracts compose this observation through the actual builtin and global-table
lookup, with the guard-free profile and empty hint policy stated explicitly.
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

/-- Actual unhinted builtin dispatch preserves generated text bytes and hard errors. -/
theorem printBuiltinRunOfRel {α : Type} [Prelude.ToValue α] {v : value} {x : α}
    (h : Rel v x) (targs : List typ) :
    (Interp_al.Effects.builtinEval [] "print_" targs [v]).run =
      (Prelude.Eval.err? ((printWithHints [] (Prelude.toValue x)).toOption.map
        ByteText.ofString)).run.map (Except.map Runtime.Value.Make.text) := by
  unfold Interp_al.Effects.builtinEval
  simp only [Builtin.Call.invokeWithHints, printEqOfRel h]
  cases printWithHints [] (Prelude.toValue x) <;> rfl

/-- info: 'P4SpecTec.Refine.printBuiltinRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms printBuiltinRunOfRel

/-- Full guard-free AL invocation preserves the printer's bytes and errors once lookup succeeds.
The three fuel steps cover function lookup, body dispatch and builtin invocation. -/
theorem invokePrintRunOfRel {α : Type} [Prelude.ToValue α] {v : value} {x : α}
    (h : Rel v x) (fuel : Nat) (cfg : Interp_al.Interp.Config)
    (hguard : cfg.guard = false) (hhints : cfg.printHints = [])
    (ctx : Interp_al.Ctx.t) (internal : Bool) (cursor : Interp_al.Ctx.cursor)
    (tparams : List tparam) (params : List param) (output : typ) (targs : List targ)
    (hfind : Interp_al.Ctx.find_func ctx (Util.Source.mkPhrase "print_") =
      pure (cursor, .Builtin tparams params output)) :
    (Interp_al.Interp.invoke_func (fuel + 3) cfg internal ctx
      (Util.Source.mkPhrase "print_") targs [v]).run =
      (Prelude.Eval.err? ((printWithHints [] (Prelude.toValue x)).toOption.map
        ByteText.ofString)).run.map (Except.map Runtime.Value.Make.text) := by
  simp only [Interp_al.Interp.invoke_func, traced_eq, hfind,
    check_func_inputs_off hguard]
  cases internal <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
      Interp_al.Effects.liftPure, pure_bind, bind_pure,
      Interp_al.Interp.invoke_func_body, Interp_al.Interp.invoke_builtin_func,
      check_func_output_off hguard, hhints]
  all_goals exact printBuiltinRunOfRel h targs

/-- info: 'P4SpecTec.Refine.invokePrintRunOfRel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms invokePrintRunOfRel

/-- The actual builtin declaration in the global table supplies the unhinted print contract. -/
theorem printRunOfHolds {α : Type} [Prelude.ToValue α] {v : value} {x : α}
    (h : Rel v x) (fuel : Nat) (cfg : Interp_al.Interp.Config)
    (hguard : cfg.guard = false) (hhints : cfg.printHints = [])
    (ctx : Interp_al.Ctx.t) (internal : Bool) (tparams : List tparam)
    (params : List param) (output : typ) (targs : List targ)
    (hfenv : ctx.local.fenv = [])
    (hdecl : Holds ctx.global
      (Q.d (.BuiltinDecD (Q.i "print_") tparams params output []))) :
    (Interp_al.Interp.invoke_func (fuel + 3) cfg internal ctx
      (Q.i "print_") targs [v]).run =
      (Prelude.Eval.err? ((printWithHints [] (Prelude.toValue x)).toOption.map
        ByteText.ofString)).run.map (Except.map Runtime.Value.Make.text) := by
  apply invokePrintRunOfRel h fuel cfg hguard hhints ctx internal .Global
    tparams params output targs
  change ctx.global.ftbl.get? "print_" = some (.Builtin tparams params output) at hdecl
  simp only [Interp_al.Ctx.find_func, Interp_al.Ctx.find_func_opt, hfenv, List.lookup, hdecl]
  rfl

/-- info: 'P4SpecTec.Refine.printRunOfHolds' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms printRunOfHolds

end P4SpecTec.Refine
