# Review: M2 phase D (rung 3 as built)

Independent read-only review, 2026-09-25, of the uncommitted phase D on
`m2-nano-p4`: `Refine/`, `Codegen/{Reify,Validate,Emit}.lean`,
`Tactic/Refine.lean`, `NanoP4Spec/Refinement.lean`, the `is_iter_var_exp`
change, the product `ToValue` instances, `docs/design.md` 5.1 and 6,
`.agents/decisions.md`, `.agents/notes/m2-phase-d.md`. No build was run
(one was in progress); `git diff`, `grep`, `awk` and a JSON walk were.

## Verdict

The theorems say what the note says they say, the tactic cannot admit a
false goal, and the interpreter change shrinks a deviation. Two things
must be fixed before the commit lands (a text-gate failure and the
vacuity risk of `HoldsSpec`), and three gaps should be written down where
a reader of the design would otherwise overestimate what rung 3 covers.

## What is proved (question 1)

Per covered `X`, for every fuel, every `cfg` with `guard = false`, every
`ctx` with `local.fenv = []` and `HoldsSpec spec ctx.global`, every
`internal`, and every `vᵢ` with `canon vᵢ = canon (toValue pᵢ)`: if
`invoke_func fuel … [vᵢ]` has a defined result, `X pᵢ` has one, the same
`Fail` or values canonically equal (`Calc.lean:35-43`). The direction is
the right one for validation: a generated `none` (`partial_fixpoint`
non-termination), a wrong failure kind, or a wrong value is caught; the
one unobservable case is the interpreter diverging at every fuel, which
is a port bug, not a codegen bug.

The hypotheses: `guard` only gates the four `check_*` functions
(`Interp.lean:91-130`), proved to be `pure ()` (`Calc.lean:348-368`);
`traced` is proved the identity for every `cfg`; `internal` only skips
those same checks; `fenv = []` makes `find_func` read the global table
(`Ctx.lean:210-214`) and is re-established for callees because
`eval_call_exp` passes the caller's localized context. None hides a
codegen bug. `Holds` matches `Ctx.load_def` case for case
(`Calc.lean:319-331` against `Ctx.lean:103-115`, itself against
`ctx.ml:89-118`).

`Rel` up to `canon` loses exactly what the interpreter's `Value.eq`
ignores, and this is a theorem, not a claim (`eq_iff_canon`,
`Value.lean:180`). Notes, regions, function ids and extern JSON are the
whole difference. Nano-P4 has no function values, so nothing the corpus
compares is collapsed.

## Findings

### High

1. **The text gate will fail on commit.** `NanoP4Spec/Refinement.lean`
   has 96 lines over 100 characters (the `-- no refinement theorem:`
   lines, e.g. 704, 792, 965, and corollary applications such as 875),
   and `P4SpecTec/Codegen/Validate.lean:107,157,196` are 101-102. Both
   files are untracked, so `scripts/check-text.sh` (which walks
   `git ls-files`) passes today and fails once they are added. Fix in
   `Validate.groupTheorems`: one reason per comment line, and break the
   corollary application after the group name; wrap the three source
   lines.

### Medium

2. **`HoldsSpec NanoP4Spec.spec g` has no witness.** Nothing proves or
   even executes that `Ctx.init NanoP4Spec.spec` succeeds and yields a
   `g` satisfying it. If two quoted definitions shared an id in one
   table, or `Holds` drifted from `load_def`, every theorem would be
   vacuously true and the build green. Suggest, in order of strength: a
   generic lemma `Ctx.init spec = .ok g → HoldsSpec spec g` (the
   `contains` guards in `add_*_global`, `Ctx.lean:86-98`, make it hold
   without a nodup hypothesis; `Std.HashMap.getElem?_insert` is the
   lemma); or a `lake test` file that runs `Ctx.init NanoP4Spec.spec`
   and checks each `Holds` executably. Either belongs in phase E.

3. **The quoting is trusted, not checked.** `Reify` is a second consumer
   of the AST; no test compares `NanoP4Spec.spec` with the export modulo
   regions and hints. I read every case of `Reify.lean` against
   `Lang/Il/Ast.lean` and `Lang/Al/Ast.lean`: every constructor of
   `exp'`, `path'`, `prem'`, `arg'`, `param'`, `deftyp'`, `def'` is
   reproduced, notes are kept on `exp` and `path`, hints and regions are
   the only omissions and the interpreter reads neither (`hints` occurs
   only in `Subst.lean:81-85`, where it is passed through). One latent
   trap: `Reify.op` (`Reify.lean:116-117`) derives the constructor from
   the last `.`-component of `repr`, which is right only while
   `unop`/`binop`/`cmpop`/`optyp` are nullary (`Ast.lean:97-154`); a
   field would print as `.IntT)`. Suggest a decode-and-compare test
   (`Decode.lean` already parses the export): erase regions and hints,
   `BEq` against `NanoP4Spec.spec` element by element. That moves
   `Reify` from trusted to checked, which is the design's own criterion.

4. **No relation is in the fragment.** All 18 theorems are
   `invoke_func` on `FuncDecD`s (`grep invoke_rel Refinement.lean`: 0).
   The relation statement (`resultRel`, `Outs`, `invoke_rel`,
   `Validate.lean:87-107`) and the tactic's rule paths (`match_rule`,
   `RulePr`, `IfHoldPr`, `refines_notHold`) are unexercised. Design 5.1
   leads with the relation form and the note says "a relation, a
   function or a table". State in `status.md` and 5.1 that at M2 the
   fragment is 18 functions and 0 relations, 0 tables, and make a
   relation the first M3 target.

5. **What the theorem cannot see is not written down.** It quantifies
   over generated values and their images. An IL value outside the
   image of `toValue` (a variant case codegen dropped, a field it
   misplaced) is never exercised, and `toValue`'s notes are placeholders
   (`.TextT` for tuples and options, `Prelude/Value.lean:55,74`) that
   `canon` erases. Rung 3 validates definitions relative to the generated
   types; the types themselves are checked only by rung 2's decode test.
   This is the one place a `Codegen/Types.lean` bug can hide behind a
   green rung 3. Add a "what it does not cover" paragraph to 5.1; the
   remedy (an `OfValue`/`toValue` round-trip theorem per type) is an M3
   item for the roadmap.

6. **`ToValue (α × β)` flattens right-nested products**
   (`Prelude/Value.lean:57-75`). `A × (B × C)` and `A × B × C` are one
   Lean type, so a spec tuple `(A, (B, C))` would encode as a flat
   3-tuple while its IL value is nested. The Nano-P4 export has no
   nested `TupleT` element (0 of 146, counted), so no theorem is
   affected today; the full spec may differ. Record it in 5.3 with the
   trigger, or have the generator name nested tuple types.

7. **The "wrong answer at fuel zero" class survives elsewhere.**
   `Match.sub_` and `check'` answer `false` at zero (`Match.lean:34,109`)
   and `Subst.subst_typ_inner` returns the type unchanged
   (`Subst.lean:42`). Their fuel is a constant 1000 spent per nesting
   level, not the interpreter's fuel, so rung 3 is unaffected now; but it
   is a silent truncation, and when casts and subtype checks enter the
   fragment `simp` will have to unfold `sub_` on the literal `1000`
   (equations on `fuel + 1` do not fire on a literal). The
   `termination_by sizeOf` pattern used for `is_iter_var_exp` applies.

### Low

8. `valueConstants` (`Tactic/Refine.lean:203-215`) scans the whole
   environment by substring on every `refine_al` call; O(|env|) per
   theorem, and `.instBEq` matches unrelated instances. Cache per
   environment or emit the list from the generator.
9. `fuelledHelpers : List Name := []` (`Tactic/Refine.lean:380`) is dead.
10. `Tactic/Refine.lean:1268-1269`: two trailing blank lines.
11. The `DecidableEq` instances for `Atom.t` and `iter` sit in
    `Calc.lean:427,654`, not beside their (mirrored) types; say why.
12. Design 5.1 does not mention `internal`; half a sentence. Section 5's
    promised mutation check ("mutate codegen and require rung 3 to
    fail") has not been run; phase E should swap two clauses of
    `$exists_` in `Funcs.lean` output once and record the failure.
13. `Refinement.lean` sets `maxHeartbeats 4000000` (20x default) with no
    per-theorem time recorded yet; the timing table in phase E should
    justify the budget.

## The tactic (question 3)

No `sorry`, `admit`, `native_decide` or `decide`-by-evaluation anywhere in
the new files. Every step is `evalTactic` of a kernel-checked tactic
(`simp only`, `cases`, `subst`, `obtain`, `split`, `by_cases`, `omega`,
`contradiction`, `assumption`) or `apply`/`refine` of a lemma proved in
`Calc.lean`; `withoutRecover` (`Refine.lean:1265`) stops error recovery
from admitting a goal; `tryTac` restores state on failure
(`RunSound.lean:31-38`); `memProof` hand-builds a `List.Mem` term that
`assert` type-checks; `#audit_axioms` on each corollary audits the group
theorem transitively. A failing step throws with the interpreter head
and the generated head, which is the right diagnostic. Robustness risks
are the environment scan (8), the name-derived `libOf`, and the
heartbeat budget (13); none is a soundness risk.

## `is_iter_var_exp` (question 2)

Faithful to `interp.ml:134-148`: `Id.eq id_var id_iter` is `.it ==`,
`iters_var = iters_iter` is `==` on the derived `BEq (List iter)`, the
call sites pass the same synthesized `IterE` phrase. The fuel was a
deviation; removing it makes the port closer to upstream, and 5.3 records
the `termination_by`. The trusted base did not grow. The `mkPhrase`
reducibility change in the mirrored `Util/Source.lean` is an attribute
only and is recorded in 5.3.

## Documentation (question 5)

5.1 describes the code accurately: statement, hypotheses, group
induction, tactic strategy and fragment all match `Validate.lean` and
`Refine.lean`. The gaps are omissions (findings 4, 5, 12), not
misstatements. Section 6's tree and the "Rung 3 lives in" paragraph are
current. `decisions.md` records the three decisions with reasons and a
revisit trigger; `status.md` is current except for the relation count.

## Hygiene (question 6)

Docstrings are on every declaration, modules open with `/-! -/`
docstrings, naming follows Lean style in our code and upstream's in
mirrors, imports are precise. Only finding 1 fails a gate.

## What is good

- `eq_iff_canon` makes the value relation the kernel of the
  interpreter's own equality by proof, not by definition; that is the
  strongest possible anchor for `Rel` and it costs 60 lines.
- The calculus is a dozen total lemmas, each an exhaustive case split;
  it is reviewable in one sitting and has no interpreter knowledge.
- Divergence-refines-anything plus quantification over every fuel turns
  the fuel into an induction measure with no semantic residue.
- The fragment is decided syntactically, closed under callees in
  `Emit`, and printed inline with reasons; coverage is visible in the
  generated file rather than in a claim.
- The tactic's failure messages and stderr trace are exactly what
  driving it on M3's definitions will need.
