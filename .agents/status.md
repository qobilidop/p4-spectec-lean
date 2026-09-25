# Status

Where the work stands now. Updated at every checkpoint; holds current
state only.

Last updated: 2026-09-25. **Milestone M2 (Nano-P4, rung 3 and the lemma
library) is closed; nothing is active.** Delivered: the fuel-free
executable encoding in the `Eval` monad with `partial_fixpoint`; the
`Prop` encoding of every relation with a generated, tactic-proved
run-soundness theorem and an axiom audit; the AL interpreter ported to
Lean and agreeing with upstream on the corpus as the second leg of rung
2; rung 3 (every definition quoted, the value relation, the refinement
calculus with a proved witness for its table hypothesis, refinement
theorems proved by `refine_al` for 18 definitions, one module per
recursion group); determinism theorems where provable (2 of 77
relations). The next milestone, M3 (the full P4 spec), needs a scope from
the user before it starts.

## Current state

| Scope | Result | Revision |
|---|---|---|
| Design | agreed; revised for M1's findings (AL not IL as the export, fuel, module grouping, naming rule) | `main` |
| Upstream build | P4-SpecTec at the `gsoc-nano-spec` pin builds in the `upstream` Nix shell on nixpkgs' OCaml 5.5 with `scripts/build-upstream.sh` | `main` |
| Export | `elab -json`, `algo -json` and `nano parse -json` from `upstream/patches/0001-json-export.patch`; `exports/nano-p4.al.json` (8.5 MB), 78 booted programs with upstream's verdicts under `exports/programs/nano-p4/` | `main` |
| Deep embedding | `P4SpecTec/Lang/Il/Ast.lean`, `Lang/Al/Ast.lean` and their JSON decoders mirror `lang/il/ast.ml`, `lang/al/ast.ml` at the same paths; `scripts/check-mirror.py` derives every mirrored pair from the paths and checks constructor lists and order | `main` |
| Prelude | `Runtime/Value/Value.lean` and `Interface/P4/Unparse.lean` mirror value construction, accessors, comparison and the printer; `Interface/Builtin/` ports every builtin file, with unit tests in `P4SpecTecTest/Builtins.lean` and the dispatcher on values `Call.lean`; `Prelude/` holds `ToValue`/`OfValue`, the `Eval` monad, numerics and iteration helpers | `main` |
| Interpreter | `Interp/InterpAl/{Backtrack,Ctx,Interp}.lean` mirror `interp/interp-al/` function by function, with fuel, over `Runtime/Value/Match.lean`, `Runtime/Type/{Typdef,Typ,Subst}.lean`, `Runtime/Dynamic/Var.lean`, `Runtime/DynamicAl/{Rel,Func}.lean`, `Lang/Hints/Input.lean`; `lake exe nano-p4-interp` (`P4SpecTecTest/Diff/NanoP4Interp/Main.lean`) runs `Program_ok` on the deep terms against the AL export | `main` |
| Codegen | `lake exe p4spectec-gen`: types, subtype bridges, functions, builtins, relations in both encodings, run-soundness theorems with audits, `Externs` class, per-file modules, `--check`/`--update`; every definition in `Eval := ExceptT Fail Option`, recursive groups by `partial_fixpoint`, no fuel | `main` |
| Tactics | `P4SpecTec/Tactic/RunSound.lean`: `run_sound` (symbolic execution of a run function against its `Prop` constructor) and `run_sound_group` (over `mutual_partial_correctness`, matching conjuncts by function); `Tactic/Refine.lean`: `refine_al`, lockstep execution of the interpreter port and the generated code (design 5.1); `Tactic/Audit.lean`: `#audit_axioms` | `main` |
| Rung 3 | `Refine/Value.lean` (`canon`, `Rel`, `eq_iff_canon`), `Refine/Quote.lean`, `Refine/Calc.lean` (`Refines`, `Holds`, `HoldsSpec`, exposure lemmas); `Codegen/Reify.lean` quotes every definition (`d.al`), `Codegen/Validate.lean` states the theorems and decides the fragment; `NanoP4Spec/Refinement.lean` holds `spec` (the quoted spec as a list) and the theorems: 18 of 153 definitions are in the fragment (18 functions, 0 relations: no builtin calls, casts, subtype checks, iteration bodies, iterated premises, type parameters, externs, indexing), all 18 theorems proved and audited; the rest are listed there with reasons | `main` |
| Generated | `NanoP4Spec/`: 27 modules named after the spec files (56.8k lines), then `Refinement/` (the quoted spec and one module per covered recursion group, 19 modules) and `Refinement.lean`, 48 modules in all, building with `--wfail`; 161 types, 76 functions, 77 relations in both encodings (77 `Prop` inductives, 98 run-soundness theorems: 77 `R.run_sound` and 21 group theorems, each audited); 65 `partial_fixpoint` definitions; 18 refinement theorems and 2 determinism theorems, each audited | `main` |
| Rung 2 | `test/diff/run.py`, two legs: the generated `Program_ok.run` and the interpreter port each agree with the AL interpreter's verdict on 78 of 78 programs (48 pass, 30 fail: 32 positive, 21 negative, 25 exercises); for the 48 that pass, the output typing context equals upstream's value on both legs | `main` |
| Timing | `docs/timing-nano-p4.md`: 860.6 s of elaboration over 48 modules (per-module sum); the 18 refinement groups are 19 to 89 s each and build in parallel, so a full rebuild of `NanoP4Spec` takes 123 s wall on 16 cores (was about 13.5 min as one module). Only the `Refinement/` modules import the tactic, so a tactic edit rebuilds only them; a gate rerun with nothing changed takes 7 s | `main` |

## Last checked evidence

2026-09-25, on the M2 branch with phases D and E, `scripts/check.sh` in
the Nix shell: exit 0 (layout, text, imports, mirror, `lake build --wfail`
with the generated modules (48 after the per-group split), the 18 refinement theorems, the 2
determinism theorems and the 98 run-soundness theorems, each with
`#audit_axioms`, `lake test`, keyword table, `p4spectec-gen --check`, and
the harness: 78 of 78 verdicts agree on both legs, 48 output typing
contexts equal), rerun after merging `main` (three Dependabot workflow
bumps) and after splitting the refinement theorems per group: exit 0. CI
on pull request #4 at `8c8d099`, run 36170670305: success (33 min on a
cold `.lake` cache; the cache on `main` predated the new modules).

## Open threads

- **Rung 3's proof time**: 19 to 89 s per group, parallel across groups;
  at the full spec's size this is the budget to watch. The profile is in
  the tactic's trace; caching the simp set (rebuilt per theorem, with a
  scan of the environment) is the next lever.
- **Rung 3 covers 18 of 153 definitions.** Growing the fragment is the
  M3 work order for rung 3, in this order of payoff: builtin calls (a
  lemma per builtin relating the port on values to the wrapper), iterated
  expressions and premises (`sub_list`/`mapM` against the generated
  `List.map`/`mapM`), casts and subtype checks (per-type lemmas about
  `upcast`/`downcast`/`Match.sub` against the generated bridges), then
  indexing, slicing, membership, type parameters, externs. The
  completeness direction (`R i o → R.run i = some (.ok o)`) is not stated
  (design section 12).
- The tactic's own diagnostics (`set_option refine_al.trace true`: the
  steps, the phase times) stay in `Tactic/Refine.lean`; the trace goes to
  stderr so that a failing step does not discard it.
- **Review findings on rung 3 open for M3** (the M2 review, in git history
  as `.agents/reviews/m2-phase-d.md`, readable at commit `530f132`; the `HoldsSpec`
  witness it asked for is proved, `holdsSpec_of_init`):
  the quoting is trusted (a
  decode-erase-compare test of `NanoP4Spec.spec` against the export is
  the check to add); `Match.sub_`/`check'` answer `false` and
  `Subst.subst_typ_inner` the identity at fuel zero, the class of wart
  fixed in `is_iter_var_exp`, harmless while their fuel is the constant
  1000 but in the way once casts enter the fragment; the codegen mutation
  check the design promises has not been run.
- The interpreter's `Value.Match.sub_` yields `false` for function values
  (`FuncT`), since `Type.Equiv` is not ported; Nano-P4 has none, the full
  spec has (M3).
- **Readability of the `Prop` encoding**: a `matches` check on a value
  that a pattern later substitutes appears as `match C x with | C _ =>
  true | _ => false = true`, and an unzipped iteration variable appears
  as `List.map (·.1) tmp_n`; both are faithful and provable, both could
  be simplified by the generator later (roadmap, readability).
- **Packet leg of rung 2** (nano-switch simulation) is M3 by the design
  ("target instances arrive with the packet leg"); the `Externs` class is
  generated, no instance exists yet.
- Path updates with indexing (`e[p[i] = v]`) are rejected by codegen;
  Nano-P4 has none. Needed for M3.
- `fresh_typeId` (a stateful builtin) has no port; not used by Nano-P4.
- `print` hints are rejected by codegen (Nano-P4 has none); hint-driven
  printing is needed for the full spec at M3. The AL's `subcheck` is not
  consulted for subtype checks: codegen asserts that a shared case has the
  same argument types on both sides and fails otherwise.
- The M1 review (in git history, `.agents/reviews/m1-nano-p4.md`, deleted by `bfecb2e`; read it at `bfecb2e^`, before
  the M1 close) is fully dispositioned; its two high findings are fixed on
  `main`. Its open fidelity notes are the last item below.
- Sizes: `exports/programs/nano-p4/` is 11 MB of JSON (regions with paths
  dominate). Acceptable; revisit if the full corpus at M3 is unwieldy.
- Generated code is functional but verbose (a temporary per hoisted
  call, alternatives nested in parentheses). Readability work is parked in
  the roadmap; the format is stable to diff.
- Small fidelity gaps noted by the review, not yet closed: `Value.compare`
  orders `ExternV` by key-sorted compressed JSON where upstream compares
  Yojson structurally; `Lang/Xl/Num.lean` mirrors the types but not
  `compare`/`bin`/`cmp` (those live under Lean names in `Prelude/Num.lean`
  and `Runtime/Value/Value.lean`); text length and indexing count
  characters where upstream counts bytes; `Texts.text_to_int` accepts
  less than `Bigint.of_string`; `Names.ctorName` is invertible only up to
  the `_` join and the `_2` suffix.

## Blocked

Nothing.
