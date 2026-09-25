# Status

Where the work stands now. Updated at every checkpoint; holds current
state only.

Last updated: 2026-09-25. **Milestone M2 (Nano-P4, rung 3 and the lemma
library) is closed; M3A is complete on `m3a-full-p4`.** Delivered: the fuel-free
executable encoding in the `Eval` monad with `partial_fixpoint`; the
`Prop` encoding of every relation with a generated, tactic-proved
run-soundness theorem and an axiom audit; the AL interpreter ported to
Lean and agreeing with upstream on the corpus as the second leg of rung
2; rung 3 (every definition quoted, the value relation, the refinement
calculus with a proved witness for its table hypothesis, refinement
theorems proved by `refine_al` for 18 definitions, one module per
recursion group); determinism theorems where provable (2 of 77
relations). The user authorized M3A: recursive spec export, the full pinned
P4 AL export and a capability census, a generated-quotation comparison
against the export, and an evidence-based plan for the rest of M3.
The user has now authorized autonomous staged completion of all M3,
including rendering, differential validation, targets and proofs. Make
reasonable reversible decisions, record uncertainty for later review,
and do not wait for routine choices. This does not authorize weakening
correctness requirements or destructive published-history changes.

## Active M3B byte-text foundation

- Branch `m3b-byte-foundation`, based on state PR #9 head `019c665`.
  Integrated the independently reviewed ByteArray-backed `ByteText`
  foundation from the isolated worktree. No IL, generator, interpreter
  or builtin behavior changed yet. Review: `.agents/reviews/m3b-byte-text.md`.
- Focused implementation/reviewer builds, both library roots and hygiene
  passed. The first primary gate exited 1 on a missing "not a mirror"
  header marker; fixed. A fresh full gate exited 0 with no skips, including
  rebuilt Nano proofs and unchanged generated output. Inventory and
  integration boundaries: `.agents/notes/byte-text.md`.
- The state calculus/proof prototype is active in isolated worktree
  `/Users/qobilidop/my/work/p4-spectec-lean-fresh-state`, branch
  `m3b-state-calculus`, with GPT-6 Astra. No generator/interpreter edits.
- Byte substrate integration is active separately in
  `/Users/qobilidop/my/work/p4-spectec-lean-byte-text`, branch
  `m3b-byte-semantics`. Root is migrating IL/runtime/codegen/interpreter
  and proofs; GPT-6 Sol migrated text builtins and is recording pinned
  upstream byte-safe observations. Initial focused core/compiler/value
  and refinement-calculus builds pass; no integration full gate yet.
- PR #7 (print) passed remote CI and merged as `5e1aa79`. PR #8 (list
  updates) passed remote CI and merged into main. PR #9 (state
  foundation/plan) is published and locally gated; its remote CI is pending.

## Completed M3B fresh-state foundation

- Branch `m3b-state-foundation`, based on list-update PR #8 head `3b8175f`.
  The isolated experiment has been integrated without changing generated
  definitions or interpreter behavior. `StateEval` retains allocations on
  failures/negation and models the 63-bit signed counter. Twenty-four
  computation checks and five audited run lemmas pass focused builds.
- Independent read-only review passed; see
  `.agents/reviews/m3b-fresh-state.md`. The full primary-worktree gate
  exited 0, no skips: all Nano proofs rebuilt, generator output unchanged,
  both differential legs, quotations, printer fixtures and census pass.
  No generator, stateful refinement or memoization claim.
- The integration direction is now recorded in
  `.agents/notes/state-integration.md`: uniform full-spec state selected
  structurally, one shared interpreter, state-indexed successful rules
  with rejected-prefix evidence. The audit caught shared rule prefixes
  that must rerun on each attempt before effects can be enabled.
  A separate ignored scratch probe
  demonstrated an Option-returning recursive allocator with
  `partial_fixpoint` and an audited standard axiom set after adding two
  monotonicity lemmas; this is not yet a committed API or full integration.
- The ByteArray-backed semantic-text foundation authored by GPT-6 Sol
  in `/Users/qobilidop/my/work/p4-spectec-lean-byte-text` has been integrated
  into the active branch above. Identifier strings remain separate.

## Completed indexed-list-update checkpoint

- Branch `m3b-indexed-updates`, based on print-hint PR #7 head `7c1bfec`.
- Implement the four root-index list updates in `Lvalue_write`, preserving
  base/replacement/index evaluation order and hard bounds errors.
  Focused implementation/test builds and `lake test` passed. The full
  `scripts/check.sh` exited 0 with no skipped gates, including the unchanged
  Nano generator check, both differential legs, quotations and printer
  fixtures. The census now has three callable failures and no relation
  `Prop` emission failures; emission alone is not full-P4 elaboration.
  Independent read-only review found no high/medium issues; its stale
  milestone wording finding is fixed. Report:
  `.agents/reviews/m3b-indexed-updates.md`. Tests elaborate synthetic
  list updates; the four full-P4 updates are emission-only evidence.
- Keep the two text updates rejected. Lean `String` contains a UTF-8
  validity proof; OCaml byte replacement can produce invalid UTF-8 even
  from valid inputs (`é`, replacing byte 0 with `X`). A character update
  or a failed UTF-8 conversion would not implement upstream semantics.
  A semantic-text representation inventory is underway before choosing
  that substrate change; identifier strings are a separate concern.
- Original isolated worktree:
  `/Users/qobilidop/my/work/p4-spectec-lean-fresh-state`, branch
  `m3b-fresh-state`, based on `7c1bfec`. Its explicit-state foundation
  and tests have been integrated into the active branch above, with no
  codegen/interpreter change. Failed branches and negation retain IDs.
- PR #6 passed remote CI and merged. PR #7 is independently reviewed,
  locally green and awaiting remote CI. No source changes to either
  published PR while subsequent work proceeds.

## Completed print-hint checkpoint

- Branch `m3b-print-hints`, based on subtype PR #6 head `b458a61`.
- PR #5 passed remote CI and merged as `4df4954`; PR #6 passed remote
  CI and merged as `351cf5d`, preserving its implementation/workflow
  commits. PR #7 is awaiting remote CI.
- Preserve full subtype applications through collection, bridge naming,
  signatures and placement. Two independent read-only audits found all
  thirteen failures are erased `continueResult<X>` arguments, not a need
  for covariant payload conversions. All 363 occurrences have equal
  payloads after substitution; all 129 checks use `MixopSC`.
- Upstream `runtime/type/sub.ml` substitutes both applications and
  requires equivalent payloads. Keep that fail-closed boundary. Add
  specialized names without changing Nano's monomorphic names.
- Implementation and compiled regression fixtures pass. All 567 full-P4
  bridge pairs emit text; Nano's 48 files are byte-identical. The full
  local `scripts/check.sh` exited 0; no gates skipped. Independent
  read-only review found no high/medium findings; report is
  `.agents/reviews/m3b-subtypes.md`. GPT-6 Sol authored focused tests;
  GPT-6 Astra handled implementation and independent semantics audits.
- Print-hint implementation is integrated: structural alternation port,
  strict JSON decoder, note-aware printer, literal generated tables,
  policy-compatibility checks, and spec-configured interpreter printing.
  All 190 hints validate. All 2,120 case origins and 567 subtype pairs
  preserve policies; actual variant/case notes are checked on CaseE nodes.
  The full table elaborated and matched decoded policies independently.
- Twelve fixtures observed directly from pinned upstream cover printer
  behavior, including unused unprintable arguments and Unicode. The
  first run exposed byte-escaping and ASCII-lowercasing bugs; fixed.
  Printer, builtin and interpreter outputs are now checked. The fixture
  revision must match upstream HEAD; selected printer failures must be
  `Fail.err`. Review findings are fixed, report in
  `.agents/reviews/m3b-print-hints.md`.
- The new full local gate passed (exit 0, no skipped gates), including
  the rebuilt proofs, 78 verdicts/48 outputs on both differential legs,
  342 quotations, twelve printer observations and the full-P4 census.
  An earlier run's shell exited 2 after its script was edited while
  running; the stable script passed `bash -n` and a fresh complete run.
  Generated Nano changes only its print builtin wrapper, now using
  checked printing and hard errors. The unchanged full export gets past
  print hints and rejects indexed path updates (expected probe exit 1).
- Next: six indexed updates at this pin, two text and four list updates.
  Preserve base/replacement/index evaluation order and upstream bounds.
  Stateful fresh IDs follow; investigate effects/backtracking before
  choosing a representation. Hinted-print refinement remains outside
  the current note-erasing relation's claims.

## M3A checkpoint

- Branch: `m3a-full-p4`, based on `384adea`.
- Delivered in PR #5 (`b5448c9` implementation, follow-up policies through
  `c5e96fb`). PR-default workflow, PR/commit-writing guidance and explicit
  AI disclosure are recorded in `AGENTS.md`; PR #5's description reflects
  them. Prior policy reviews and full local gates passed; see
  `.agents/reviews/pr-workflow.md`.
- User approved choosing merge strategy per PR, preserving meaningful
  commits by default. PR #5 should use a merge commit to retain its
  distinct implementation and workflow decisions. The AI disclosure also
  names the authoring agent and model in one sentence, per the user's
  brevity request: OpenAI Codex (GPT-6 Astra), verified via the session
  coauthor helper and existing trailers. Merge strategy stays out of the
  PR description. These policy-only changes passed independent review
  and the full local gate (exit 0); they change no repository settings.
  Remote CI must pass on the final PR revision before merging.
- Confirmed only the expected four patched upstream OCaml files were dirty.
- Read the resume documents, exporter, generator entry point, quotation
  emitter, fragment classifier and differential harness.
- Recursive export delivered: Nano-P4 is byte-identical; full P4 is
  98,387,720 bytes, 1,689 definitions. The exporter review independently
  reproduced both hashes. Full P4 contains 108 source files, with 80
  top-level declaration-region files in AL.
- Independent quotation check caught and fixed a type/function namespace
  collision (`id.al` incorrectly contained `$id`'s FuncDecD). Regenerated
  output changes only that quotation. Runtime comparison: all 342
  definitions match, exit 0; sensitivity and namespace tests: exit 0.
  Quotation review passed after explicit gate invocation was added.
- Census: four callable emission failures, one Prop-emission failure,
  thirteen subtype bridge failures; 138 functions syntactically eligible
  for refinement. Nano-P4 cross-check reproduces its 18 candidates with
  no emission failures. Type text estimates corrected after independent
  review; post-correction review and census check passed.
- Pipeline distinctions and remaining M3 phases are documented in
  `docs/design.md` section 3 and `.agents/notes/full-p4-reconnaissance.md`.
  Working reports and the machine census live under `.agents/notes/`,
  not in human-facing `docs/`, per the user's documentation policy.
- User approved preserving published history and compressing both spec
  snapshots: Nano 244,303 bytes; full P4 2,738,237 bytes. Raw JSON is
  ignored, checksum-verified and extracted by the gate. Full P4's 98 MB
  raw export was never committed. The gate rejects files over 5 MiB,
  checking the index as well as the working tree; no exceptions.
- Independent export, quotation and census reviews are in
  `.agents/reviews/`; all code findings fixed. Later storage and size-guard
  reviews passed. Documentation findings (remaining IL/AL contradictions)
  fixed; final documentation-placement review passed. Full gate after
  relocation: exit 0. Delivered in PR #5; remote CI is not part
  of this local evidence and must be checked before merging.
- M3B is now active under the user's authorization to complete all M3.
  The phased plan gives exit criteria and fidelity gaps.

## Current state

| Scope | Result | Revision |
|---|---|---|
| Design | agreed; revised for M1's findings (AL not IL as the export, fuel, module grouping, naming rule) | `main` |
| Upstream build | P4-SpecTec at the `gsoc-nano-spec` pin builds in the `upstream` Nix shell on nixpkgs' OCaml 5.5 with `scripts/build-upstream.sh` | `main` |
| Export | `elab -json`, `algo -json` and `nano parse -json` from `upstream/patches/0001-json-export.patch`; both spec AL snapshots stored as gzip plus raw SHA-256; 78 booted programs with upstream's verdicts under `exports/programs/nano-p4/` | M3A branch |
| Deep embedding | `P4SpecTec/Lang/Il/Ast.lean`, `Lang/Al/Ast.lean` and their JSON decoders mirror `lang/il/ast.ml`, `lang/al/ast.ml` at the same paths; `scripts/check-mirror.py` derives every mirrored pair from the paths and checks constructor lists and order | `main` |
| Prelude | `Runtime/Value/Value.lean` and `Interface/P4/Unparse.lean` mirror value construction, accessors, comparison and the printer; `Interface/Builtin/` ports every builtin file, with unit tests in `P4SpecTecTest/Builtins.lean` and the dispatcher on values `Call.lean`; `Prelude/` holds `ToValue`/`OfValue`, the `Eval` monad, numerics and iteration helpers | `main` |
| Interpreter | `Interp/InterpAl/{Backtrack,Ctx,Interp}.lean` mirror `interp/interp-al/` function by function, with fuel, over `Runtime/Value/Match.lean`, `Runtime/Type/{Typdef,Typ,Subst}.lean`, `Runtime/Dynamic/Var.lean`, `Runtime/DynamicAl/{Rel,Func}.lean`, `Lang/Hints/Input.lean`; `lake exe nano-p4-interp` (`P4SpecTecTest/Diff/NanoP4Interp/Main.lean`) runs `Program_ok` on the deep terms against the AL export | `main` |
| Codegen | `lake exe p4spectec-gen`: types, subtype bridges, functions, builtins, relations in both encodings, run-soundness theorems with audits, `Externs` class, per-file modules, `--check`/`--update`; every definition in `Eval := ExceptT Fail Option`, recursive groups by `partial_fixpoint`, no fuel | `main` |
| Tactics | `P4SpecTec/Tactic/RunSound.lean`: `run_sound` (symbolic execution of a run function against its `Prop` constructor) and `run_sound_group` (over `mutual_partial_correctness`, matching conjuncts by function); `Tactic/Refine.lean`: `refine_al`, lockstep execution of the interpreter port and the generated code (design 5.1); `Tactic/Audit.lean`: `#audit_axioms` | `main` |
| Rung 3 | `Refine/Value.lean` (`canon`, `Rel`, `eq_iff_canon`), `Refine/Quote.lean`, `Refine/Calc.lean` (`Refines`, `Holds`, `HoldsSpec`, exposure lemmas); `Codegen/Reify.lean` quotes every definition (`d.al`), `Codegen/Validate.lean` states the theorems and decides the fragment; `NanoP4Spec/Refinement.lean` holds `spec` (the quoted spec as a list) and the theorems: 18 of 153 definitions are in the fragment (18 functions, 0 relations: no builtin calls, casts, subtype checks, iteration bodies, iterated premises, type parameters, externs, indexing), all 18 theorems proved and audited; the rest are listed there with reasons | `main` |
| Generated | `NanoP4Spec/`: 27 modules named after the spec files (7 of the 34 spec files have none: their definitions all sit in recursive groups completed by a later file), then `Refinement/` (the quoted spec and one module per covered recursion group, 19 files) and `Refinement.lean`; with the root `NanoP4Spec.lean`, 48 modules, about 57k lines, building with `--wfail`; 161 types, 76 functions, 77 relations in both encodings (77 `Prop` inductives, 98 run-soundness theorems: 77 `R.run_sound` and 21 group theorems, each audited); 65 `partial_fixpoint` definitions; 18 refinement theorems and 2 determinism theorems, each audited | `main` |
| Rung 2 | `test/diff/run.py`, two legs: the generated `Program_ok.run` and the interpreter port each agree with the AL interpreter's verdict on 78 of 78 programs (48 pass, 30 fail: 32 positive, 21 negative, 25 exercises); for the 48 that pass, the output typing context equals upstream's value on both legs | `main` |
| Timing | `docs/timing-nano-p4.md`: 860.6 s of elaboration over 48 modules (per-module sum); the 18 refinement groups are 19 to 89 s each and build in parallel, so a full rebuild of `NanoP4Spec` takes 123 s wall on 16 cores (was about 13.5 min as one module). Only the `Refinement/` modules import the tactic, so a tactic edit rebuilds only them; a gate rerun with nothing changed takes 7 s | `main` |

## Last checked evidence

2026-09-25, M3A, `scripts/check.sh` in the default Nix shell: exit 0
after both gzip snapshots and the file-size guard were integrated. All
existing Lean builds/tests/axiom audits and generator checks pass; 78
verdicts and 48 output contexts agree on both differential legs; all 342
quotations match; the 1,689-definition census is current. Snapshot tests
(3) and size-guard test pass. No Lean gates skipped. Final rerun after
moving the work reports: exit 0. Diff whitespace check: exit 0.

Both export scripts rerun through the upstream Nix shell: exit 0;
archives/checksums byte-identical to staged versions. Upstream's `$sink`
missing-clauses warning is expected and recorded. No fresh upstream
build was needed; the existing executable at the unchanged pin was used.
Full-P4 generation, proofs and target simulation were not attempted as
completion gates: they remain blocked on the measured M3B–M3F work.

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
  quotation comparison is now covered by M3A's runtime gate;
  `Match.sub_`/`check'` answer `false` and
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
- Root-index list updates are supported; text, nested and sliced path
  updates remain rejected by codegen. Nano-P4 has none.
- `fresh_typeId` (a stateful builtin) has no port; not used by Nano-P4.
- `print` hints are supported under checked policy compatibility; a
  hinted-print refinement theorem still needs a stronger value/environment
  contract. The AL's `subcheck` is not
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
