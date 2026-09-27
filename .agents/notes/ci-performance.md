# Build, test and CI performance

Active authorized optimization, 2026-09-26. The user requested diagnosis, approved
implementation and then granted roughly three hours of autonomous optimization
(until approximately 2026-09-27 03:41 UTC). Keep all certification obligations,
proof statements, axioms, corpus cases and failure classifications intact. Nano
feature implementation and broader full-P4 campaigns remain paused.

## Baseline evidence

GitHub timestamped logs, not a controlled same-machine benchmark:

| Revision/run | Workflow elapsed | Gate elapsed | Cache state |
|---|---:|---:|---|
| `5687b0d` / 36277971665 | 6m15s | 4m59s | prior Lake cache restored; no Nano proofs rebuilt |
| `ad1ac33` / 36280484313 | 22m44s | 21m33s | prior cache restored; changed proof support rebuilt |
| `29ddf22` / 36281893597 | 21m02s | 19m56s | ad1ac33 cache restored; Prelude order invalidated dependents |

All three runs succeeded. Workflow elapsed is created-to-updated time; gate
elapsed is its logged boundaries. Main Lean rebuilding consumed about 11 minutes
in each slow run. The latest log's expensive proof jobs include
split_dataplane_parameters (281s), directionless_trailing_p (243s), and
update_fieldValue (194s); concurrent job durations are not additive wall time.
Remote certificates built once, not twice. Nine oracle Main modules built twice.

On the warm baseline, adjacent log boundaries attribute about 109s to the
field-update mutation runner and 145s to the full-P4 census; on the ordering
run they are 177s and 137s respectively. These include small process/startup
boundaries, not isolated profiler measurements. Cache restoration succeeded;
cache setup is not the dominant source of the twenty-minute gates.

Sol's local-log inventory found duplicate certificate work in the ordering gate.
Root edited Prelude whitespace after that local run began, a confounder which
can invalidate build traces. Do not infer a persistent Lake/proof duplication
bug from that run. Avoid changing executable inputs during measured validation.

## Workstreams

1. Root owns integration, gate evidence and census profiling. Sol
   `organize_lean_tests` owns test-library/executable ownership; Sol
   `enforce_library_layers` owns stage timing. Cross-review excludes authorship.
2. Profile the census before optimizing. Existing native-executable sampling
   found repeated `Funcs.monotonicityConsumers` whole-definition traversals in
   recursive relation emission. Inspect equivalent reachability calculations;
   require byte-identical Nano generation and full-P4 census results.
3. Astra `review_oracle_refactor` profiles expensive actual generated proofs and
   may optimize existing refinement tactics. Do not hand-edit generated sources
   or weaken statements/audits. Use matching before/after measurements.
4. Profile mutation replay after the first checkpoint; preserve baseline proof,
   intended diagnostic boundaries, isolated scratch inputs and failure handling.

## First checkpoint (`2743c3b`, local and remote pass)

Removed the test library's recursive globs, using Lake's canonical root default.
Actual module query contains the root and all 25 unit-test imports; oracle roots
retain their executable configurations. All 15 executable declarations are
unchanged; the gate explicitly builds all 11 oracle executables. Author's warm
`lake test` and oracle build both exited 0 with zero Built entries, compared to
nine duplicated Main builds in old warm logs. Library boundary check passed.

Gate timing adds 44 named start/end stages with integer elapsed seconds and
actual command exits. Author compared complete command traces against the prior
script for success, collected failure, immediate snapshot failure, missing-Lake
rejection and explicit skip: all order/exit behavior matched. Syntax and whitespace
checks passed.

Independent read-only cross-review, no findings:
- Sol `enforce_library_layers` reviewed only Lake ownership, excluding its own
  gate edits; diff SHA-256 `098b7734347118f26035cabae8b78769e696061f13d11cd1ee593ce9ec227617`.
- Sol `organize_lean_tests` reviewed gate timing, excluding its own Lake edits;
  diff SHA-256 `0c366970e8c82c55ff992a15226e1a0af0aba73bb7cc4dc4cbee65b7c631785f`.
  Independent helper probes checked success, failure17, scoped cwd and missing
  root; the five full stub traces are author evidence, not reviewer execution.
Both reviews used `7ebf4ea` as baseline. Root reviewed the integrated changes.

Full local gate `nix develop -c bash scripts/check.sh` passed with actual exit 0
(session 21389, no skips); `.artifacts/ci-stage-ownership-gate.log`. All 44 stage
results are zero; unit/oracle ownership, fresh generated output, both 78-program
replay legs and unchanged 888/95/793 completion accounting pass together. Proof
profiling ran concurrently for part of this validation, so it is not a controlled
wall-clock comparison. Final review/checkpoint prose receives text/whitespace
checks; CI is asynchronous for the resulting publication.


Its exact-head CI 36283667100 succeeded. All 44 stages passed; warm library,
unit-test and executable builds reported zero seconds, with no duplicate Main
builds. The remote mutation stage took 185s and census 140s. The gate ran from
00:50:22 to 00:56:33 UTC on 2026-09-27; these are observed runner timings, not
controlled hardware comparisons.

## Census reachability optimization (`859e8aa`)

Native sampling of the existing binary found `Funcs.monotonicityConsumers` in
2396 of 2541 active-thread samples in the middle three-second window. It repeatedly
walked every definition's AST while expanding reachability, then repeated that
closure for candidate consumers. The replacement constructs forward/reverse
adjacency once per invocation and walks each reachable graph once. Source-order
filtering and callback gating are unchanged; repeated definition names union
their outgoing edges and retain repeated output entries.

On Apple M3 Max, 16 logical CPUs, 64 GiB RAM, arm64 Darwin and Lean 4.34.1,
alternating native executions (after, before, before, after) took
14.951s, 84.466s, 83.104s and 14.179s. Every run checked the same committed
1689-definition report successfully. The old binary was retained before source
edits; SHA-256 `f4636d50f63487a44a905ead779eeb12ed2bbd3a0ab4d2c2a88bda577ea3754c`.
Raw runs and binary identities are ignored under
`.artifacts/ci-performance/census-before-after.json`. Proof profiling overlapped
part of this work; the alternating comparison controls machine/input but is not
an isolated laboratory benchmark. Native sampling itself is not a timing sample.

Focused builds passed (sessions 97004 and 32667), as did byte-identical Nano
generation `--check` (3079). A bounded independent list-saturation reference checks
all 512 directed three-node graphs; additional fixtures check missing vertices,
duplicate edges/definitions, callback gating, source order and SCC exclusion.

Independent read-only Sol review (`enforce_library_layers`) found no correctness
or ordering defect. The initial review suggested a duplicate-definition fixture;
it was added and passed, and the reviewer confirmed that resolution. Reviewed
four-path diff against `2743c3b` SHA-256
`d8e6cb68c1cdc676bc2d80b6debe5c6bd3c8d75721064ee2796404c27513a2ed`.
The subsequent tactic-test root import is outside that snapshot. Reviewer did
not execute builds; the checks above are integrator evidence.

## Integration validation

The combined census/tactic working tree passed the full local gate, session
63747, actual exit 0, no skips. All 44 stages passed; generated outputs and
committed census/completion inventories are unchanged. The census stage took
13s and mutation replay 24s (previous local stage measurements 83s and 88s).
This run rebuilt certificates, unit tests and downstream examples, so its total
is not a warm-gate comparison. Log: `.artifacts/ci-census-tactic-gate.log`.
The two independently reviewed source changes will be committed separately and
published together at the fully validated combined revision.

## Refinement rule preparation (`19195eb`)

Astra `review_oracle_refactor` profiled original generated proof files. More than
80% of elapsed time was spent normalizing goals/hypotheses; the large fixed global
simp set was elaborated at every normalization. The implementation prepares those
rules once per `refine_al` call, freshly elaborates local facts per goal and leaves
simplification results uncached. Changed rule lists fall back to ordinary simp
elaboration, as does the existing unprepared StateRefine path. Preparation rejects
local or unresolved rule expressions.

Matching original-file `lake env lean -Drefine_al.trace=true` runs, in seconds:

| Generated certificate | Before | After |
|---|---:|---:|
| split_dataplane_parameters | 63.367 | 18.890 |
| directionless_trailing_p | 55.060 | 11.323 |
| update_fieldValue | 45.640 | 10.112 |

All three original proofs and their existing axiom audits passed; no generated
file changed. These are serial direct Lean runs with dependency artifacts already
built, not clean build or kernel-only measurements. Author checks also passed for
tactic/StateRefine warning-free builds, StateForward tests and five new regressions:
changed rule lists, opposing sibling facts, hypothesis self-exclusion, local-rule
rejection and no-progress rollback. Root wires the regression module into lake test.

Root's independent review compares the implementation against pinned Lean's
`mkSimpContext`, `elabSimpArgs`, `simpLocation` and `evalSimp`. It found a diagnostic
fidelity issue: traced hypothesis normalization omitted its location. The author
corrected it and added an exact trace regression; proof semantics were unaffected.
Root re-reviewed the fix: no outstanding findings. Six focused regressions now
pass. Final three-file content digest (ordered path + NUL + bytes, SHA-256):
`6bbe5dec5f49e799d5d260944677cfbb79c2a5de545e6a8ca8c787ebe5c3f6d1`. Review is independent of authoring; full-gate
validation remains the integrator's next check.


Integration gate 63747 above covers the final tactic code including its trace
correction and all six regressions. All 18 forward certificates rebuilt with
unchanged axiom audits. Library/certificate build 26s, unit tests 36s and downstream
examples 27s were followed by passing runtime replay, mutations and census.
The mutation stage fell from 88s to 24s locally without any runner change.
StateForward's unprepared stateful path still takes 34s in the unit-test build;
preparing its completed global rules is the next measured experiment.


## Stateful refinement rule preparation

After the shared mechanism passed, prepare StateRefine's rule set after adding
its state-specific equations. This is a one-line change in `prove`; the existing
StateForward fixture and all semantic contracts are unchanged. Isolated direct
full-file Lean runs took 29.266s before and 8.065s after (3.63x), both exit 0 with no
messages. Warning-free tactic build also passed. Author Astra retained exact
commands and file hashes in `.artifacts/proof-perf-state-{baseline,cached}.json`.

Independent read-only Sol review (`enforce_library_layers`) found no issue with
preparation placement or fresh local facts. Reviewed diff against `19195eb`:
SHA-256 `5b859dc41590a3d3376c2a03098350d248d32839aec9ba2c088b71f407d4941f`.
Root also inspected the one-line change and unchanged stateful fixture. Existing
six normalization regressions cover the shared mechanism; the stateful fixture
covers calls, branches, errors, mismatches and retained state. Full integration
gate is required before publishing this next batch.
