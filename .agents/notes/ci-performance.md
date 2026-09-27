# Build, test and CI performance

Durable implementation and review evidence, 2026-09-26. The authorized build/test/CI
optimization is complete through `4cba852`; retained for review provenance and
measurement limits. Public results live in
[the performance snapshot](../../docs/performance/build-test-ci-2026-09-26.md).
All certification obligations, proof statements, axioms, corpus cases and failure
classifications were preserved. Nano feature work and broader full-P4 campaigns
remain paused.

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
balanced ABBA native executions (after, before, before, after) took
14.951s, 84.466s, 83.104s and 14.179s. Every run checked the same committed
1689-definition report successfully. The old binary was retained before source
edits; SHA-256 `f4636d50f63487a44a905ead779eeb12ed2bbd3a0ab4d2c2a88bda577ea3754c`.
Raw runs and binary identities are ignored under
`.artifacts/ci-performance/census-before-after.json`. Proof profiling overlapped
part of this work; the balanced comparison controls machine/input but is not
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


## Packet fixture mutation copying

All eleven contract tests and twelve existing field mutations remain. Replacing
an immediate field now copies only the dictionaries/lists along that path,
rather than deep-copying the entire large fixture. Validation reads shared
unchanged payloads; teardown revalidates the source fixture after each test.
Paths must identify existing fields. No production oracle code changed.

Author Sol measured an initial trial at 3.797s to 0.420s wall time. Root requested
removal of an extra implementation-level helper test; the final original eleven
tests passed in 0.287s as reported by unittest (not wall time). All existing
assertions remain. Raw timing and original source are under ignored
`.artifacts/packet-contract-path-copy-*` and `packet-contract-before-path-copy.py`.

Independent root read-only review checked mutation paths, guards and the
read-only nature of fixture.validate/typed_value; no findings. Scoped final
diff SHA-256 against `60d74c9`: `e2d4d1c95b44796b498c3227eb7d1ded2285a6c18cd203e49ad0e29e847ba32d`.
The next combined full gate remains required before publication.


## Concurrent independent mutations

The complete baseline still runs first. Only after it passes, run the three
independent mutants with three bounded worker threads. Ordered executor results
preserve the JSON report; validators, nonces, scratch directories and separate
60s/300s phase timeouts are unchanged. Any worker execution failure rejects the
runner; shutdown waits for other bounded workers.

Author Sol measured the original serial runner at 24.349s and concurrent runner
at 16.978s, both exit 0 with byte-identical JSON, before the byte-access optimization.
The eleven focused runner contracts passed; two added orchestration tests force
reverse completion order and reject HarnessError/OSError from mutant workers.
The existing test still requires baseline failure to prevent all mutants.

Independent read-only Sol review (`enforce_library_layers`, distinct from author
`organize_lean_tests`) found no issues. Two-file diff against `60d74c9` SHA-256:
`2a4183e8a5b1532d41e95e5426f159f58a178c0add029f3f31a00bcf767d900c`.
Root also inspected ordering, per-case isolation and failure propagation. Raw
comparison artifacts: `.artifacts/field-update-concurrency-*`.
Full combined gate and final measurements follow the JSON optimization.


## Packed JSON byte access

After graph optimization, native census sampling found all 2129 active-thread
samples during seconds 5–8 in `Yojson.validateEscapes`, predominantly materializing
and freeing boxed arrays. Its seven `bytes.data[index]?` accesses converted the
entire packed buffer. Replace them with `bytes[index]?`, whose pinned Lean
logical definition has exactly the same bound check and byte result. Unicode
validation order, fuel, branch choices and diagnostic strings are unchanged.

Independent read-only Astra review (`review_oracle_refactor`, not author) checked
all seven accesses against Lean 4.34.1 definitions and existing Unicode/transport
coverage. No findings; diff SHA-256 against `c795c26`:
`fee9ca8cd82cf765bd1634664d3bbed0e1411ea40822897fce13dfda3dcbf20a`.
Focused warning-free census/Decode build passed, session 73330. The existing tests
retain invalid UTF-8, malformed/unpaired/valid surrogate and escaped-backslash
cases; full replay checks both transport legs.

Isolated native ABBA comparison (after,before,before,after): 5.331s, 14.245s, 12.964s,
3.837s, all exit 0 checking the identical committed census. The previous graph
binary SHA-256 is `436c836c3ab0742f3f7c63262a43436981ee51eb41b6dc5e5d5968dc35cce21b`;
complete binary identities and runs are in ignored
`.artifacts/ci-performance/census-byte-access-before-after.json`. These short
samples show variability; report the range rather than a precise universal factor.

## Second batch validation

Full local gate 81923 passed with actual exit 0 and no skips. All 44 stages passed
on frozen executable inputs including StateRefine, fixture copying, concurrent
mutations and byte access. Certificates and examples rebuilt; unit tests 10s,
packet contracts under 1s, concurrent mutations 18s and full-P4 census 4s. All corpus
cases, generated sources, axiom audits and 888/95/793 accounting remain unchanged.
Log: `.artifacts/ci-performance/second-batch-gate.log`.

Earlier published `19195eb` passed exact-head CI 36284518064. Its gate ran
01:07:21–01:15:32 UTC (8m11s); workflow elapsed 9m21s, with prior cache restored.
The three expensive proof jobs took 50s/33s/21s, versus 281s/243s/194s in the older
ordering run. This is observational CI evidence with different invalidation
patterns, not a controlled clean-build benchmark. The replay stage still spent
140s, mostly hidden executable builds; investigate unnecessary native tactic
imports next. No remote failures are known.


## Native dependency ownership

Runtime replay now imports its actual typing-definition owner. Quoted Spec
modules use Prelude/Quote support, while certificate modules retain their exact
prior proof imports. The coverage launcher loads full NanoP4Spec in its child
frontend; Lake `needs = ["NanoP4Spec"]` builds all model/certificate leanArts first
without adding them to the launcher's native link closure. No theorem checker,
argument escaping, exit propagation, generated body or proof statement changed.
Only three imports changed in the generated Spec module; all other generated
files remain byte-identical after regeneration.

Independent Sol cross-reviews exclude each author's own files:
- `enforce_library_layers` reviewed generator/Spec diff against `b916f9c`,
  SHA-256 `79e794fa4a6a863ed2fa0ce81c5a1a9f34d06d61ee44428a68287f8b1a7b4929`.
  Minimal imports supply the referenced namespaces/types; no introduced finding.
- `organize_lean_tests` reviewed launcher/Lake/replay diff against `b916f9c`,
  SHA-256 `4ed8b1f002a6e42341a162f1c432a40e832508bcbd166f3415e0d1b3e1c358ea`.
  Pinned Lake's extraDep/needs and default leanArts implementation preserve fresh
  standalone coverage execution; all claims remain in the child environment.

The initial full gate 95154 failed because the downstream Environment example
had received HoldsSpec indirectly through Spec/Calc. Root added its explicit
owning-module import. Independent Sol addendum reviewed generator/Spec/example
scope, SHA-256 `590ac71a5859de1d0bf6f5cbd8007f2964d58942246575fbfb4a58dc9d6068d1`;
no remaining finding. Example build 23762 then passed. A separate pre-existing
review observation: empty-spec planning appears to emit a leading cons token;
this scope did not test or expand empty-spec support. Revisit with generator
empty-input coverage, not as an import-cleanup regression.

Native build 24303 passed. Actual linker response files show all five refinement
tactic objects removed from each of nano-p4-run, check-coverage, check-quotes and
check-nano-packet. Lake's no-build transImports query shrinks replay 107→50 and
coverage 129→38 imported modules. These are dependency counts, not timing claims.
Before/after response files and JSON summaries are under
`.artifacts/ci-performance/`. Root moved the compiled Nano root aside, confirmed
it absent, then standalone `lake exe check-coverage` rebuilt it byte-identically
and checked all 97 claims successfully (session 63559). This checks the explicit
prerequisite instead of relying on an already-present root artifact.

Full corrected gate 5946 passed, actual exit 0, no skips, 51.524s wall time with
warm artifacts. All 44 stages passed; raw log/measurement:
`.artifacts/ci-performance/native-import-gate-fixed.{log,json}`. The earlier
published byte-access batch `b916f9c` also passed exact-head CI 36285243949.


## Final checkpoint and discarded experiment

Exact-head CI 36285795982 for `4cba852` succeeded. Its gate took 4m02s and workflow
5m14s; certificates, examples and affected executables rebuilt. These are observed
runner timings with different invalidation from earlier runs, not a controlled
clean-build comparison. Raw log: `.artifacts/ci-performance/native-import-remote.log`.

Astra instrumented two repeated-normalization sites in Forward. All 177 repeated
passes made no progress across the three original heavy proofs, which passed with
their existing axiom audits. Removing those passes yielded only 16.601→16.261s,
10.373→9.982s and 9.039→8.705s. The bounded pair's 2–4% gain was comparable to run
variation, so the experiment was discarded. Forward was restored byte-for-byte
to `4cba852`; `lake build --wfail P4SpecTec.Tactic.Refine` exited 0 after restoration.
No instrumentation or experimental tactic change is committed. Revisit only with
stronger measurements; ignored evidence is in `.artifacts/proof-repeat-study/`.

Independent read-only Sol `organize_lean_tests` reviewed the public snapshot and
Performance link against retained logs/JSON at `4cba852`. Draft snapshot SHA-256
`3abbc009cf2f600a75d2241997ad53f9168ed4acbc14be9499932653589d1c2a`, guide SHA-256
`1933c7f22340876ec403835e84e8a3696e7ab604a7626009ed200c6ba47fde48`.
Two minor findings were resolved: name ABBA accurately, and identify `29ddf22` as
the retained baseline binary's build revision (compiler unchanged through `2743c3b`).
Reviewer checked the three original proof timings against retained author evidence,
without rerunning them. All later changes are evidence/checkpoint prose; executable
validation remains full gate 5946, actual exit 0, all 44 stages, no skips.

The final four-file evidence/status addendum received independent Sol read-only
review at `4cba852`, with no findings. Ordered path+NUL+bytes fingerprint
(`docs/performance.md`, its new snapshot, status, this note):
`91bb28cf81679a91002f0609301b15a7f04ba4c9e35caab62883469b0dafb84e`.
The reviewer independently checked the remote gate log and discarded-study JSON;
workflow elapsed used the integrator's queried CI metadata, and restoration-build
success remained author evidence. This review record is added afterward.
Final text hygiene, staged whitespace, tracked file-size and local Markdown link
target checks passed (12 local targets; no public link into `.agents/`).
