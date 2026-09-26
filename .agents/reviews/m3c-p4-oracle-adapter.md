# Independent full-P4 oracle adapter review

## Follow-up: four findings resolved

2026-09-25. Independently reviewed final revision
`997d0ab6b7b03ddc8ac3f452d181f4489f19c407`, including the complete diff
from `16a2d57413e74c48e266689a920349103e9cfade`, the resulting exporter and
checker, the unchanged OCaml probe and its pinned IL serialization types,
the twelve offline contract tests, and the updated boundary note.

No remaining correctness findings in this bounded upstream-oracle slice.
All four medium findings below are resolved at this revision:

- Provenance now requires the indexed gitlink, exact committed export
  patch and exact four-file working-tree status. Unexpected tracked or
  untracked source changes fail closed. Dune refreshes the CLI and its
  library dependency graph before linking the probe; a failed rebuild
  prevents linking. This uses the normal build system's freshness
  contract, not a claim of reproducible or adversary-resistant binaries.
- Digest normalization is restricted to source-region fields and rendered
  diagnostic regions. Semantic text and identifiers are not rewritten;
  arbitrary `ExternV` JSON is explicitly preserved. The tests distinguish
  literal checkout paths from placeholders, including nested semantic
  text, while preserving portability of genuine source locations.
- The fixed ordered four-case manifest and revision are mandatory; empty,
  missing, duplicated or reordered cases are rejected. Probe envelopes
  require the requested relation, AL mode, exact cache/det/guard booleans,
  zero initial counter, integer counter checkpoints and class-specific
  boot/output/diagnostic shapes before export or expectation update.
- CLI success requires exit 0 and exact success output; diagnostic failure
  requires exit 1, empty stdout and nonempty stderr. Signals and unexpected
  exits no longer count as semantic negatives.

The schema check is a transport-envelope check, not a replacement for a
recursive IL decoder or a typing proof: its typed-value checks inspect the
outer phrase/note/location structure and leave constructor contents to the
pinned OCaml serializer. Future Lean replay must decode those contents
strictly and apply an explicit semantic note/ID/hash policy. This does not
weaken the existing byte-digest comparison of all emitted contents.

### Independently rerun checks

Both commands below ran from
`/Users/qobilidop/my/work/p4-spectec-lean-p4-oracle-adapter` at the final
revision, with no implementation or fixture edits:

```sh
nix develop /Users/qobilidop/my/work/p4-spectec-lean --command python3 /Users/qobilidop/my/work/p4-spectec-lean-p4-oracle-adapter/test/p4-oracle/test_contract.py
```

Exit 0: all twelve offline tests passed, including corrupt expectation,
manifest, probe-envelope, source-patch/rebuild, normalization and CLI-crash
sensitivity checks.

```sh
nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean#upstream --command python3 /Users/qobilidop/my/work/p4-spectec-lean-p4-oracle-adapter/test/p4-oracle/check.py --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --p4c /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c
```

Exit 0: all four pinned cases matched for both independent relation
processes, and all eight CLI parity checks passed. The real check exercised
the exact source-patch guard and Dune refresh before the probe link.

```sh
nix develop /Users/qobilidop/my/work/p4-spectec-lean --command python3 /tmp/p4-oracle-followup-review.py
```

Exit 0: independent additional in-memory mutations rejected enabled guard
or det, Boolean/nonzero initial counters, absent successful boot, scalar
output values and a malformed diagnostic code. Nested semantic text path
changes retained distinct digests; similar-but-not-contained path prefixes
were preserved; CLI exits -9, 2 and 127 were rejected as negatives. This
temporary script is review evidence, not a new maintained test suite.

The only tracked change from this review is this report. No full repository
gate, remote CI, new standalone gzip export, whole-corpus run or Lean
differential replay was performed on this follow-up. Earlier deterministic
gzip evidence below pertains to the initial revision; the serialization
and compression paths are unchanged. Corpus size, exclusions and actual
Lean agreement remain the explicitly separate M3C obligations.

## Publication gate integration review

2026-09-25. The root agent independently reviewed the publication branch's
four-line `scripts/check.sh` integration: six required files and an
unconditional offline test call whose failure sets the gate's failure
flag. It found no issues and independently reran all twelve offline tests
and `bash -n scripts/check.sh`, both exit 0. This was AI-agent review, not
human approval. The existing adapter/test code is byte-identical to the
reviewed `997d0ab`; the publication branch does not enable a real upstream
oracle run or a corpus download in ordinary CI.

## Initial review (historical findings)

2026-09-25. Reviewed commit `16a2d57413e74c48e266689a920349103e9cfade`
in `/Users/qobilidop/my/work/p4-spectec-lean-p4-oracle-adapter`.
Read-only review by the executable-codegen agent. Only this report was
written in the worktree; no implementation, fixture, commit or push was
changed. Temporary sensitivity probes and compressed observations were
written under `/tmp`; the adapter produced its normal ignored probe builds.

## Findings

No high findings. Four medium findings need correction before integration.

### Medium: source pin metadata does not establish linked-code provenance

`scripts/export-p4-oracle.py:45–80` checks repository root and HEAD against
the indexed gitlink, then links existing `_build/default` archives without
checking source changes or refreshing the build. A checkout at the right
HEAD with a modified interpreter, builtin, spec or regression input still
passes; a stale build from an earlier source tree is linked unchanged.
`check_cli` similarly executes an existing `main.exe`. Agreement between
these two artifacts does not establish that either came from the recorded
pin. The export nevertheless records only `upstreamRevision` as provenance.

The current inspected upstream tree has only the four expected patched
files, and the real observations reproduced; this finding is about the
missing boundary, not evidence of a contaminated present observation.

Require pristine pinned sources plus exactly the supported export patch,
or another explicit verified source policy, and use the build system to
establish that all linked archives and the CLI are current for those
sources. Reject unexpected tracked/untracked source or spec changes
without altering the user's tree. Add sensitivity tests for a wrong pin,
unexpected dirty source and a failed/stale build path.

### Medium: digest normalization can erase semantic text differences

`test/p4-oracle/check.py:42–48` serializes the complete value, then replaces
checkout path strings globally. That replacement applies to `TextV`
payloads and identifiers as well as source regions. For the actual p4c
root, these distinct values have the same digest:

```text
["TextV", "/…/.artifacts/p4c/semantic.p4"]
["TextV", "$P4C/semantic.p4"]
```

This was reproduced directly against `digest`; the lists differed but
their SHA-256 results were equal. The note's claim that normalization
preserves payloads is therefore too strong. A semantic-output mutation
can escape the fixture check without a cryptographic collision.

Normalize only explicitly identified source-location fields, with a
documented diagnostic-path policy. Preserve semantic text and identifier
bytes, even when they resemble a checkout path or placeholder. Add a
mutation test which requires these two text payloads to hash differently.

### Medium: the observation and fixture contracts fail open

`check.py:98–104` accepts a missing `upstreamRevision` by defaulting to the
current revision, and executes whatever `cases` remain. Replacing the
fixture with `{"cases": []}` returns normally and runs zero comparisons.
Removing or duplicating a case likewise has no manifest check.

`export-p4-oracle.py:84–96` requires only matching `boot` fields from the
two JSON objects. Supplying `{"boot": null}` twice returns relation
objects `{}` without rejection. The declared relation, AL mode and
cache/det/guard settings are not validated; `summarize` ignores those
fields, so mode/configuration changes need not be caught when the bounded
outputs happen to agree. Result classes and class-specific output versus
diagnostic shapes are not validated before `--update` or export.

Both the empty-fixture acceptance and malformed-observation acceptance
were reproduced with in-memory subprocess/fixture stubs against the
unmodified functions. Require the fixed four-case manifest, revision and
field types; validate both probe envelopes and their exact requested
relation/configuration; require the appropriate boot/output/diagnostic
shape for each recognized class. Reject invalid data before writing a
runtime artifact or updating an expectation. Add bounded corrupt-fixture
and malformed-probe sensitivity tests.

### Medium: CLI crashes count as expected negative verdicts

`check.py:78–81` defines failure as anything other than exit 0 plus
`passed\n`. A CLI killed by a signal, an unexpected OCaml exception or an
unrecognized output is therefore accepted for a recorded negative case.
An in-memory `CompletedProcess` with exit `-9`, empty stdout and `killed`
stderr passed `check_cli` for an expected `unmatch` result.

Pinned `p4spec/bin/cli_error.ml` specifies exit 1 for a diagnostic failure;
`main.ml:283–288` prints `passed\n` only on success. Validate the known
success and diagnostic-failure exit/output contracts and reject signals,
unexpected exit codes and malformed success output. Do not collapse
process failure into semantic verdict parity.

## Positive checks and replay limits

- The OCaml adapter follows the pinned CLI's actual AL route:
  `backend-boot/build.ml:15–20` uses `Pass.algo`, and
  `p4spectec.ml:50–52` delegates to `Backend_sim.Build.build`.
  CLI defaults at `main.ml:219–258` are cache on, deterministic and guard
  checks off. The probe requests those settings explicitly.
- It uses the placeholder simulator, as the architecture-free `run -al`
  CLI does. This is not target execution or a packet oracle.
- Each relation runs in a new process, preventing the first relation's
  fresh counter from becoming the second's initial counter. Both complete
  boot JSON trees are compared. `Program_inst` receives the boot program,
  not the output of a previous typing call.
- `eval_rel` clears interpreter caches before invocation. The CLI's
  `eval_program` clears them before parsing, then invokes the same relation
  dispatch; fresh process initialization leaves the adapter's caches empty
  during parsing too. The no-handler hook difference introduces no observed
  semantic effect in these runs.
- Typed values use upstream's actual `Il.value_to_yojson`. Raw runtime
  observations preserve outputs, notes, identifiers and counters; the
  payload-normalization finding concerns only the checked digest path.
  Successful subprocess output is decoded strictly; unexpected probe
  exceptions propagate rather than becoming an exclusion or pass.
- Public AL `Err` and `Unmatch` both become `Run.Unmatch` at
  `interp.ml:1666–1673`. The adapter and note correctly avoid claiming
  internal failure-kind fidelity. The Lean replay must retain that explicit
  observable quotient while separately checking its stronger failure laws.
- Lean replay should initialize each `evalRelState` session from the
  recorded `counterAfterBoot`, retain exact `counterAfter` on terminating
  results, and compare semantic values through an explicit note/ID/hash
  policy. Upstream raw typed JSON digests are not directly a shallow Lean
  value equality. Cache-enabled upstream behavior still needs actual
  differential evidence against cache-free Lean execution.
- No exclusions are silently applied here. The four deliberately selected
  inputs are a regression set, not a corpus denominator; the note states
  that limitation. Broad source counts, exclusions and Lean replay remain
  separate M3C work.
- Deterministic gzip uses empty filename, mtime 0 and atomic replacement.
  Two independent exports of positive `issue-212.p4` produced identical
  31,775-byte gzip files (906,411 decompressed bytes), SHA-256
  `8104dd23930acfe488916890b45cef74c0854f274cb564f5823be9b91ebdec5c`.
  Both relation sessions recorded counters 0/0/0. Broad artifacts remain
  ignored, consistent with the storage policy; corpus-scale peak memory
  and retained scratch builds remain an explicitly documented limit.

## Commands and evidence

The real four-case check ran in the pinned upstream Nix shell:

```sh
nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean#upstream --command python3 /Users/qobilidop/my/work/p4-spectec-lean-p4-oracle-adapter/test/p4-oracle/check.py --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --p4c /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c
```

Exit 0: basic routing, positive regression, negative regression and syntax
failure all matched both relation observations and the current CLI parity
test. The bounded in-memory sensitivity script exited 0 after asserting
all four reproduced validation failures described above. Two standalone
positive-regression exports exited 0; byte comparison, strict JSON decode,
gzip mtime and size checks exited 0. No full repository gate, remote CI,
whole-corpus run or Lean differential run was performed for this review.

The original author has been informed of all four findings and is adding
offline contract tests; changes after `16a2d57` require follow-up review.
