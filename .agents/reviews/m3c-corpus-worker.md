# Bounded corpus-v2 worker review

Independent root source review and execution, 2026-09-25. Reviewed the v2
OCaml probe, Python envelope/driver/offline tests, Lean spec-once worker,
Lake target and documented boundary. The inventory has its separate review.
No blocking finding remains in this bounded pilot.

The probe observes the separate Type.Fresh counter before/after each
initialization/boot/evaluation phase without resetting it. Each upstream
relation is a fresh process. The worker rejects nonzero Type.Fresh state
as unsupported and retains exact builtin fresh-state comparisons. It
validates both result envelopes before replay, recursively checks typed
values and rejects duplicate JSON keys. Exhaustion, hard error, mismatch,
abort, syntax-only results and output/state disagreements are not silently
combined. Public upstream failure equivalence is labeled as such; the
actual Lean failure tag remains recorded.

The driver verifies pinned upstream/p4c inputs, the committed inventory and
checksum-extracted snapshot; its report includes worker/probe/source
identities and explicit byte/time/fuel/recycling bounds. These hashes
detect mismatched/corrupted artifacts, not malicious coordinated rewriting.
This tranche has no resume or shard execution logic. Resource usage is a
cumulative child-process high-water mark, not a per-case measurement.

Review found that worker initialization was outside the durable-report
try/finally lifecycle. A startup timeout/crash therefore lacked report.json.
The author moved initialization inside the guarded lifecycle and added a
forced-init-failure regression checking complete:false and the failure kind.

Independent checks, all in pinned Nix shells:

- Seven offline contract tests: exit 0, including that regression.
- Full bounded v2 pilot: exit 0; three original program cases each match
  both AL relations, one additional case is syntax-only, eight CLI checks,
  sixteen actual Lean mutation checks and successful post-mutation replay.
- Root report: ignored .artifacts/p4-corpus-pilot/98530/report.json.

The pilot rebuilds the worker and upstream probe rather than trusting a
preexisting binary. Published v1 code/fixtures remain unchanged. No
whole-corpus, generated-relation leg, packet target, resume correctness,
full local gate or remote CI claim follows from this review. Review the
small-shard/resume implementation independently before scaling.
