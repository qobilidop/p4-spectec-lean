# Independent probe-workspace hardlink follow-up

2026-09-25, read-only AI-agent review by Codex (GPT-6 Sol) of state_props'
narrow fix. Reviewer authored the earlier additive workspace-key option;
this review covers only the separately authored safety follow-up/regressions,
not independent approval of the whole helper/shard. Root owns that review.

Corpus worktree, branch `m3c-corpus-shards`, base `2c85f1b`:

- `scripts/export-p4-oracle.py` blob
  `fbabd5fabe16ffcf77729f2d604e4ee3229f81eb`.
- `test/p4-corpus/test_shard.py` blob
  `045382787a6456b481114df1486b0de28a4e2735`.

No findings within the stated persisted-cache/cooperative-lock boundary.
`lstat` rejects a symlink workspace; every existing child must be regular
with exactly one hard link before source copy and again before compilation.
This prevents persisted outside aliases of source, executable and compiler
outputs from being overwritten. The rebuild preceding validation does not
write the compile workspace. Keyed shard callers already hold the build lock;
the helper explicitly does not claim defense against hostile concurrent
replacement after validation. The default actual-PID recipe and compile
arguments remain unchanged apart from the same cache-safety validation.

Reviewer read the full helper diff and both new regression tests, then ran:

```sh
nix develop --command python3 test/p4-corpus/test_shard.py
nix develop --command python3 test/p4-corpus/test_contract.py
nix develop --command python3 test/p4-oracle/test_contract.py
```

All actual exits 0: sixteen, seven and twelve tests respectively. The
sixteen-test suite creates actual outside hardlink aliases for `probe.ml`,
`probe`, `.o`, `.cmi` and `.cmx`; each fails before compiler invocation and
leaves outside bytes unchanged. Directory/symlink/FIFO children and an
injected post-copy hardlink are rejected. Existing default/keyed recipe,
shard crash/recovery, terminal-record and path sensitivities remain green.
Both reviewed blob hashes were rechecked unchanged after execution.

No real shard was launched, no full gate/CI was run, no source file was
edited, and no commit/push was made by this reviewer. The earlier real
four-case/resume evidence predates this helper hash and is not relabelled
as final-revision validation; a fresh bounded check follows root approval.
