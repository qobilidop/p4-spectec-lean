# Bounded shard recovery review

Independent read-only review by the state/target agent, 2026-09-25.
Reviewed all of `test/p4-corpus/shard.py`, its fourteen offline tests,
the compile-workspace helper diff, and the reused worker/observation
contracts relevant to recovery. No shard was launched by this review.

## Original finding and bounded fix

The changed `scripts/export-p4-oracle.py:compile_probe` rejects symlinks
in an explicit keyed workspace but does not reject hardlinked regular
files. A pre-existing `probe.ml` with `st_nlink > 1` passes the check and
`shutil.copyfile(PROBE, source)` overwrites its outside alias. Compiler
outputs in that same reusable directory have the analogous risk. The
new Store already rejects this situation for durable artifacts; apply
equivalent regular-file/single-link validation to keyed compiler entries,
or publish fresh exclusive temporary outputs safely. Add a hardlink
regression before closing this finding. The original finding was static;
this reviewer did not mutate an external alias to demonstrate it.

Root subsequently assigned the reviewer the bounded helper fix. The helper
now requires a real workspace directory and single-link regular entries
before copying source, then revalidates immediately before compiler writes.
The check applies to default PID and keyed directories. Sixteen shard tests
pass, including actual outside hardlink aliases for source/executable/object
destinations remaining unchanged, directory/symlink/FIFO rejection, and a
link injected after source copy being rejected before compiler invocation.
The existing seven v2 and twelve v1 contract tests also pass; all commands
ran in the pinned shell and returned exit 0.

Frozen source blobs are `fbabd5fabe16ffcf77729f2d604e4ee3229f81eb`
(compile helper) and `045382787a6456b481114df1486b0de28a4e2735`
(shard tests). These are author validations of the fix, **not independent
post-fix review**. The separate oracle agent is assigned independent review.
Checks protect against persisted cache redirections under the caller's
cooperative build lock, not hostile concurrent filesystem replacement by
another process with write access; the helper documents that boundary.

## Recovery and accounting assessment

- Quarantine moves the observation first, fsyncs that rename, and retains
  the current attempt marker until moving it last. A restart after the
  first move still identifies the interrupted attempt; the second recovery
  can complete the marker move without losing or duplicating the attempt.
  The injected between-moves regression exercises precisely that state.
- Only a valid terminal record, terminal-phase marker, increasing attempt
  number and validated bounded observation reference complete a case.
  Known temporary files are preserved separately, never decoded as successful
  observations. Malformed committed or final-name artifacts fail closed.
- Terminal failures are retained, not retried as successful cases. Fatal
  protocol/validation failures stop the selection; resource failures may
  continue but keep `okay=false`. Worker failure after the final reply
  creates a sticky run failure, preventing a completed semantic record
  from being mistaken for an overall passing run.
- Summaries derive their counts from validated records, distinguish
  unsupported/syntax cases from actual Lean execution, and retain the
  canonical inventory denominator and selected-case count separately.
- JSON duplicate keys/nonfinite constants, exact record key sets, strict
  integer counters/attempts, CLI contracts, byte bounds, source/identity
  hashes and symlink/hardlink-safe descriptor-relative artifact reads
  support the stated fail-closed boundary. Hashes are not authentication
  against coordinated malicious rewriting, as the design explicitly says.
- Run identity includes exact selection/settings, actual worker/probe
  binaries, linked archives and relevant source/pin hashes. The separately
  content-keyed compiler workspace is serialized under its build lock.

No semantic-accounting or recovery finding beyond the compiler-workspace
hardlink issue was identified in the original scope. Crash behavior is modeled by
injected exceptions and filesystem state transitions, not a power-cut test
or a proof of filesystem durability on every platform.

## Independent evidence

From `/Users/qobilidop/my/work/p4-spectec-lean-p4-corpus-replay`:

```
nix develop /Users/qobilidop/my/work/p4-spectec-lean-p4-corpus-replay \
  --command python3 \
  /Users/qobilidop/my/work/p4-spectec-lean-p4-corpus-replay/test/p4-corpus/test_shard.py
```

Original independent process exit 0; fourteen tests passed. The authorized
fix's author rerun of that command passes sixteen tests as recorded above.
No full gate, real shard, remote CI or whole-corpus completeness is claimed.
