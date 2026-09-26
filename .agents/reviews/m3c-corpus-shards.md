# Independent bounded corpus shard review

Root review, 2026-09-25. Read the complete shard runner, offline tests and
compile-workspace helper change. Re-read the final worker-close/resource
accounting changes and hardlink follow-up. No remaining findings within
the documented cooperative-lock, persisted-cache boundary.

The run identity fixes the inventory, selection, roots, sources, toolchain,
actual executables, linked archive hashes, configuration and resource bounds.
Only validated terminal records skip replay. Interrupted artifacts retain
their attempt history and are quarantined before retry; corrupt final
artifacts fail closed. The earlier marker-first quarantine crash window is
fixed by artifact-first, fsynced movement with the marker retained until
last. The injected between-moves regression exercises the corrected order.

Semantic success cannot absorb worker startup/final-exit failures, timeout,
unsupported Type.Fresh, or malformed artifact outcomes. A final worker exit
failure persists a run failure even after its last successful reply. Unknown
byte counts are null rather than invented zeros. The RSS observation is a
cumulative terminated-child high-water mark, excludes a still-live worker
at case commit, and is neither a per-case measurement nor a hard memory cap.

The bounded compile helper now rejects persisted symlink, special-file and
hardlink destinations before copying source and before compiler writes.
Independent follow-up review is recorded separately. This is not protection
against a hostile process concurrently replacing the directory under the
cooperative lock. Hashes likewise do not authenticate malicious coordinated
rewrites of the cache.

Root independently ran the final sixteen offline shard tests in the pinned
shell, actual exit 0. Read the narrow CI addition: two required source paths
and the unconditional offline suite propagate failure; the gate does not
launch a real shard or fetch the corpus. Existing v1/v2 APIs remain intact;
the optional compiler workspace key preserves the default PID convention.

The earlier four-case pilot and exact resume are bounded evidence only.
The final helper revision changes provenance; its four-case pilot and exact
resume both exit 0 at identity `901d53d9`, with terminal-record hashes
unchanged and all attempts one. Root independently reran the exact resume
under the pinned upstream shell, actual exit 0 recorded in ignored
`.artifacts/root-shard-resume.exit`. Full local gate and final-head remote
CI remain separate obligations. No whole-corpus or generated-leg comparison
is established by this review.
