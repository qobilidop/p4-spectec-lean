# Bounded full-P4 Lean interpreter replay

Publication integration: `m3c-p4-replay-publish` on main `ea9533d` retains
the reviewed implementation unchanged. The ordinary gate now requires its
files, runs six offline contract tests and builds `p4-interp-replay`; real
upstream/p4c replay remains explicitly provisioned. Integrated full
`scripts/check.sh` exited 0 with no skips. Independent gate review passed;
the initial remote Gate `36209104840` passed on `94fd99e` in 4m53s.
Root independently reran the frozen end-to-end
replay with six relation matches and nine mutation rejections (exit 0).

After PR #19 merged as `c974c3d`, its bounded refinement changes merged
without source conflicts; only status documentation needed reconciliation.
Replay executable/driver/tests, Lake configuration and gate script remain
byte-identical to `94fd99e`. The repeated frozen full gate exited 0 with no
skips, including twelve oracle and six replay offline tests:

```sh
nix develop /Users/qobilidop/my/work/p4-spectec-lean --command /Users/qobilidop/my/work/p4-spectec-lean-replay-publish/scripts/check.sh
```

Final merged-head remote CI remains required before landing. No additional
real upstream replay was run for this source-unchanged reconciliation.

2026-09-25 checkpoint on `m3c-p4-interp-replay`, based on oracle head
`997d0ab`. This is an interpreter-fidelity slice, not a full corpus result,
generated-code result, or completion of M3C.

`test/p4-oracle/replay.py` regenerates the four committed oracle cases. It
checks the indexed P4-SpecTec gitlink, exact four-file export patch, rebuilt
source, clean nested p4c pin, typed observation envelope, fixture digests and
counts, and eight CLI verdicts before invoking Lean. It writes a temporary
compact JSON bundle and runs one `p4-interp-replay` process, so the 94 MiB
extracted `exports/p4.al.json` is parsed and initialized once. The bundle
is removed on exit; no duplicate corpus or output is committed.

`P4SpecTecTest/Diff/P4Interp/Main.lean` decodes the full typed boot value
through the IL decoder, sets AL guard=false and the fresh state to the
observed counter after boot, and checks both relations independently. Each
terminating run must have the exact final counter. Success checks output
arity and semantic `Runtime.Value.eq` for every output. The public upstream
AL API collapses internal hard errors and unmatches to its `unmatch` class,
so either Lean failure kind is accepted for that class; Lean fuel exhaustion
is reported separately and never accepted. Upstream abort is outside the
comparison and fails. The syntax fixture has no boot value and is explicitly
reported as syntax-only, with no Lean AL evaluation claim. Missing or
malformed values, outputs, counters or case identities fail closed.
Both ordinary and syntax-only envelopes enforce the AL/cache/determinism/
guard settings and signed 63-bit representability of all fresh counters;
the latter prevents a malformed post-boot seed from silently wrapping.

The initial replay exposed an actual `Program_inst` mismatch on positive
`issue-212.p4`: Lean's default `Extern.none` caused a hard error at
`init_objectState`, while the pinned upstream placeholder simulator returned
an `ExternV null` with type `objectState`. The replay config now mirrors the
two placeholder extern functions `init_objectState` and `init_archState`,
and rejects all other extern operations. This adapter belongs to the P4
replay runner, not the generic AL interpreter. With that exact boundary,
all three booted cases' six relation executions matched upstream; the
fourth syntax case remained syntax-only.

Focused verification in the pinned Nix shells:

- `lake build --wfail p4-interp-replay`: exit 0.
- `python3 test/p4-oracle/test_replay_contract.py`: exit 0, six tests.
- `python3 test/p4-oracle/replay.py --upstream <absolute pinned checkout>
  --p4c <absolute sparse checkout>`: exit 0; basic-routing, positive and
  negative cases matched, syntax-only case explicitly reported. The driver
  also runs Lean's `--sensitivity` mode: nine mutations were rejected,
  covering changed typed value, changed final counter, malformed output and
  boot, unsupported class, out-of-range seed, syntax mode and guard, and
  zero-fuel classification. The changed value/counter and configuration
  mutations assert the specific rejection reason, not just nonzero exit.

The full `scripts/check.sh` gate was not run in this isolated branch; root
owns gate integration. No push was made. The raw basic-routing observation
is over 500 MiB, so this bounded in-memory driver must be redesigned for
corpus-scale streaming/sharding rather than extrapolated to all p4c samples.
