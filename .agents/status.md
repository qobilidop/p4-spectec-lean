# Status

Active: full-P4 M3, resumed by the user on 2026-10-04 with autonomous authorization
(decisions, "Scope and product"). The Nano-P4 completion milestone stays closed at
`42ffad6` (2026-09-30); [`notes/nano-release.json`](notes/nano-release.json) records its
review and exact-revision CI for that tree digest.

## Where M3 stands

- M3B, first stage (pushed as `6e57dcb`, CI 37270348930 passed in 33 min, the first cold
  Linux build of `P4Spec`): the whole full-P4 export generates as the executable library
  `P4Spec` (ignored sources, pinned by `P4Spec.manifest.json`), builds with `--wfail`, and
  its 1,672 quotations match the export. No certificate of any kind exists for it.
  [Full-P4 overview](notes/full-p4/overview.md) has the measurements and what is missing.
- M3C, sweep: the generated library and the reference interpreter both agree with
  upstream on 1,266 of the 1,267 corpus candidates, for typing and instantiation
  (semantic outputs, exact fresh counters). One candidate is unobserved (above the 1 GiB
  case bound). [Corpus note](notes/full-p4/corpus.md) has the evidence and its limits.
- M3B's exit (logical relations with audited run-soundness), M3C's durable campaign,
  M3D, M3E and M3F are open.

## Verified state

Evidence for the working tree of the commit that adds the corpus sweep (the parent of the
commit recording CI, if any):

- Full gate: `nix develop -c /usr/bin/time -p scripts/check.sh` returned actual exit 0 in
  248.63 s, all 55 stages (`.artifacts/m3c/gate-3.log`); Nano completion 888 obligations,
  0 unresolved, review and release pending under the allowance as on every tree after
  `42ffad6`. Generated Nano output is byte-identical; `P4Spec` matches its manifest.
- Corpus sweep: `nix develop .#upstream -c python3 P4SpecTecTest/Oracle/P4/Corpus/sweep.py
  --upstream "$PWD/upstream/p4-spectec" --p4c "$PWD/.artifacts/p4c" --jobs 8` returned
  actual exit 0 in 1,228.0 s (`.artifacts/m3c/sweep-committed-2.log`): 1,266 of 1,267
  candidates `matched,matched` on both legs, one unobserved (`oversized`). The gate ran
  after a comment-only edit that followed the sweep; both worker executables still have
  the digests the sweep's summary records.
- Four-case replay, both legs: `P4SpecTecTest/Oracle/P4/Replay/replay.py` returned actual
  exit 0 (`.artifacts/m3c/replay-both-2.log`), before that same comment-only edit.
- Independent review: [full-P4 review](notes/full-p4/review.md), "Corpus sweep stage";
  one policy blocker and the should-fix items resolved before the commit, resolutions
  not re-reviewed.
- Remote CI: `6e57dcb` passed (run 37270348930, 33 min). Not yet run on this commit.
- Not run: the shard campaign (`shard.py`); no committed mutation suite for the sweep.

## Open threads and next step

1. Next: M3B's exit, starting with its measured bottleneck. A scratch probe
   ([overview](notes/full-p4/overview.md), "Executable generation") emitted logical
   relations for all 256 relations; `Cast_impl`'s module (99 helper inductives in one
   mutual block) does not elaborate in 13 minutes, and three emitter defects remain.
   Fix elaboration cost first, then the defects, then run-soundness for the 14 relations
   that need no recursive-group support, then the recursive motives.
2. M3C: extend the shard campaign to the generated worker and a larger bound for a
   durable, CLI-checked record; add rejected programs (negative regressions,
   `p4_16_errors`); commit a generated-code mutation suite for the sweep.
3. Generated `==` converts both operands to IL values (`valueEq`); on the largest programs
   the generated leg is about five times slower than the interpreter. Fix before any
   generated-leg target work (M3D); untried options are in the corpus note.
4. CI went from 9 to 33 minutes on the first cold `P4Spec` build; check the next run with a
   restored `.lake` cache before deciding whether the full-P4 build needs its own cache key.
5. A warm `lake build` log shows `PANIC at Lean.Meta.whnfEasyCases ... loose bvar` replayed
   as an info message from `NanoP4Spec.Refinement.Reverse.TableEntry_ok` (line 36). The
   module builds and its audits pass; the message predates this work and is unexplained.

## Repository state

M3 work is committed directly on `main`. Preserve local `n3-decl-load`
(`82fbe2e`, non-ancestor WIP), unrelated `docs/repository-review`, and the dirty old
`../p4-spectec-lean-replay` worktree. The expected four-file upstream exporter patch
remains applied; no source pins changed. `.artifacts/p4c` holds the pinned p4c samples.
