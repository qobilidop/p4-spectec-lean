# Status

Active: full-P4 M3, resumed by the user on 2026-10-04 with autonomous authorization
(decisions, "Scope and product"). The Nano-P4 completion milestone stays closed at
`42ffad6` (2026-09-30); [`notes/nano-release.json`](notes/nano-release.json) records its
review and exact-revision CI for that tree digest.

## Where M3 stands

- M3B, first stage: the whole full-P4 export generates as the executable library `P4Spec`
  (ignored sources, pinned by `P4Spec.manifest.json`), builds with `--wfail`, and its 1,672
  quotations match the export. No certificate of any kind exists for it.
  [Full-P4 overview](notes/full-p4/overview.md) has the measurements and what is missing.
- M3C, first evidence: the generated library and the reference interpreter both agree
  with upstream on the three evaluated pinned programs, for typing and instantiation: two
  pass with upstream's outputs and exact fresh counters, one is rejected by all three
  (upstream reports no failure kind, so any Lean failure matches). The corpus campaign (1,267 candidates) has not been run on either
  leg in this tree.
- M3B's exit (logical relations with audited run-soundness), M3D, M3E and M3F are open.

## Verified state

- Full gate on the working tree of the commit introducing `P4Spec`, after the review
  resolutions: `nix develop -c /usr/bin/time -p scripts/check.sh` returned actual exit 0 in
  310.33 s, all 54 stages (`.artifacts/m3b/gate-2.log`), including full-P4 generation, manifest,
  build and quotation stages, with Nano completion at 888 obligations, 0 unresolved
  (review and release pending under the allowance, as on every tree after `42ffad6`).
- `nix develop .#upstream -c python3 P4SpecTecTest/Oracle/P4/Replay/replay.py --upstream
  "$PWD/upstream/p4-spectec" --p4c "$PWD/.artifacts/p4c"`: exit 0, both legs, nine
  observation mutations rejected on each (`.artifacts/m3b/replay-both-2.log`). Not a gate
  stage: it needs the upstream build and the p4c checkout (`scripts/fetch-p4c.sh`).
- Generated Nano output is byte-identical (`p4spectec-gen ... --check` in the gate).
- Independent review: [full-P4 review](notes/full-p4/review.md), "Executable generation
  stage"; no blockers, findings resolved before the commit.
- Remote CI has not run on this work; a cold Linux build of `P4Spec` and byte-identical
  generation there are unobserved until it does.

## Open threads and next step

1. Next: the M3C campaign on both legs. Extend the corpus worker with the generated leg
   (decode into `P4Spec.p4program`, wall-clock bound instead of fuel), re-establish run
   identities, then run shards and classify every disagreement.
2. Then M3B's exit: generate `StateProps` relations and state run-soundness in modules
   beside the spec chain, starting with nonrecursive relations and measuring before the
   recursive groups.
3. A warm `lake build` log shows `PANIC at Lean.Meta.whnfEasyCases ... loose bvar` replayed
   as an info message from `NanoP4Spec.Refinement.Reverse.TableEntry_ok` (line 36). The
   module builds and its audits pass; the message predates this work and is unexplained.

## Repository state

Work is on local branch `m3b-generation` until reviewed. Preserve local `n3-decl-load`
(`82fbe2e`, non-ancestor WIP), unrelated `docs/repository-review`, and the dirty old
`../p4-spectec-lean-replay` worktree. The expected four-file upstream exporter patch
remains applied; no source pins changed. `.artifacts/p4c` holds the pinned p4c samples.
