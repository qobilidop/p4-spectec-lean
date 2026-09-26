# Project state archival review

Independent read-only review by `/root/p4_oracle`, 2026-09-26, with nested
repository and sequencer inventory by `/root/state_props`.

The stronger user request permits external archival and closure of historical
refs/checkouts, not completion or silent integration of experiments. Earlier
generator, interpreter, bounded proof and oracle work is integrated/superseded
on main; later recursive/SCC/determinism work is captured by paused production
`925fdbf`. Documentation reconciliation is reviewed in `project-state-docs.md`.

The lossless archive scope covers eighteen complete secondary trees plus full
primary `.git`: all artifacts, private metadata, seven absolute alternates
targets and detached shallow p4c. The bundle and restored mirror independently
preserve committed histories. Primary source/artifacts stay active.

Root recorded tar create/compare 0, exact 108,370-entry inventory equality,
bundle verification, mirror fsck 0, all 43 original tips present, all 16 bundled
local refs matching, and archive hashes. The reviewer independently checked
bundle scope and accepted removal conditional on these results, clean source,
no open handles and unchanged sequencer fingerprints.

The stale cherry-pick todo's five source/test files exactly matched integration
HEAD. After archival, `--quit` kept HEAD, index bytes and clean source unchanged.
Earlier porcelain-only checks missed this sequencer; the procedure corrects
that audit gap without aborting, resetting or resuming the operation.

All 23 old non-main GitHub refs were exact merged PR heads (#5-27), ancestors
of `499230b`, with no open PR at inventory. After the fresh full local gate
passed, an atomic deletion push guarded every exact SHA. Fresh remote inventory
then showed only main. Unique local histories left active refs only after exact
backup matching. Consolidation publication still requires its own review/CI.

No preservation finding remains. This is not validation of archived experiment
correctness or full-P4 completion. Local-only backup and restore-path limits are
explicit in `.agents/notes/archive.md`.

## Subsequent user-directed reduction

After the verified worktree removals, the user explicitly approved retaining
only the small committed-history backup and deleting the 24 GiB folder snapshot.
Root deleted that snapshot and the redundant verification mirror, then verified
their paths absent and the bundle retained. Old ignored logs, probes, raw corpus
artifacts and exact checkout/sequencer metadata are intentionally no longer
recoverable from this backup. The earlier lossless-archive review describes
the safety of the worktree removal, not the final retained backup's contents.
