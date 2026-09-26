# Retired committed history

Durable recovery instructions, 2026-09-26. The user requested one active
checkout and the smallest branch set.
Old experiments are retired, not silently merged or declared complete.

## Small recovery backup

Location: `/Users/qobilidop/my/work/p4-spectec-lean-archive-20260926`.
This private directory is not a registered worktree. It holds a roughly 7 MB
`repository.bundle`, `manifest.json`, `SHA256SUMS` and `RESTORE.md`.

Bundle SHA-256:
`0ee22dd99e6d05a3255b80a1795bf2096c583ca0becfa9b3e725ca159d2a9a8f`.

Bundle verification reported complete history with no prerequisites. An
independent mirror restore and `git fsck --full` passed. All 43 original local
branch tips were present, and all 16 refs at the archival checkpoint matched.
The temporary verification mirror was removed after these checks.

## Intentionally discarded

A 24 GiB full-folder snapshot initially preserved eighteen secondary worktrees
and common Git metadata. It passed byte/metadata and 108,370-entry inventory
checks before worktree removal. The user then explicitly chose to keep only
the small committed-history backup and discard the full snapshot.

Consequently, old ignored logs, probes, raw corpus data, caches, exact checkout
metadata and saved sequencer state are no longer recoverable from this backup.
This is intentional, not a claim that the bundle contains those files.
Current primary source and its artifacts were left untouched.

The stale integration cherry-pick was closed before removal with `--quit`,
not `--abort`: HEAD `8c16ed9`, index SHA-256
`1699458ac1109ff5797c903826c5cea3beaeb5dec47487bd3f2016daebf9cbca`
and clean source stayed unchanged. Its source was already integrated.

## Recovery landmarks

- `m3b-state-production` at `925fdbf`: genuinely paused aggregate, source
  integration `1b2ac70`. The second full-P4 casting proof still exceeds the
  recorded budget. Do not merge it blindly or claim it is completed.
- Corpus code `c4a8858`: historical partial campaign logic; raw campaign
  artifacts were discarded, so exact resumption is no longer available here.
- Documentation `1bedd08`: original approved README/design work and earlier
  preservation/cleanup ledgers before selective reconciliation with main.
- WIP snapshots `dc9468f`, `a74690b`, `2334c90`, `a9bd60d`, `3e13ba8`
  and `4ad0378`: individually preserved committed generator/proof/corpus work.

## Recover code deliberately

Verify and clone the bundle into an unused directory, or fetch a saved branch
into a new recovery branch. `git bundle list-heads` lists the saved names.
Historical names can be restored from their manifest commit tips.

Rebuild pinned dependencies and revalidate before using an experiment.
Historical result summaries remain in committed notes; do not reinterpret
them as fresh evidence or resume a discarded raw campaign automatically.
The backup is local-only: retain it or back it up before deleting the directory.
