# M3A export review

2026-09-25, independent read-only reviewer `review_export`.
Scope: `scripts/export-spec.sh`, full P4 export, Nano-P4 stability.

No blocking findings. Upstream's `frontend/parse.ml` and
`util/filesys.ml` implement recursive sorted traversal, excluding
`include/`; the script now delegates to them. The export contains all
108 source files in its regions and no unexpected source paths.

Checks in the Nix shells: shell syntax exit 0; Nano export identical to
HEAD; two independent upstream export runs, streamed into hashes without
file writes, exit 0 and byte-match the working exports:

- Nano: 8,508,087 bytes,
  `3a7b47d75ca97a1404026cde45df09bde0372a06e32c8d80b00ca3ef48b99dd6`.
- P4: 98,387,720 bytes,
  `803d798c13ae102e6aa970f65dfd2313d9d9b4094cae745049d3418c1af11953`.

Observations dispositioned in `.agents/notes/full-p4-reconnaissance.md`: the full
JSON was close to the GitHub per-file size limit; after user discussion
it is stored losslessly compressed with a checksum (snapshot changes
reviewed separately below). Upstream warns that `$sink` has no clauses, which is recorded
without calling the export warning-free. Quotation work and the full
gate were outside this review's scope.

Follow-up storage review: no findings. Three snapshot tests and shell
syntax pass; full-P4 gzip reproduces byte-for-byte, decompresses to the
original hash, and matches the index. Invalid/truncated gzip and a wrong
checksum exit 1 and preserve an existing cache. The gate immediately
exits on verification failure, before census execution. Raw JSON is
ignored; Python is available in both Nix shells. Nano migration and the
size guard received an additional review: no code findings. The Nano
archive restores HEAD's original bytes exactly and is deterministic;
the actual size gate and its staged/working/boundary/deletion tests pass.
The only remaining finding was stale checkpoint prose, fixed in status.
