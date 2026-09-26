# Pinned Nano corpus inventory

`corpus.json` is generated from the Git trees at the repository's recorded
P4-SpecTec and Nano specification stage-0 indexed gitlinks. Missing, unmerged
or non-gitlink index entries fail; each checkout must be at its indexed pin.
This also admits a reviewed staged pin change before commit. It retains all
78 source programs
(including 30 upstream AL typing rejections) and all 39 paired STF sessions.
There are no source-profile exclusions at these pins. A missing source file
fails freshness checking even if its manifest case is removed; changed source,
include or specification bytes also fail against their pinned Git objects.

Each program has a `corpus:typing:<group>/<name>` obligation and each STF has
a `corpus:packet:<group>/<name>` obligation. IDs stay stable when evidence is
added. The Python API is `load(path)`, `check_manifest(manifest, root)` and
`check(root, path)`; successful checks return every required obligation ID.
`obligation_ids(manifest)` is only an accessor, so call a checker before using
its result to validate completion.

Typing export links retain upstream verdicts, parsed programs and outputs or
failure diagnostics. They describe artifacts captured by
`scripts/export-program.sh`; inventory consistency does not prove that tool's
capture was faithful. All 78 current programs have complete upstream typing
bundles. Packet links retain the three guard-disabled sessions already in the
bounded upstream packet fixture. The guarded failure session remains in that
fixture as boundary evidence, but it cannot fulfill the guard-disabled profile.
The other 36 STF sessions have no packet observations yet. An empty observation
list is an outstanding obligation, never a successful skip.

Observation presence is separate from checked generated/reference replay and
kernel-checked semantic certificates. This inventory claims neither: all 117
replay evidence obligations remain outstanding here. The combined completion
checker owns proof and replay validation. Unknown verdicts and missing typing
artifacts are reported explicitly; canonical comparison also rejects stale or
forged observation links and added `certified`/`replayChecked` flags.

Run in the repository Nix shell (absolute paths shown):

```sh
nix develop --command python3 /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/Oracle/Nano/Certification/corpus.py
nix develop --command python3 /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/Oracle/Nano/Certification/test_corpus.py
nix develop --command python3 /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/Oracle/Nano/Certification/corpus.py --update
```

`--update` only regenerates inventory from current bytes and exact pins; it
does not recapture upstream observations. `--strict` additionally rejects the
currently absent checked replay evidence, while ordinary mode checks freshness
and reports outstanding work. It must be replaced by actual replay evidence
validation before claiming corpus completion.

For N5, prefer pinned `positive/src-addr-filter.p4` and its STF session: the
parser actually extracts the Nanonet header, then a source-address table allows
addresses 1 and 2, denies 3, and defaults to drop. The STF forwards `000100`
unchanged on port 0, then drops `000300` and `000A00`. This is a future proof
candidate, with no packet replay or whole-program theorem claimed today.
