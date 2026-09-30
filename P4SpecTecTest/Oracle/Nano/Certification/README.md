# Nano certification inventory and cross-layer mutations

This directory holds the pinned Nano corpus inventory and the cross-layer mutation
runner that the completion check (`scripts/nano-certification.py`) uses.

## Pinned corpus inventory

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
bundles. Packet links retain the three guard-disabled sessions of the bounded
upstream packet fixture; the guarded failure session remains in that fixture as
boundary evidence, but it cannot fulfill the guard-disabled profile. Upstream
observations of all 39 STF sessions live in the session recording
(`P4SpecTecTest/Oracle/NanoSwitch/Sessions/`). An empty observation list is an
outstanding obligation, never a successful skip.

Observation presence is separate from checked generated/reference replay and
kernel-checked semantic certificates. This inventory claims neither; the combined
completion checker owns proof and replay validation, and counts a replay obligation
only after its own replay run verifies it. Unknown verdicts and missing typing
artifacts are reported explicitly; canonical comparison also rejects stale or
forged observation links and added `certified`/`replayChecked` flags.

Run in the repository Nix shell (absolute paths shown):

```sh
nix develop --command python3 /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/Oracle/Nano/Certification/corpus.py
nix develop --command python3 /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/Oracle/Nano/Certification/test_corpus.py
nix develop --command python3 /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/Oracle/Nano/Certification/corpus.py --update
```

`--update` only regenerates inventory from current bytes and exact pins; it
does not recapture upstream observations. Ordinary mode checks freshness and
reports observation presence; `--strict` always fails, because this inventory never
validates replay (the completion checker does).

## Cross-layer mutations

`mutations.py` mutates generated code, generated quotations and a copy of the
export, and requires each mutation to be observable and rejected by its named
check: the replayed generated refinement proof, quotation comparison, or
`check-quotes`' empty print-hint check. Its docstring lists the cases;
`test_mutations.py` holds its fail-closed contracts. Run after
`lake build check-quotes` and the default targets:

```sh
nix develop --command python3 /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/Oracle/Nano/Certification/mutations.py
nix develop --command python3 /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/Oracle/Nano/Certification/test_mutations.py
```
