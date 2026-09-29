# Nano STF session replay

`sessions-observed.json.gz` records every STF session of the pinned Nano corpus from the
pinned upstream AL simulator (guards, caches and deterministic checking off): the
initialization outcome, context and architecture state, then each driven packet's outcome,
forwarding decision, transmissions, context and architecture state. Values are stored once
in a table; their `vid`/`vhash` cache identities are zeroed and source regions normalized.
A raw SHA-256 of the expanded JSON sits beside it.

`check.py` (ordinary gate, no OCaml) verifies the checksum, requires exactly one session per
corpus packet obligation with the inventory's source digests and program export, and runs
`check-nano-sessions`. That executable initializes the target in Lean from the exported
program and drives the recorded packets through both Lean paths: the AL interpreter with the
registered NanoSwitch externs, and the generated model with the typed extern instance. Each
must match upstream at every step, and the whole-session compositions of
`NanoP4Target.Session` must match the stepwise replay. Five observation mutations must be
rejected. Nothing is skipped: a decode failure or exhausted fuel fails the session.

Recapture in the upstream shell (exact pins required):

```sh
nix develop .#upstream -c python3 /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/Oracle/NanoSwitch/Sessions/capture.py \
  --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec \
  --spec /Users/qobilidop/my/work/p4-spectec-lean/upstream/nano-p4-spec --check
```

`--update` rewrites the snapshot. The probe observes upstream's own `run_stf_test` and never
changes target outputs. At these pins all 39 sessions (74 packets) pass upstream.
