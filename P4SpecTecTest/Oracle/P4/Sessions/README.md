# Full-P4 STF sessions on both Lean legs

The full-P4 packet targets: upstream's v1model and eBPF simulators
(`p4spec/lib/backend-sim/{v1model,ebpf}/`, with the `core`, `spec_impl`, `table`, `hash`,
`state` and `stf` modules they use) ported to Lean under `P4SpecTec/BackendSim/`, generic in
the effect carrier and in the spec they call back into through explicit trampolines
(`Make.Spec`); the statement runner of upstream's `make.ml` is ported once over a target's
architecture operations (`BackendSim/Stf/Run.lean`). The reference leg registers a port as
the AL interpreter's externs, with the interpreter's own function and relation evaluators as
the trampolines; the generated leg runs the same port over the generated library's functions
and relations through value codecs (`Generated.lean`), and its typed `Externs` instance is
that same dispatch. The two legs therefore share one target implementation, as the
placeholder target is shared, and differ only in the semantics they call back into.

`probe.ml` runs upstream's own `run_stf_test` with an observing pipe of the given target and
records, for one P4-STF pair: the parsed program, the statements as upstream parsed them, and
every event at the architecture's boundary: the initialization, each packet with the states
before and after it, its transmissions and the fresh-identifier counters, and each
control-plane change of the architecture. Table entries and default actions are applied by
upstream's statement runner directly, so their effect is observed through the state before
the next packet. The session worker (`Main.lean`, `p4-sessions-check --arch NAME`) replays
each cached observation statement by statement on both legs with the ported statement runner
and compares every event: class, context, architecture, transmissions and counter. Upstream's
expectation matching is not ported; its verdict is recorded and every candidate is required
to pass upstream, as its expectation files say.

Values are compared as the corpus comparison compares them (`Runtime.Value.eq`), after
the target's serialized state is canonicalized: the IL values a register or a scheduled
packet keeps inside an extern payload lose their notes and regions, as they would outside
one, so upstream's cache identities and source regions do not count as semantics
(`Check.lean`, `canonPayload`).

```sh
nix develop --command scripts/fetch-p4c.sh
nix develop .#upstream --command python3 P4SpecTecTest/Oracle/P4/Sessions/sessions.py \
  --upstream "$PWD/upstream/p4-spectec" --p4c "$PWD/.artifacts/p4c" --arch v1model --jobs 8
nix develop .#upstream --command python3 P4SpecTecTest/Oracle/P4/Sessions/sessions.py \
  --upstream "$PWD/upstream/p4-spectec" --p4c "$PWD/.artifacts/p4c" --arch ebpf --jobs 8
nix develop --command python3 P4SpecTecTest/Oracle/P4/Sessions/test_sessions.py
```

The candidates of a target mirror upstream's simulator test (`p4spec/test/sim/dune`,
`Util.Test.collect_test_pairs`): the p4c samples including the target's model, paired with
their STF files, less upstream's static and dynamic exclusions, with the v1model patch
directory upstream passes (no patch applies at this pin), plus upstream's 20 regression
simulator programs, all v1model. At the pins: v1model 204 pairs, 5 excluded, 219
candidates; eBPF 17 pairs, 2 excluded, 15 candidates. Upstream's five custom v1model
sessions (`testdata/custom`) and its p4testgen STF sets are not swept. Observations are cached under
`.artifacts/p4-sessions-sweep/<arch>/` by an identity of pins, probe, harness and bounds;
the summary accounts for every candidate. The exit is zero only when every candidate was
observed and matched on both legs. Not covered: the PSA target, p4testgen's STF files,
statements after the last packet of a session (unobserved upstream), upstream's
expectation matching, and anything a session does not exercise.
