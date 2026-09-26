# Bounded dynamic Nano target observations

This is not a typed `NanoP4Spec.Externs` instance or a simulator/boot port.
The target intentionally returns the pinned raw `ExternV objectState`.
No `PACKET` repair or semantic JSON normalization is applied.

`observed.json` holds 24 primitive and direct-handler observations. The
callback checks cover names, order and selected semantic arguments,
including the exact `Atom LOCAL` shape and header name. They do not compare
all value notes. Primitive assertion/array/decode categories are distinct;
at the StateEval target boundary an upstream array exception corresponds
only to Lean hard error, never mismatch or a successful empty packet.
Packet records retain signed indices and inconsistent declared lengths.
The numeric boundary is a 64-bit OCaml runtime's signed 63-bit integers;
outside that domain the primitive API reports unsupported host range.

`packet-observed.json.gz` is a lossless compact snapshot of four actual
upstream AL STF sessions, including typed relation inputs and outputs.
The 154 KB snapshot expands to about 4.3 MB, with a SHA-256 sidecar.
Only recognized source-region paths are normalized; arbitrary ExternV
JSON, text bytes, notes and other semantic data remain in the fixture.
Source hashes are independently checked against a catalog hashed from
the exact pinned Git objects. This is reproducible provenance, not a
cryptographic attestation of oracle correctness.

The Lean replay starts each `NanoSwitch_drive` invocation from the
upstream-captured initial context and exact fresh counter. It compares
every semantic relation output using the existing `Runtime.Value.eq`
boundary (which ignores notes/regions and function-value identities),
and the exact final fresh counter. It checks six successful invocations:
one `free-pass`, two `field-access`, and three `action-call-table-2`.
The seventh, guarded `field-access`, fails upstream and returns Lean
`.err`. Upstream's public runtime failure collapses internal failure kinds;
the replay does not claim equality of those internal kinds.

This is real AL relation replay, not a port of boot, the driver, STF
parsing, or packet transmission. Upstream STF success is recorded but
not independently derived by a Lean STF runner. Callback interpreter fuel
is one million and callback nesting is limited to 100; exhaustion fails
the comparison. These are explicit test bounds, not a termination theorem.

Sensitivity checks reject changed outputs, counters, a source-header bit,
and the wrong singleton-sequence LOCAL shape. A restored PACKET wrapper
changes the guarded failure into success and is rejected there. It is
**not** distinguished by unguarded final outputs in these programs, because
the receiver is discarded; the direct-handler oracle separately preserves
and checks that boundary.

Run offline in the default pinned shell:

```
lake build --wfail check-nano-target check-nano-packet P4SpecTecTest.NanoTarget
python3 test/nano-target/test_contract.py
python3 test/nano-target/check.py
```

Re-observe in the pinned upstream shell, using absolute checkout paths:

```
python3 test/nano-target/run.py --upstream /absolute/p4-spectec --check
python3 test/nano-target/packet-run.py --upstream /absolute/p4-spectec \
  --spec /absolute/nano-p4-spec --check
```

The runners reuse the reviewed exact-pin/four-file-export-patch check and
rebuild the complete upstream executable before linking probes. Every
primitive observation and every packet session runs in a fresh process.
Packet configuration is AL, cache=false, det=false, with guard recorded
per session. `packet-run.py --update` regenerates the compressed snapshot;
updates require independent review and the full gate before publication.
