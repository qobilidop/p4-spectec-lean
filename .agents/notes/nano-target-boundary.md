# NanoSwitch target boundary

Root reconnaissance with bounded implementation checkpoint, 2026-09-25.
No whole target or packet-leg completion is claimed.
Branch `m3d-nano-target` starts at `e31c1e8`.

## Pinned inputs and observed mismatch

P4-SpecTec: `8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`, with exactly the
committed four-file JSON export patch. Nano spec:
`60dfd9912011bd5b1746ac88b26b58f7b3981991`.

`backend-sim/nano_switch/pipe.ml` takes a PACKET receiver and returns
`Value.Make.extern objectState` directly from `eval_extern_method_call`.
However, `8.01-eval-relation.watsup` declares that extern relation's first
output as `value`; `8.13-eval-call.watsup` writes that result back to the
receiver. The generated `NanoP4Spec.value` has a PACKET constructor carrying
objectState but no raw ExternV constructor. A typed adapter cannot encode
this exact upstream output by silently restoring the PACKET wrapper.

A direct pinned probe with an empty PacketIn and the `extract(hdr)` method
confirmed output `[ExternV objectState, unchanged context]`. This bypasses
header access on the short-packet branch; a dummy context suffices for
that isolated boundary test. It does not claim the dummy context is a
valid P4 program context.

A second probe instantiated the actual Nano simulator with a read-only
wrapper around its extern relation, AL mode, cache/determinism/guard all
false. Three real pinned STF cases completed with exit 0 and upstream
`Pass` results:

- `free-pass`: forwarded `00`, no extern call.
- `field-access`: forwarded `002A05`; four actual extract observations
  returned raw objectState ExternV (idx 24, len 24).
- `action-call-table-2`: forwarded `010000` and `030000`; six actual extract
  observations likewise returned raw ExternV.

Thus unguarded upstream packet success does not establish the typed extern
contract. Multiple observations include retrying ordered rule alternatives;
they are not a count of distinct input packets.

Repeating actual `field-access` with `guard=true` returned a runtime failure:
`invocation of relation NanoSwitch_drive failed`, after observing its first
raw ExternV result. The probe itself exited 0 because it records both Pass
and Fail outcomes. This guarded outcome is not a successful packet test.

Both probes compiled against rebuilt, revision-guarded upstream libraries
using the existing export-oracle compilation helper, in the pinned upstream
Nix shell. Scratch source/log artifacts stay ignored under `.artifacts/`.
This evidence must become a durable versioned oracle before it gates any
target implementation; scratch observations alone are not a published test.

## Next steps and constraints

Port shared packet data operations with exact byte/bit/JSON tests. Determine
the full affected Nano corpus and whether guarded upstream execution rejects
this boundary. Preserve the mismatch as explicit evidence. Do not silently
repair upstream, widen every generated value type, classify affected cases
as agreeing, or substitute packet-only agreement for full context agreement.
Any compatibility deviation requires an explicit documented decision and
independent review. Full-P4 v1model/eBPF packet work remains separate; no PSA
implementation follows from the syntax present in the export.

## Bounded implementation checkpoint

Core.Object and NanoSwitch.Pipe now partially mirror the data operations
and dynamic extract handler, with explicit StateEval callbacks and raw
ExternV outputs. The 24-case direct oracle is versioned and replayed.
Real NanoSwitch_drive replay covers six successful events and the guarded
field-access failure, starting from upstream-captured contexts. Full
semantic outputs and exact fresh counters agree. The replay caught and
fixed a wrong LOCAL singleton-sequence shape which loose mock unpacking
had accepted; exact callback shape checks now guard that boundary.

The full typed four-session observations are stored losslessly as a
154 KB gzip snapshot, with exact source hashes and bounded decoding.
`test/nano-target/README.md` defines comparison scope and reproduction.
The port still excludes boot, driver/STF, verify, and a typed Externs
instance. Existing unguarded packet outputs do not distinguish a repaired
PACKET receiver; the guarded outcome and direct-handler oracle do.
Independent final review and full gate are pending, so this is not yet a
published support claim or completion of M3D.
