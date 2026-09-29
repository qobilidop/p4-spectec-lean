# Bounded Nano target

Raw-receiver rejection and short-packet extract have reusable branch contracts;
broader N4 implementation remains planned.
Retained because it owns the current target exclusions that constrain claims
under the approved certification plan. Updated 2026-09-29.
Historical target/packet/driver/verify evidence remains
below; new raw-receiver continuation checks are recorded in the
[Nano checkpoint](nano-certification.md). Full-P4 integration remains paused. Current reproduction belongs to
[NanoSwitch target](../../P4SpecTecTest/Oracle/NanoSwitch/Target/README.md) and
[NanoSwitch verify](../../P4SpecTecTest/Oracle/NanoSwitch/Verify/README.md).

## What is established

The retained dynamic ports cover packet primitives and extract, a partial
`drive_pipe`, and shared `verify`. They use explicit StateEval callbacks,
preserve failures and final counters, and are exercised by committed upstream
observations. They do not provide Lean boot/STF parsing, a complete simulator,
a typed Nano Externs instance, full-P4 v1model/eBPF support, or whole-corpus
coverage. Ordinary CI replays fixtures offline; it does not recapture upstream.

Pins for the historical evidence are P4-SpecTec
`8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3` and Nano
`60dfd9912011bd5b1746ac88b26b58f7b3981991`, with the four-file exporter patch.

## Boundaries that must survive future work

- Nano extract returns raw `ExternV objectState`, while the Nano AL relation
  declares a `value` output and writes it into the receiver. Generated value
  source constructors include PACKET but not bare ExternV; canonicalization retains
  that distinction. An explicit runtime-only generated alternative now carries
  raw externs while source packet/object membership stays unchanged. Restoring
  PACKET would repair upstream semantics, not faithfully port it. Full contexts
  and subsequent calls matter, not merely final transmitted bytes.
- Three original unguarded STF cases (`free-pass`, `field-access`,
  `action-call-table-2`) passed; extract observations returned raw ExternV.
  Guarded field-access failed after its first such result. The observation
  probe itself exits 0 when recording a failure: inspect its classified result.
  Unguarded outputs can discard the bad receiver. Keep both guarded and
  direct-handler distinctions when testing a proposed adapter.
- Packet operations preserve signed/inconsistent decoded records with
  operation-specific checks. Signed-63-bit addition occurs before the
  short-packet branch. Out-of-host values are unsupported, not empty packets.
  Callback order, failure state and explicit fuel/nesting bounds are part of
  the comparison.
- The driver transmits only for the exact optional FORWARD mixop; noncases
  and singleton sequences drop. Preserve original port/payload, ctx/arch
  and actual upstream driver observations. Ports outside signed 63-bit range
  reject before callbacks rather than wrap.
- Schema 2 retains complete independent relation and driver contexts:
  8,510,069 raw bytes / 305,049 compressed bytes, 16 MiB expanded limit and
  1 MiB compressed limit. Do not drop semantic fields to fit the old 8 MiB
  limit. Semantic value equality is not arbitrary note/cache identity equality;
  selected direct tests check notes separately.
- Shared verify uses the full-P4 prefixed-name/cursor getter ABI, not Nano's
  scope/context/name ABI. Both ordered lookups precede Boolean unpacking.
  Preserve RETURN/REJECT notes and callback failure post-state. Nano permits
  extern objects only and has no ExternFunctionCall_eval; the actual Nano AL
  getter replay yields unmatch with unchanged counter. Direct helper success
  is not successful Nano source-program verify coverage.
- Capture guards require the exact canonical spec root/pin, clean tracked
  inputs/index, and no untracked inputs, including ignored files. This is a
  cooperative local check, not protection from hostile concurrent mutation.
  Compressed fixture provenance uses exact-pin Git objects and strict JSON.

## Historical review and validation

Independent root reviews covered primitive/packet/driver/verify semantics;
separate agents reviewed root-authored gate wiring and main reconciliation.
Implementation authors reviewing separate gate changes did not claim
independent review of their own semantics. The full reports, frozen hashes,
commands and ownership boundaries are recoverable from commit `968ad65`
under the former `.agents/reviews/m3d-*.md` paths.

The primitive mocks initially missed an incorrect LOCAL singleton-sequence
shape. Actual AL packet replay exposed it; the handler and both oracles now
require the exact Atom constructor. The distinguishing test, not a new
universal instruction, retains this lesson.

Reviewed replay evidence: 24 direct primitive/handler cases, eleven direct
driver cases, six successful actual relation/driver events plus one guarded
failure, and nineteen direct verify cases. Root independently recaptured
the pinned upstream observations; fixture bytes remained unchanged after
the exact-spec guard fix. The verify review reran five replay mutations,
seven fixture contracts and six spec-input guard regressions, all exit 0.
Packet/driver reviews also reran distinguishing output/state/shape mutations.

Gate reviews and source-preservation checks covered merges of `96078a0`
with `2c85f1b`, `2635a32` with `d039786`, and `cf1832f` with
`1f5cfc0`. Those reviews did not themselves establish final remote CI.
A recorded Nano combined full gate exited 0 with 342 quotations and 1,689
census definitions; the latest whole-repo validation belongs in status.

## Remaining integration obligations

### Reusable raw-receiver contract

Bounded implementation based on `e9c9b5e`: `PipeContract.lean` now owns
`P4SpecTec.BackendSim.NanoSwitch.Pipe.rawReceiverHandlerError`. Its statement and
`rfl` proof are moved from the representation test, with the same exact axiom audit
(`propext`, `Classical.choice`, `Quot.sound`). The test keeps its original theorem
and audit, consuming the library theorem. The core root imports the new module;
the new module imports only `Pipe`, with no generated-model dependency.
This changed proof ownership, not execution or certified scope. At that checkpoint,
short-packet extract, JSON round trips and target composition remained open.
Targeted `lake build --wfail` of the contract and representation test returned exit 0.
Independent read-only Codex GPT-6 Astra review against `e9c9b5e` found no issue:
the exact universal statement, proof, audits and core import boundary are retained.
This is AI review without reviewer builds. The full
`nix develop -c /usr/bin/time -p /Users/qobilidop/my/work/p4-spectec-lean/scripts/check.sh`
returned actual exit 0 in 161.97s, no skips (session 25315); log
`.artifacts/n4-raw-receiver-gate.log`. Strict N3, oracle replay and mutations passed.
Fresh text, whitespace and relative-link/heading checks also passed. Documentation
review corrected the status link's ownership of earlier versus current checks.
Remote CI for this new code checkpoint is separate and not yet established here.

### First bounded N4 task: extract without callbacks

Implemented from `9aff53b` as `Pipe.shortPacketExtract` in `PipeContract.lean`.
It covers the short-packet branch of `Pipe.eval_extern_method_call`, aligned with
`p4spec/lib/backend-sim/nano_switch/pipe.ml`. For correctly shaped PACKET/extract/hdr
arguments constructed with the theorem's fixed notes, whose JSON decodes to
`PacketIn pkt`, and `hostAdd pkt.idx 24 > pkt.len`, it proves the exact result for
every context, packet type identifier, callback and initial fresh counter:
`some (.ok [rawExtern (extern_to_yojson (.PacketIn pkt)), originalContext], counter)`.
Here `rawExtern` abbreviates `Value.Make.extern (Pipe.varT "objectState")`.
No callback premise is needed: this branch never calls one. Keep signed/inconsistent
decoded records admitted and the actual wrapped `hostAdd` guard, not natural addition.
Use the now-reusable `Pipe.rawReceiverHandlerError` theorem alongside it: raw-ExternV
receiver rejection gives hard `.err`, unchanged counter, for arbitrary callback
and other arguments. This is a helper contract, not N4 closure.

The proof simplifies the handler with its decoding/guard hypotheses, then closes
the concrete dispatch with `rfl`; the audit requires exactly `propext`,
`Classical.choice`, `Quot.sound`. The target regression checks the full packet JSON,
context Boolean and counter for an inconsistent signed-length record with a
state-changing callback available. The universal theorem proves the stronger exact
context/value equality. Focused contract/target `--wfail` builds passed, exit 0.
Early focused failures were proof completion, audit whitespace and an attempted
concrete JSON equality proof; that extra round-trip proof is outside this slice.
The final executable regression uses structural JSON comparison, not value-wide BEq.
One premature full gate was stopped (exit 143) before code correction; it is not
passing evidence. The corrected full `scripts/check.sh` returned actual exit 0
in 142.03s, no skips (session 78128); log
`.artifacts/n4-short-packet-gate-validated.log`. Strict N3, both Nano replay legs,
target oracles and mutations passed. Fresh text, whitespace and 26 relative-link/
heading checks passed. Independent read-only Codex GPT-6 Astra review against
`9aff53b` found no blocker in the theorem, exact axiom audit, final executable
regression or scope documentation. It ran no builds; this is AI review.
This branch helper leaves completion metadata unchanged. Remote CI for the new
checkpoint is separate from these local results.

Next separately scoped proof pieces:

- Extend `P4SpecTec/BackendSim/NanoSwitch/PipeContract.lean`, already registered
  in `P4SpecTec.lean`. It must not import generated Nano modules.
- The short branch assumes successful JSON decoding. Separately establish that
  serialization/decoding gives that premise for admitted host-range packet records.
  Do not assume JSON round trips for arbitrary mathematical integers.
- `P4SpecTecTest/BackendSim/NanoSwitch/Target.lean` already has receiver
  and argument constructors, `noCallback`, inconsistent-length and overflow cases.
  Preserve these checks when adding round-trip and long-packet proofs.
- The future typed bridge must consume the representation established in
  `P4SpecTecTest/Refine/NanoTargetRepresentation.lean`; reusable versions belong
  outside tests. Generated `NanoP4Spec/8.01-eval-relation.lean` defines pure
  `Externs`, whereas `Pipe` uses `StateEval`. Discharge the state/pure bridge
  explicitly; do not reset or discard callback counters. The full contract in
  `NanoP4Spec/Refinement/Externs.lean` quantifies arbitrary related inputs, not
  merely this successful branch. Long-packet callbacks and all failure branches
  remain obligations; do not bind the complete target obligation after this slice.

The next round-trip task must justify decoding on its stated host domain; it is
not a claim of this branch contract. Reproduction commands from the repository root:

```sh
nix develop -c lake build --wfail P4SpecTec.BackendSim.NanoSwitch.PipeContract P4SpecTecTest.BackendSim.NanoSwitch.Target
nix develop -c lake build --wfail check-nano-target check-nano-driver check-nano-packet
nix develop -c python3 /Users/qobilidop/my/work/p4-spectec-lean/P4SpecTecTest/Oracle/NanoSwitch/Packets/check.py
nix develop -c /Users/qobilidop/my/work/p4-spectec-lean/scripts/check.sh
```

Run one build at a time, then independent review and the required publication checks.
The full gate builds the oracle binaries before running their replay.
No new library, generated-file edit, source pin change or whole-corpus claim is needed.

Readiness validation: documentation only, reusing the actual exit-0 full gate for
`67f67ae` (124.00s, unchanged executable inputs). Fresh text and whitespace checks
and eight relative-link/heading checks passed. Independent read-only Codex GPT-6
Astra review of the two-document diff against `fde887c` identified the existing
raw-receiver theorem for reuse and confirmed the branch semantics and scope;
that finding is incorporated. Final review also required building the three native
oracle executables before direct packet replay; the command sequence now does so.
This is AI review without builds or new proof checks.
Maintenance CI `36543103039` for `fde887c` was still in progress when first checked;
no passing verdict is inferred for that run or the new readiness checkpoint.

### Broader target obligations

Enumerate affected extract cases with exclusions remaining in the denominator.
Dynamic execution may agree where a typed adapter is explicitly unsupported.
An unsupported typed result ends that comparison as excluded, never as an
upstream runtime error or matching failure; propagate the exclusion through
callers rather than continuing with a repaired context.
An adapter requires an upstream-supported pin correction or a separately proved
contextual representation contract, never silently rewrapping values.
Do not apply this Nano mismatch by analogy to v1model/eBPF: their externs return
ctx/arch/callResult and require separate faithful ports and validation.
Clarify the supported target profile before declaring any M3D milestone closed.
