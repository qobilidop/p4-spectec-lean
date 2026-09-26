# Bounded Nano target

Paused integration boundary. Updated 2026-09-26 by consolidating the
2026-09-25 target, packet, driver and verify notes/reviews, not by running a
new semantic audit. Current reproduction belongs to
[test/nano-target](../../test/nano-target/README.md) and
[test/nano-verify](../../test/nano-verify/README.md).

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
  constructors include PACKET but not bare ExternV; canonicalization retains
  that distinction. Restoring PACKET would repair upstream semantics, not
  faithfully port it. Full contexts and subsequent calls matter, not merely
  final transmitted bytes.
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

## Resume only under new scope

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
