# Nano whole-program consumer (N5)

Active, 2026-09-30: owns the N5 whole-program certificate's working evidence, constraints and
review record until the milestone closes. The user-facing account is in
[Certification](../../docs/certification.md#a-whole-program-example); the rationale for the
evaluator and the packet-text premise is in [decisions](../decisions.md) ("N5 whole-program
evidence").

## What is established

- `P4SpecTec.Tactic.LazyEval` (`lazy_eval`, `lazy_eval%`) evaluates generated code with
  kernel-checked proofs; unit tests in `P4SpecTecTest/Tactic/LazyEval.lean`, including the
  64-element `Array.mapM` regression that times out in the kernel without gap abstraction.
- `NanoP4Target.Packet`: `hexText`, `string_to_bits_hexText`, `bits_to_int_unsigned_bytesBits`
  and the `PacketStateText` premise with its evaluation rule; `NanoP4Target.Session` adds
  `Transmits`, `ReferenceTransmits` and `referenceTransmits`.
- `ExampleProofs/NanoP4SrcAddrFilter/`: the generated quotation, evaluation theorems
  (`forwardOne`, `forwardTwo`, `denyThree`, `dropUnlisted`, three short-packet drops, the STF
  session with its outcome pinned as `stfOutcome`), the `Certificate` and `referenceFilter`.
- `check-consumer` (identity, upstream observation, 7 exact claims) binds `profile:consumer`;
  the gate requires `--require-owned N5` and runs the mutation suite (baseline plus five
  rejections).

## Constraints that bind later work

- The domain is every host-range port with every three-byte packet and every shorter packet.
  Payloads need rules for symbolic array sizes, `Array.extract` over an append, and the tree
  decoder over a symbolic bit array; `omega` facts can already discharge the size checks.
- `PacketStateText` covers only host-range packet states; a theorem must not assume a broader
  JSON round trip. Rules must be proved lemmas or this premise, never axioms.
- The oracle decides only tests whose symbolic atoms all occur in the supplied facts; stuck
  bits of unconstrained header fields are left symbolic by design.
- `lazy_eval` counts its work against `maxHeartbeats`; the multi-packet STF session needs a
  4M budget. The budget is a resource limit, not a weakened statement.
- A mutation of the target is exercised on a copy in the probe namespace; the library
  instance is never edited by the runner.

## Costs (2026-09-30, local)

`ExampleProofs.NanoP4SrcAddrFilter.Evaluation` builds in about 64 s wall (170 s CPU); the
certificate, walkthrough and `check-consumer` add a few seconds; the mutation suite takes
about 90 s; `--require-owned N5` completion took 70 s.

## Review record

Pending: independent read-only review of `24d36aa`..HEAD.
