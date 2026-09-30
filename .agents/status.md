# Status

N5 (whole-program theorem) in progress on local branch `n5-consumer`, 2026-09-30; the user
authorized completing the Nano-P4 milestone (N5 and N6) fully autonomously the same day. N4 is
complete on `main` (`4535868`, [CI 36592809255](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36592809255)).
Full-P4 M3 remains paused.

## Verified state (branch)

- `lazy_eval` evaluates generated code with kernel-checked proofs: `partial_fixpoint` and
  well-founded definitions are rewritten by their equations, definitional gaps abstract shared
  fixpoints, free variables become temporary axioms, and `omega` decides stuck tests from facts
  (decisions, "N5 whole-program evidence").
- `ExampleProofs/NanoP4SrcAddrFilter/` proves, from the quoted export, that every three-byte
  packet on every host-range port is forwarded unchanged exactly when its source address is 1
  or 2 (other header fields symbolic), shorter packets are dropped, and the STF session's
  outcome; `referenceFilter` transfers the property to the reference interpreter. The only
  premise is `NanoP4Target.PacketStateText`. Certificate axioms: `propext`, `Classical.choice`,
  `Quot.sound`.
- `check-consumer` passes: the quotation is the decoded export, the proven initialization and
  final STF contexts and transmissions equal the upstream recording, and 7 claims have their
  exact types.

## Commits on `n5-consumer`

`24d36aa` evaluator; `4c9dcb8` packet families and transmissions; `a8136b1` program quotation;
`62f41b7` whole-program example and checker.

## Validation

At `62f41b7`'s tree: `lake build --wfail` (default targets), `lake test`,
`lake build --wfail ExampleProofs check-consumer nano-program-quote`, `check-consumer` on the
decompressed session bundle, the library boundary check and the text check all exit 0. The full
gate has not run; the gate does not yet run the new checks.

## Remaining N5 obligations

1. Mutation tests at the intended boundaries: source identity, packet branch, extern result,
   output and state (`ExampleProofs/NanoP4SrcAddrFilter/test/`).
2. Gate integration: quotation freshness, `check-consumer`, the mutation runner.
3. Completion binding of `profile:consumer` to `check-consumer`, with CLI tests.
4. Documentation: certification guide, design section 9 status, example note, pitfalls.
5. Independent review, full gate, merge, push and CI.

Then N6 (plan, `notes/nano-certification.md#n6-close-release-evidence`).

## Repository state

Preserve local `n3-decl-load` (`82fbe2e`, non-ancestor WIP), unrelated
`docs/repository-review`, and the dirty old `../p4-spectec-lean-replay` worktree. The
expected four-file upstream exporter patch remains applied; no source pins changed.
