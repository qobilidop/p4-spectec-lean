# Stateful upstream oracle review

2026-09-25. Root-agent independent review of Sol-authored checkpoint
`59525a2`, then integration with the reviewed byte/effect interpreter.
No outstanding findings in the original oracle after the fixes below.

The OCaml probe links the real pinned `Interp_al.Interp.Make` functor and
interface, constructs the same small AL definitions as the Lean consumer,
and records actual interface checkpoints. Each independent case resets the
interface counter; the session case deliberately does not reset between
calls. The extern stub allocates through the same interface before failing.
Negation alternatives return distinguishable tags, and the shared-prefix
case can detect incorrectly hoisted allocation. Caches, deterministic checks
and input/output guards are explicitly disabled on both sides.

The five primitive cases call the actual fresh builtin, not a transliteration.
The initial consumer accepted either Lean failure tag even for primitive
observations; review required exact `.unmatch` for the probe's caught
`BuiltinError`. Fixed, with negative/positive guards. Review also requested
capturing the initial seed directly, checking initialization succeeds, and
checking the git-index command's exit status; all are fixed.

The public upstream AL interface collapses internal error kinds, so its
observations intentionally compare success/failure, exact payload and final
counter, not unobservable internal tags. This limitation does not apply to
the direct primitive mismatch checks. Guards and wrap are separately scoped;
the fixture does not claim guarded higher-order or full-P4 coverage.

The consumer requires the exact ordered case list, known scopes/operations
and status tags, the indexed gitlink, actual checkout HEAD and recorded
revision. Missing, duplicate or unknown cases cannot silently be skipped.
Integration keeps fresh ASCII payloads exact through ByteText, uses checked
UTF-8 observation and strict JSON ingress, and adds the oracle to the gate.

Independent primary-worktree checks through the pinned Nix shells:

- Recompile and run upstream `test/state/run.py --check`: exit 0, all 15
  observations reproduced at `8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`.
- `lake build --wfail check-state-oracle`: exit 0 after byte integration.
- `lake exe check-state-oracle`: exit 0, all 15 observations match.

The original author independently rechecked the root-authored byte/JSON/CLI
adapters and gate sensitivity harness: no findings. Its independent run
exited 0; the passing control is accepted and all ten corrupt fixtures are
rejected (missing/duplicate/reordered cases, wrong counter/payload/scope,
unknown status, wrong revision, invalid UTF-8 and invalid JSON).
Full-gate evidence is recorded in status rather than inferred from these
focused checks. No stateful codegen/refinement or full-P4 claim.
