# Independent bounded full-P4 interpreter replay review

2026-09-25. Root independently reviewed `a4c907b` and follow-up `5657373`.
The implementation was authored by the oracle/replay agent. No correctness
findings remain within the stated four-case boundary.

The driver rechecks the pinned source/export patch, rebuilds upstream, checks
the pinned p4c inputs, exact manifest/digests and CLI parity before handing
typed boot JSON to Lean. Lean seeds each relation independently at the
observed post-boot counter, compares semantic output values and arity, and
requires the exact final counter. Public upstream unmatch collapses the
internal failure tags; the runner documents that limit rather than claiming
to distinguish them. Fuel exhaustion and upstream abort do not count as
matching failures. The syntax case is explicitly not a Lean AL execution.

Compared the two narrow placeholder extern implementations with pinned
`backend-sim/placeholder.ml` and its dispatch in `backend-sim/extern.ml`.
The null payloads and `objectState`/`archState` notes agree; this is a replay
configuration adapter, not a generic interpreter change or a packet target.

Initial review found syntax-only execution settings bypassed validation and
counter seeds could silently wrap. Follow-up centralizes envelope checks and
requires signed 63-bit round-trip equality before state construction. Nine
real Lean-side mutations now exercise output/counter disagreement, malformed
values, unsupported classes, invalid seeds, syntax settings and zero fuel.
The value/counter/configuration tests check the particular rejection reason.

## Independent verification

- `nix develop <primary>#upstream --command python3
  test/p4-oracle/replay.py --upstream <primary>/upstream/p4-spectec
  --p4c <state-oracle>/.artifacts/p4c`: exit 0 in the frozen replay worktree.
  All six booted relation runs matched; the syntax case remained syntax-only;
  all nine Lean mutations were rejected.
- `nix develop <primary> --command python3
  test/p4-oracle/test_replay_contract.py`: exit 0, six offline tests.

Read the full runner and Python driver/tests and both implementation diffs.
Full gate, ordinary CI integration, generated replay and the full corpus
denominator remain separate obligations. The large runtime bundle also
requires a streaming/sharding design before corpus-scale claims.
