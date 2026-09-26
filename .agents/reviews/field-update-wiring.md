# Field-update build and documentation wiring review

Independent read-only review by the oracle agent, 2026-09-25, of the current
field-update worktree changes in `lakefile.toml`, `NanoP4Proofs.lean`,
`scripts/check.sh`, `AGENTS.md`, and `.agents/decisions.md`. Only this report
was written; no semantic module, build output, or gate was changed.

## Findings and coverage

No findings in the reviewed wiring.

The new `NanoP4Proofs` library is registered once and added to the existing
default targets, rather than replacing any target. Its root explicitly imports
all six currently present modules: Domain, Representation, Semantics,
Environment, Laws, and Example. Ordinary `lake build --wfail` therefore
elaborates these proofs and their exact axiom-message checks. The gate also
requires the proof root and includes the library in `check-imports.sh`, so a
future unimported module cannot silently evade the build.

No separate test module is needed for the current proof-only interface: the
theorems and boundary examples are checked during default elaboration, their
axiom sets are checked in-module, and the existing test driver and `lake test`
remain unchanged. This does not forbid adding executable/regression tests if
the interface later includes non-proof behavior requiring them.

The `check.sh` diff is strictly additive: one required root path and one
library argument to the import-coverage check. Existing build/test/oracle,
snapshot, hygiene, failure propagation, and explicit skip behavior are
unchanged. No new upstream execution, network request, optional semantic
check, or suppression was introduced.

`AGENTS.md` points to the handwritten bounded proof/walkthrough location.
The decision entry records the intended scalar correspondence and transferred
law as this milestone's scope, not as completed evidence. It preserves
duplicates, first-match and absent-key behavior, representation/environment
obligations, and the distinction from arbitrary assignment reordering or
full-P4 certification. It explicitly keeps broader M3 paused.

Correspondence does not yet exist at this review point. Adding its explicit
root import remains pending when the module is created; the current six-module
coverage check does not claim that reverse correspondence is already built.

## Focused validation

All commands ran inside the pinned Lean Nix shell with the field-update
worktree as working directory:

- `bash -n /Users/qobilidop/my/work/p4-spectec-lean-field-update/scripts/check.sh`: actual exit 0.
- `scripts/check-imports.sh P4SpecTec P4SpecTecTest P4Lib NanoP4Spec P4Spec NanoP4Proofs`
  (invoked by absolute path): actual exit 0.
- Python `tomllib` parse/assertions: actual exit 0; one registered default
  proof library, existing `P4SpecTecTest` driver retained, six current modules.
- `git diff --check -- lakefile.toml scripts/check.sh AGENTS.md .agents/decisions.md`:
  actual exit 0.

No concurrent Lake build or full gate was run. Prior semantic reviews and
root's focused library build are separate evidence.

## Status compaction follow-up

Independently reviewed only the compacted `.agents/status.md` against its
prior Git version, production pause handoff `925fdbf` and latest production
source integration `1b2ac70`. The reduction removes archived chronological
progress, not a claimed new milestone. The active scalar profile, actual
initialization/forward evidence, pending reverse realization/reference
commutation, and required final review/full gate/publication remain explicit.
The preliminary gate is correctly separated from pending reverse integration.
The primary tree's uncommitted design work remains protected.

The paused production summary accurately preserves the second casting-group
4M-heartbeat failure and unpaid combined/full-build/reconciliation obligations.
Published bounded gates are not promoted to unpublished full-P4 certification.
The detailed paused obligations and exact resume procedure remain recoverable
from the referenced production handoff and Git history.

One narrow wording correction was requested: replace corpus "eleven oversized
inputs" with "eleven retained oversized-artifact failures". The failure
classification concerns retained bounded-artifact outcomes, not proof that
eleven source input files are oversized. The recorded 180 attempts / 338
matched comparisons are authoritative retained totals including the separately
validated final shard, not the campaign ledger totals. The pause handoff
records this distinction: the ledger still has 44 rows / 176 attempts / 330
comparisons, with shard 44 awaiting exact-resume reconciliation. Compaction
need not reproduce all of that runtime detail, but it must not reinterpret
the failures as matches or claim the campaign completed.

Read-only checks confirmed accessible corpus HEAD
`c4a8858a9b87c5466c70784040bfcd53fa895e36` is clean, actual batch exit is 130,
and the ledger retains those 44/176/330 counts with eleven oversized failures
and `completeCanonicalAttempts: false`. The additional shard-44 retained
counts are supported by the durable pause handoff and the earlier independent
paused-boundary validation, not by pretending the ledger already contains it.
The field-update preliminary gate `.exit` file independently reads 0.
No process, corpus run, build, or external-tree edit was launched by this review.

Root corrected the wording and explicitly labeled the retained totals as
handoff totals; the reviewer reread those lines. The finding is closed, with
no remaining status-compaction findings in this scope.
