# Status

Current checkpoint, updated 2026-09-26.

## Authorized scope

The user approved the [code/test organization refactor](notes/code-organization.md)
and explicitly authorized execution. It takes priority over Nano implementation:
concrete library boundaries, nearby related code/tests, shared harness plumbing,
responsibility-based module splits and evidence-backed test consolidation.
The refactor is published as `ad1ac33`; its full local gate passed with exit 0
(session 65742, no skips), and exact-head CI 36280484313 succeeded. The user
additionally authorized a bounded configuration/import-ordering cleanup while CI ran.
The follow-up passed independent Sol review and the full local gate (session
61425, exit 0, no skips); publication CI remains to be verified. The user requested
`tend-repo` after committing it. Nano proof implementation remains paused and incomplete.

Autonomous implementation of the [Nano certification plan](notes/nano-certification.md)
is approved, with both core and target stages required by
[Design section 9](../docs/design.md#9-nano-p4-scope-and-acceptance).
N0 is complete; N1 remains active and incomplete. Broader full-P4 M3 stays paused.
Luna performed the inventory, Sol implemented corpus/packet tests, and Astra
handled proof work and independent review; root integrated the changes.

## Delivered and checked

- Code/test organization: four nonempty library targets, supported CLI roots in
  Tools, Lean tests grouped by ownership, colocated oracle suites, shared probe
  plumbing, separated compiler/certificate/proof responsibilities, and checked
  library layers/reachability. No generated Nano output or oracle payloads
  changed; only duplicated infrastructure checks and the trivial Smoke test
  were removed. Independent Sol/Astra reviews have no outstanding findings.
  Exact scopes, hashes, capture checks and limits are in the
  [organization evidence](notes/code-organization.md).
  `nix develop -c bash scripts/check.sh` passed with actual exit 0, no skips;
  log `.artifacts/code-organization-final-gate.log`, session 65742. All 78
  programs agree on both differential legs. Completion remains 350 declarations,
  888 obligations, 95 bindings and 793 unresolved. No full-P4 campaign was run.
  Exact-head [CI 36280484313](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36280484313)
  succeeded for `ad1ac3310e034494fa05bdbcdac395b5053860de`.

- `35bda29`: complete Nano obligation and pinned corpus inventories. There are
  350 declarations, 888 obligations, 95 existing compiled bindings and 793 open
  obligations. All 78 programs and 39 STF sessions remain in the denominator.
  Completion/corpus tests pass (15/19); strict completion correctly fails.
- `f6d1b05`: reusable eventual reverse-realization rules, with 31 audited library
  and test theorems. The combined full gate passed (session 77137,
  `.artifacts/nano-n0-realize-gate.log`). Both commits are published; exact-head
  [CI 36276724234](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36276724234)
  succeeded.
- `9309e26`: no-hint printer congruence; independent decoded/compiled Nano
  empty-hint checks; raw-extern representation obstruction proofs; actual
  short/full extract continuation and distinguishing PACKET-rewrap mutation.
  Independent reviews have no remaining findings. Full gate passed with actual
  exit 0, no skips (session 8909, `.artifacts/nano-n1-target-print-gate.log`).
  Exact-head remote
  [CI 36277488013](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36277488013)
  succeeded; the implementation publication obligation is closed.
  Final documentation-only handoff edits receive text/whitespace checks;
  publication CI must match the final checkpoint SHA in
  [main CI](https://github.com/qobilidop/p4-spectec-lean/actions/workflows/ci.yml).

These changes do not increase generated Nano coverage: still 18 forward
certificates, 77 relation run-soundness theorems and no generated reverse
certificates. Full source/representation, builtin, initialization, target and
corpus-completion obligations remain open. The bounded field-update consumer
and [generic coverage increment](notes/coverage.md) remain complete.

## Immediate next step

Commit the validated ordering cleanup, then perform the requested `tend-repo`
consistency, compaction and learning pass. Verify publication CI. Keep Nano proof
work paused during maintenance; its next implementation step is below.

Finish the actual exists_ reverse induction from local unpushed branch
`wip/nano-reverse`, commit `efd626c7cb40004f8d6725f2b29172d09ecd8dbe`.
Its `.agents/notes/nano-reverse-proof/README.md` describes the checked clause
proofs and the unverified full draft. The [Nano handoff](notes/nano-certification.md#n1-recursive-proof-handoff)
records hashes, independent review, measured cost and the remaining outcome/fuel
composition. The branch has no passing full gate and must not be published as
complete; its temporary worktree was removed. Preserve main's status when
integrating the proof later.

Then exercise Type_eq/ParameterType_eq and prove the faithful raw-extern runtime
representation contract. The current generated value type cannot represent
extract's result; no replacement has been adopted. Printing at this pin requires
an explicit empty hint environment, now supported by a checked generic theorem.
The internal-fuel probes found no in-profile counterexample, not a general safety
proof. N1's full exit criteria still block broad proof generation.

The expected four-file upstream exporter patch remains applied. No submodule
pins changed. The older docs/repository-review branch and archive recovery
artifacts were not removed; [archive recovery](notes/archive.md) retains their
boundaries. No background verification processes remain from the proof attempt.
