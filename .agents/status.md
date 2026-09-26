# Status

Current state only; git history is the archive. Updated 2026-09-25.

## Goal and authorization

M1/M2 and M3A are closed. **M3 is incomplete and its broad expansion is
paused.** The user authorized the bounded Nano field-update consumer proof
on 2026-09-25 after a design review. The contract is two-way terminating
correspondence on a declared scalar source domain plus distinct-field
commutation transferred to the reference. This example does not complete M3.
No correctness gate is waived.

## Completed field-update implementation

Worktree `/Users/qobilidop/my/work/p4-spectec-lean-field-update`, branch
`nano-field-update`, based on published PR #26 merge `fdb8a8d`. The primary
worktree's uncommitted design-review changes are untouched.

Agreed layout: handwritten `NanoP4Proofs/FieldUpdate/` with checked
`Example.lean`, root library, and normal build/import gates. No separate
field-update test module or Markdown tutorial. Independent scalar source
grammar includes W/S/B/MATCH_KIND and ordered finite field lists, preserving
duplicates and absent-key identity. It is a shape profile, not a typing or
range theorem; no nested-payload, extern, printing or parser claim.

Representation coverage, sufficient-fuel decoder round trips and observation
injectivity pass. General generated-operation semantics and commutation pass.
Concrete Nano initialization is proved using logical map laws, not native
hashing. Forward soundness and actual-reference reverse realization now pass,
including a structural finite-fuel bound of `7 * length + 33`. The final
consumer proves reference observation equivalence at distinct field names,
with a separate existence theorem: no termination or initialization premise.
All advertised theorems have exact core-three axiom guards.

Evidence so far, in the pinned Nix shell:

- Domain build: exit 0, 18 jobs; representation build: exit 0, 57 jobs.
- Semantics/Laws build: exit 0, 76 jobs; combined new library: exit 0,
  87 jobs; final complete proof library: exit 0, 89 jobs.
- Direct representation and forward-reference proof checks: exit 0,
  including exact core axiom audits.
- Quotation check: all 342 definitions match the checksum-verified export.
- Final complete `scripts/check.sh`: actual exit 0, no skips,
  recorded in `.artifacts/field-update-final-gate.exit` (session 33622). Both
  78-program differential legs and all 48 output contexts agree.
- Independent representation, environment, semantics, correspondence,
  final consumer and wiring reviews have no findings. Reports are
  `.agents/reviews/field-update-*.md`.

Implementation, independent review and final local validation are complete.
Publication and final-head remote CI remain owed. No further implementation is
active; finish publication, then stop at this checkpoint. Broader M3 stays paused.

## Published baseline

Main `fdb8a8d` contains reviewed, locally gated and remotely green bounded
checkpoints through PR #26: byte-preserving text and state foundations,
bounded generator/refinement fixtures, checked type-runtime outcomes,
full-P4 upstream oracle and interpreter replay, corpus inventory/worker/shards,
partial dynamic Nano target and packet driver, and shared verify.

PR #26's final remote Gate `36218916889` passed on `c7172f3`.
Published gates do not validate unpublished production full-P4 generation.
The baseline Nano comparison covers 78 verdicts (48 pass, 30 fail), 48
successful output contexts, and 342 source quotations. General mutation,
whole-corpus, whole-program and complete packet/target claims remain open.
Detailed bounded evidence remains in the corresponding notes/reviews; git
history archives completed progress reports.

## Paused broader work

- Production tree: `/Users/qobilidop/my/work/p4-spectec-lean-state-production`,
  branch `m3b-state-production`, pause handoff `925fdbf`, latest source
  integration `1b2ac70`. Full-P4 regeneration produces 74 files, but the
  complete build fails: `Cast_expl.run_sound_group` exceeds the unchanged
  4M heartbeat budget. Focused checks are not a full-build verdict.
  Production reconciliation with later published Nano checkpoints is owed.
- Corpus tree: `/Users/qobilidop/my/work/p4-spectec-lean-p4-corpus-replay`,
  frozen `c4a8858`. The campaign stopped with exit 130 after shards 0–44:
  180 attempts, 338 AL matches, eleven retained oversized-artifact failures.
  These are handoff totals, not a whole-corpus result. Do not restart or
  reinterpret partial evidence.
- The primary worktree's separate design-review documents remain user-owned.
  Do not replace them with this isolated branch's baseline documentation.
- Future scope and exit criteria remain in `docs/design.md`,
  `.agents/roadmap.md` and `.agents/notes/full-p4-reconnaissance.md`.
  The census describes decoded/emitted capabilities, not full-P4 elaboration.
  Nonempty observable FuncT substitution, guarded higher-order fidelity,
  hinted-print refinement, complete targets and broader determinism remain
  explicit limitations; consult decisions before changing their contracts.

## Hygiene and handoff

Every command uses the pinned Nix environment. Preserve the expected patched
upstream files and separate worktree caches. Raw spec JSON is ignored and
checksum-verified; do not commit logs, scratch output or duplicated corpora.
Tracked/indexed files must stay below 5 MiB.

Freeze implementation during the final full gate and record its actual exit
before pushing. Independent review and final-head remote CI remain required
by the current publication policy. No external blocker requires user input.
