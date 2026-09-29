# Status

Active autonomous stabilization and performance work, updated 2026-09-28.
The user requested a passing local gate and CI before further optimization,
then measured improvements to the remaining N3 iteration workflows.
The current `n3-perf` tree passes the full local gate; publication and CI are next.
It contains the work on `n3-core`; `main` still holds the first N3 checkpoint.
N4–N6 have not started and full-P4 M3 remains paused.

## Verified checkpoint on `main`

N0/N1/N2 are complete (closure `d85e82c`, CI 36316496027). The first N3 checkpoint
(68 of 153 bodied definitions two-way) and the replay tooling are on `main`, with
passing full local gates; details in the
[Nano plan](notes/nano-certification.md#n3-first-checkpoint-in-progress).

## Work in progress on `n3-core`

The branch contains WIP checkpoints and merges `n3-runtime` (`be20c38`, `c2a5f04`,
delegated to a subagent). These commits are now published: preserve their history.
Integrate only after validation and review, with the incomplete N3 scope explicit.

- Refinement: every one of the 153 bodied definitions is admitted and emitted with
  forward and reverse theorems (extern-dependent ones under the abstract
  `externsContract`). All certificates and tests passed the full local gate on
  2026-09-28, including the generated runtime-domain claims.
- Domain evidence: the evaluation side uses the runtime-inclusive profile (decisions,
  "Runtime-inclusive evaluation domain"). The manifest accepts complete evidence from
  one profile. After regenerating with the current generator, the N3-owned inventory
  (`--require-owned N3`, unchecked mode) lists only `domain` for `ite`, `repeat_`,
  `empty_set`, `empty_map`, plus `sourceIdentity`, which the completion CLI checks
  itself. The refreshed completion manifest and bounded N2 checks pass; broader
  core/target/release obligations remain incomplete. The stale producer guard,
  obsolete generated modules, and source/generated line-length failures are fixed.
- Parked: constant/selection polymorphic domains for `empty_set`, `empty_map` and
  `ite`. Hand prototypes prove the outputs (`simp only [f] at run` then
  `simp [set.admitted]`; `cases p0 <;> simp [f, Eval.check] at run <;> subst run;
  assumption`), but routing them through `SourcePolymorphic.field` made the generator
  run the uncached recursive `RepresentationCertificates.plan` for 20+ minutes; the
  change was reverted. Resolve their fields from the catalog instead. `repeat_` (a
  recursive list builder) needs a `partial_correctness` proof shape.

## Proof-build performance on `n3-perf`

Claude's `deaa47a` removed synchronization and repeated simplification work. A fresh
isolated `bin_op` check against those tactic artifacts passed in 173.77s. Independent
review then found two tactic-completeness issues in its caches; those are fixed and
covered by regressions. Replay and mutation tools now handle hoisted audits.

`nix develop -c /usr/bin/time -p scripts/check.sh` exited 0 on the stabilization tree
(1073.97s wall, library/certificate build 903s). No gate was skipped. Evidence is
`.artifacts/perf/codex-stabilization-gate.log`; review and measurement limits are in
[the performance note](notes/proof-build-performance.md). The rebuilt `bin_op` took
316s, so recovering performance with the corrected caches is an explicit next task.
CI now covers pushes to `main` and `n3-*`; this checkpoint's CI is not yet observed.

## Resume point

0. Publish the reviewed stabilization checkpoint and require passing CI. Preserve
   that run while measuring performance experiments on a separate `n3-*` branch.
1. Reuse the representation catalog for domain planning; measure proof finalization,
   structural sharing and independent forward/reverse dependency chains. Preserve
   statements, audits and all validation requirements.
2. After performance work, the four polymorphic domains above; then run
   `nix develop -c python3 scripts/nano-certification.py --update` and
   `--require-owned N3`.
3. Update the Nano plan's N3 section and `docs/certification.md` to the delivered
   claims, run `nix develop -c scripts/check.sh`, get an independent review, then
   integrate into `main` without rewriting published commits.

Iteration: `scripts/replay-cert.py` in the main tree with `--no-build` after
`lake build P4SpecTec` (never while a full build runs there); it is faithful only for
tactic-only changes. Generation takes seconds; minutes mean a generator regression.
`replay-cert.py --only` now preserves each selected theorem's hoisted audit.

## Maintenance and repository state

Worktrees: main (`n3-perf`) and `../p4-spectec-lean-replay` (scratch replays,
detached, disposable). Local branch `n3-runtime` is merged into `n3-core`; delete it
with the other feature refs after integration. Older local branches `n3-decl-load`
and `n3-expr-eval` are superseded by `n3-core`. The expected upstream exporter patch
remains applied. No source pins changed.
