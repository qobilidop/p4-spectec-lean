# Status

Session handoff, updated 2026-09-28. N3 is authorized and in progress on the local
feature branch `n3-core` (not pushed); `main` still holds the first N3 checkpoint.
N4–N6 have not started and full-P4 M3 remains paused.

## Verified checkpoint on `main`

N0/N1/N2 are complete (closure `d85e82c`, CI 36316496027). The first N3 checkpoint
(68 of 153 bodied definitions two-way) and the replay tooling are on `main`, with
passing full local gates; details in the
[Nano plan](notes/nano-certification.md#n3-first-checkpoint-in-progress).

## Work in progress on `n3-core`

Every commit on the branch is WIP (its message states what it holds and lacks); the
branch merges `n3-runtime` (`be20c38`, `c2a5f04`, delegated to a subagent). The history
must be squashed into coherent commits before `main`.

- Refinement: every one of the 153 bodied definitions is admitted and emitted with
  forward and reverse theorems (extern-dependent ones under the abstract
  `externsContract`). The last full `lake test` (2026-09-28, local, not the gate)
  built every refinement certificate and the whole test library; its only failures
  were eight runtime producers of extern-dependent relations missing the `Externs`
  binder, fixed in the generator since.
- Domain evidence: the evaluation side uses the runtime-inclusive profile (decisions,
  "Runtime-inclusive evaluation domain"). The manifest accepts complete evidence from
  one profile. After regenerating with the current generator, the N3-owned inventory
  (`--require-owned N3`, unchecked mode) lists only `domain` for `ite`, `repeat_`,
  `empty_set`, `empty_map`, plus `sourceIdentity`, which the completion CLI checks
  itself. The latest generated claims are **not compiled yet**: runtime producers
  with the `Externs` binder, per-output producers for multi-output relations, call
  admission with deep alias resolution (`find_var_t/e`, `write_value_*`), and the
  extern relation's runtime entry.
- Parked: constant/selection polymorphic domains for `empty_set`, `empty_map` and
  `ite`. Hand prototypes prove the outputs (`simp only [f] at run` then
  `simp [set.admitted]`; `cases p0 <;> simp [f, Eval.check] at run <;> subst run;
  assumption`), but routing them through `SourcePolymorphic.field` made the generator
  run the uncached recursive `RepresentationCertificates.plan` for 20+ minutes; the
  change was reverted. Resolve their fields from the catalog instead. `repeat_` (a
  recursive list builder) needs a `partial_correctness` proof shape.

## Proof-build performance on `n3-perf`

Branch `n3-perf` (local, not pushed) holds a WIP commit on top of `n3-core` that
roughly halves certificate rebuild latency: critical path 20.5 → 10.9 min, and
`bin_op` 540 → 173s. See
[the performance note](notes/proof-build-performance.md). The certificate build
passes. The full gate still fails in "Certificate replay contracts" and
"Field-update mutation runner contracts", because both scripts assume an audit next to its
theorem. Two later stages and the WIP's own failures are also still open. Next step: update
`scripts/replay-cert.py` and the mutation runner for hoisted audits, rerun the gate,
then merge `n3-perf` into `n3-core`.

## Resume point

1. `nix develop -c lake test`; fix the new domain modules it reports.
2. The four polymorphic domains above; then run
   `nix develop -c python3 scripts/nano-certification.py --update` and
   `--require-owned N3`.
3. Update the Nano plan's N3 section and `docs/certification.md` to the delivered
   claims, run `nix develop -c scripts/check.sh`, get an independent review, squash
   the WIP history into coherent commits, then integrate into `main`.

Iteration: `scripts/replay-cert.py` in the main tree with `--no-build` after
`lake build P4SpecTec` (never while a full build runs there); it is faithful only for
tactic-only changes. Generation takes seconds; minutes mean a generator regression.

## Maintenance and repository state

Worktrees: main (`n3-perf`) and `../p4-spectec-lean-replay` (scratch replays,
detached, disposable). Local branch `n3-runtime` is merged into `n3-core`; delete it
with the other feature refs after integration. Older local branches `n3-decl-load`
and `n3-expr-eval` are superseded by `n3-core`. The expected upstream exporter patch
remains applied. No source pins changed.
