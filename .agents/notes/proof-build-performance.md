# Proof build performance

Active until final main CI, 2026-09-28. Retained for review provenance, rejected
experiments and remaining constraints. The public
[N3 performance snapshot](../../docs/performance/n3-iteration-2026-09-28.md)
owns measured artifact behavior and reproduction. This note supersedes the
working reports retained in Git history; it does not claim N3 completion.

## Stabilization and inherited work

Claude's `deaa47a` removed repeated simp preparation and synchronization, including
hoisted audits. An isolated replay against the initial `694e616` artifacts passed
in 173.77s; that timing predates the cache-completeness repairs below and is not the
comparison baseline for the final implementation. The earlier reported 540s to
173s improvement had different build conditions. Preserve those limits.

Codex GPT-6 Astra independently reviewed `694e616`/`deaa47a`, read-only. Across
682 changed generated modules, all 3,894 audits and nonblank non-audit lines were
preserved by hoisting. No kernel-soundness escape was found; four N3 domain
contracts and explicit runtime/extern assumptions remained mandatory. Two
completeness findings required fixes: reducible aliases of discharger assumptions
must enter cache keys, and imported constant inventories cannot use a process-global
prefix-only cache across environments. Local lets, including implementation-detail
lets, can change definitional equality and are retained too.

Generated cleanup now rejects a symlinked library root, skips linked children,
removes only files with the exact generator ownership header, and preserves
handwritten/foreign files. Tests cover those boundaries. Replay and mutations
handle hoisted audits; the stale producer guard and completion manifest were fixed.
The reviewer rechecked these changes with no remaining blocker. Review limits:
no builds by the reviewer and not an exhaustive audit of every earlier N3 tactic.

Stabilization `770e405` passed the full local gate: 1073.97s wall, 4271.05s user,
441.99s system; library/certificates 903s, no skipped stages. It also passed
[CI 36525856029](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36525856029),
whose certificate stage took 2110s. Expected upstream exporter changes remain.

## Kept changes

- `2ee52b9`: source builtin and polymorphic planning use the existing nominal
  representation catalog and produce proof, statement and dependencies from one
  plan. Missing catalog entries fail instead of launching recursive planning.
  The standalone compatibility APIs remain available. Regressions verify the
  callback path and exact existing successful contracts.
- `c5974e7`: discharge-only keys omit direct rigid Eq/HEq/And/Or/True/False heads;
  aliases/unknown heads, every selected rewrite fact and every local let remain.
  Fact lookup builds a fresh name/type map for multiple facts, preserving shadowing,
  order, duplicates and fresh metavariable instantiation. Unfolding-equation matchers
  are realized alongside constructor-equation matchers before downstream proofs.
- `fa522c6`: separate forward/reverse SCC modules with independent callee chains;
  old names remain import-only aggregates. Forward modules omit direct Realize
  imports, although shared extern support may reintroduce that dependency.
  All 3,932 normalized theorem chunks and 4,095 audit names exactly match
  `770e405`, including multiplicities. Replay expands aggregates, requires both
  directional sources and rejects unmatched selectors per requested module.
- `d28d3b8`: opt-in native replay queries Lake for Batteries/core shared libraries
  in load order. Stale/missing artifacts fail under `--no-build`; malformed output
  fails closed. Production Nano library configuration is unchanged.

## Validation and measurements

Parent-owned `nix develop -c /usr/bin/time -l -p scripts/check.sh` exited 0:
835.25s wall, 4437.53s user, 430.68s system; library/certificates 668s. All stages
ran. A warm full gate exited 0 in 118.93s; its main costs were completion/coverage/
quotation 43s, reachability 17s, mutations 16s and completion contracts 12s.
No executable inputs changed after these runs. Fresh text/link checks cover later
performance/state documentation. Logs live under ignored `.artifacts/perf/`:
`codex-stabilization-gate.log`, `codex-optimized-gate.log`,
`codex-optimized-warm-gate.log` and `codex-stabilization-ci.log`.

The same saved combined `bin_op` source passed isolated profiled checks:
conservative baseline 291.29s wall / 465.06s user / 6.66 GB maximum RSS;
rigid-head filter 283.16s / 449.71s; the same filter with native tactics
262.60s / 413.08s (7.3% versus its matching non-native run). These experiments
precede final fact indexing and matcher pre-realization. Profiling phases nest:
simp ~288s and interpretation ~104s are not exclusive wall time. Native loading
removes interpreter dispatch but simp remains dominant.

Three warmed native generator checks were 4.08–4.14s before and 3.93–4.10s after,
all exit 0. Different concurrent process conditions and tiny sample size preclude
a throughput claim. Catalog reuse prevents the future complex-field planning cliff;
current supported signatures barely exercise it. A real interpreted catalog probe
took 21470ms to build the catalog; 1000 repeated `value` field lookups reported 0ms
(timer resolution/possible loop invariance, not a reliable throughput estimate).
Both actual `empty_set --only refines --native` and subsequent native `--no-build`
CLI replays passed, validating the portable loader path.

## Independent final review

A second read-only Codex GPT-6 Astra reviewer reviewed the fact lookup change
(authored by the first reviewer), cache filtering, behavioral regression, catalog
reuse, directional imports/replay, matcher pre-realization and native CLI. No
blocking finding remained. Bounded implementation/tests used GPT-6 Sol agents;
review is AI-agent review, not human review. Reviewers did not run builds.

Pinned Lean's discharger consults local assumptions only for forall-shaped equation
hypotheses, so the six excluded inductive heads cannot match. Review confirmed
unknown/alias heads and selected facts remain. The regression requires an actually
cached imported closed expression, then adds an open equality that enables a
conditional rewrite. A private local marker would not exercise the cache because
harvesting rejects non-imported constants; that test was strengthened before passing.
Other test-only context/hygiene errors were fixed and the focused Lean file passed.

Native loader review checked query order, parsing, missing targets and `--no-build`.
A real initial core-only load crashed because Batteries symbols were absent;
Batteries-before-core passes. Broad production native loading was rejected:
pinned Lake hashes configured dynlibs into every module trace, so changes to any
Codegen module in the core shared library would rebuild all Nano modules.

Documentation review independently recounted 153 paired definitions, 888 obligations,
758 bindings, 130 unbound items and 129 unresolved after CLI-owned source identity.
It confirmed exactly four outstanding N3 domains and distinguished local gates from
remote CI. The final performance snapshot records observations, not clean-build or
runtime-speed claims.

## Rejected approaches and remaining work

Exact structural sharing after simp (32-result epochs) passed in 293.44s versus
291.29s, so it was removed. A one-second stack sample had overemphasized finalization;
the full profile attributed only ~5s to sharing and ~3s to predefinition processing.
The rejected patch and raw trial logs remain ignored, not production options.

Do not omit selected facts just because they cannot rewrite closed terms. A selected
`n = 0` can discharge the open condition of `n = 0 → closedMarker = 0`, changing
an earlier cached failure. Old unpartitioned reuse broke eight certificates.
Closed results also require imported constants because tactic backtracking may
roll back freshly realized constants. Both boundaries remain protected.

The longest chain still includes reverse `bin_eq`, `bin_op`, `Expr_eval` and
`Call_eval`; reverse `bin_op` took 308s during the concurrent optimized rebuild.
Further native build integration needs a narrower tactic artifact boundary, not
whole-core invalidation. Current performance is adequate to resume the remaining
four domain proof shapes using catalog-backed generation. N3 completion still
requires those proofs, strict owned-obligation validation and final review.
