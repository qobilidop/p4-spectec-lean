# Nano-P4 release evidence (N6)

Durable, closed 2026-09-30: retains N6's evidence, scope audit, costs and review record, which
`nano-release.json` cites as the release's review record; supersede it with the next release. The user-facing
account is in [Certification](../../docs/certification.md#distinguishing-mutations); the
record format's rationale is in [decisions](../decisions.md) ("N6 release evidence").

## What is established

- `P4SpecTecTest/Oracle/Nano/Certification/mutations.py` (with `test_mutations.py`): five
  cross-layer mutations, each rejected by a named check, the two code mutations after first
  changing a runtime result (ordering and
  failure kind by the replayed forward proof of `$expression_is_lvalue`; an omitted
  constructor and a changed premise by quotation comparison; a print hint by `check-quotes`'
  empty-hint check). Corrupted target state is the source-address filter's `extern`,
  `receiver` and `state` cases.
- The plan named a "hard-error retry" mutation, meaning code that retries past an error.
  No generated function reaches a hard error inside an earlier alternative of a
  mutation-friendly definition (in `$expression_is_lvalue` each `Eval.err?` follows its
  guard and cannot fail), so a retry mutation would be unobservable. `failureKind` instead
  tests the same boundary in the other direction: a mismatch the interpreter retries past
  becomes an error, and the replayed proof rejects the differing failure kind. Revisit if a
  generated definition with a reachable error in an earlier alternative becomes convenient.
- `scripts/nano-certification.py` binds `profile:sensitivity` to running all three mutation
  suites, and `profile:review`/`profile:release` to `nano-release.json` for the matching tree
  digest. The gate runs `--require-n2 --require-complete all --allow-unpublished`.

## Scope audit (2026-09-30, `4e2555a`)

The regenerated manifest has 350 declarations, matching the export kind for kind (161 `TypD`,
1 `ExternTypD`, 77 `RelD`, 76 `FuncDecD`, 26 `BuiltinDecD`, 8 `VarD`, 1 `ExternRelD`), and 888
obligations, the N0 baseline: 153 forward and 153 reverse, 77 soundness, 180 domain, 163
representation, 26 builtin, 8 variable, 117 replay (78 typing, 39 packet), one each of
extern, initialization, source identity, target, observations, printing, composition,
consumer, sensitivity, review and release. 762 obligations are bound to a compiled claim
only, 121 to a checker run only, and 5 to both (the target claims and the consumer); none is
unbound. Scope has not narrowed.

## Validation and costs

- `868cc81`: full `nix develop -c /usr/bin/time -p scripts/check.sh` returned actual exit 0 in
  255.46s, all 49 stages (`.artifacts/n6-gate-1.log`): combined completion with 0 unresolved
  and the two publication records pending, and all three mutation suites (141s stage).
- Costs are in `docs/performance/nano-release-2026-09-30.md`; no regression against N3.

## Review record

- `551df89` (with uncommitted `.agents/` edits): independent read-only review (Claude Opus 5.5
  subagent, no builds). No blockers. The reviewer independently regenerated the manifest and
  confirmed the scope audit. Findings and resolutions:
  - Release record not bound to its revision (a digest could be carried forward): the checker
    now recomputes the digest from the recorded revision's own objects and requires the review
    record file (`a146d78`).
  - README and guide overstated what the gate checks, and the mutation table named
    `check-consumer`/`check-quotes` where copies or `compareSpecs` run: reworded, trust table
    extended, the guide no longer names a working-state path (`868cc81`).
  - Hard-error retry mutation replaced without a reason: recorded above.
  - Stale status, decisions and AGENTS rows; performance snapshot and AGENTS edits must precede
    the reviewed revision: fixed, snapshot committed in `5ebec11` before the final review.
  - Nits resolved: the replayed proof now keeps its generated 8M heartbeat budget; plain
    completion runs skip the mutation suites; the allowance filter has a contract test.
    Not changed: index-mode digest (chmod-only changes are unseen; Git tracks only the
    executable bit, which the index records), the legacy corpus identity path (pre-existing,
    mapped by `source_path`), and `.agents/notes/p4-census.json` outside the digest (full-P4
    only).
- `d5c4b17`: delta review by the same reviewer. It confirmed findings 2–5 and the nits
  resolved or justified, and the snapshot figures against the artifacts. It found that the
  recorded revision could be any tree-ish (`HEAD` would follow the checkout): now a
  verified full commit id is required (`5eefa3f`). Nits resolved in `883ebca` (run order,
  attributions) and here (the print mutation is not claimed observable). Missing objects in
  `cat-file` output fail closed with a traceback; left unchanged.
- `42ffad6`: release CI 36696461554 for `a65c265` failed in one stage: the cross-layer
  contract tests read the extracted export before the gate's snapshot stage creates it (a warm
  local copy hid this). `42ffad6` runs that stage after extraction; the same reviewer found no
  other warm-artifact dependency and no unresolved findings.

## Release

`42ffad6`: full gate with the extracted exports removed first returned actual exit 0 in 219.95s,
all 49 stages (`.artifacts/n6-gate-4.log`); exact-revision
[CI 36697907550](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36697907550) passed.
`nano-release.json` records both for tree digest `4432d6a5…`.
