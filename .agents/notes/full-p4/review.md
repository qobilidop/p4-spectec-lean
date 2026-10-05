# Full-P4 retained review evidence

Compacted 2026-09-26 from independent read-only AI-agent/root reports dated
2026-09-25. This is historical evidence, not a new semantic review or gate
run. No remaining findings were recorded within the bounded reviewed scopes.
All original reports remain at `968ad65:.agents/reviews/<name>.md`.

Named reviewers: `review_export` authored `m3a-export`, `review_census`
authored `m3a-census`, and `review_quotes` authored `m3a-quotation`.
The state/target agent authored `m3c-corpus-shards-recovery` and then its
hardlink fix, so post-fix checks there are author evidence. The separate
hardlink review covers that fix independently. `m3c-shards-nano-reconcile`
records Codex GPT-6 Sol as reviewer. “Root” below denotes the historical
coordinator, not the author of this compaction.
The executable-codegen agent reviewed `m3c-p4-oracle-adapter`.
Codex `state_codegen` reviewed `m3c-corpus-gate` from `e31c1e8`, gate blob
`928e81e856078bd1eed8a12263b0c4b50a9be05c`.
Codex GPT-6 Sol reviewed the `state_props` hardlink fix in
`m3c-probe-workspace-hardlinks`, excluding its own earlier workspace-key option.

| Original report(s) | Findings resolved and evidence retained |
|---|---|
| `m3a-export` | Sorted upstream traversal/all 108 regions verified; two independent exports byte-matched Nano and P4. Snapshot corruption/truncation/checksum failures preserve cache and stop gate; size guard tests passed. No quotation/full gate review. |
| `m3a-census` | Raw recursion distinguished from emitter mutual blocks; 15 aliases in six groups corrected. Census `--check` passed; counts independently matched. First-error/text-only qualifications required; no full-P4 build. |
| `m3a-quotation` | Gate must execute checker, not only build it. Type/callable namespace fix and all 342 Nano quotations plus QuoteChecks passed. No full-P4 quotation/census/full-gate claim. |
| `m3c-corpus-prep` | Corrected empty-submodule parent-HEAD confusion, exact p4c pin, independent relation sessions and pinned config/symlink/error checks. Root reran ten restore tests and real idempotence (1,352 paths), not initial network fetch. |
| `m3c-p4-oracle-adapter` | Four medium findings fixed at `997d0ab`: stale/dirty linked-source provenance, semantic-text normalization, fail-open manifests/envelopes and crashes accepted as negatives. Independent twelve tests and four cases/eight CLI checks passed. v1 envelope check is not recursive IL typing; later Lean decode is separate. |
| `m3c-p4-interpreter-replay` | At `a4c907b`/`5657373`, corrected syntax-envelope bypass and wrapping counter seeds. Independent six real matches, syntax-only case, nine specific Lean mutation rejections and six offline tests passed. Placeholder externs audited; no packet/generated/corpus claim. |
| `m3c-replay-gate` | Required paths/offline tests/build failure propagation reviewed; six tests and shell syntax passed. Integration preserved `5657373` source; real upstream replay not rerun for unchanged merge. |
| `m3c-corpus-inventory` | Independently reproduced canonical 1,267 candidates, eighteen omitted helpers, 67 exclusions. Five tests including thirteen corruptions and fresh exact-pin inventory passed. No execution/resume claim. |
| `m3c-corpus-worker` | Worker initialization moved inside durable reporting lifecycle. Root independently passed seven tests and full v2 pilot `98530`: six AL matches, syntax-only case, eight CLI checks, sixteen mutations and subsequent valid replay. No shard/full gate claim. |
| `m3c-corpus-gate` | Nine required paths, five/seven unconditional offline tests and worker build propagate failure. Independent tests/syntax passed; no fetch/network/real pilot introduced. |
| `m3c-corpus-shards` | Root reviewed exact identity, terminal/recovery accounting, artifact-first quarantine, final-worker failure and null byte metrics. Sixteen tests and final-helper exact resume `901d53d9` independently passed. No full corpus/generated leg claim. |
| `m3c-corpus-shards-recovery` | Reviewer found hardlink cache overwrite risk, then authored fix; its post-fix tests were author evidence. Original independent fourteen-test recovery review found no other issue. Exception/state-transition injection is not a power-cut test. |
| `m3c-probe-workspace-hardlinks` | Separately authored fix independently reviewed on helper blob `fbabd5fabe16ffcf77729f2d604e4ee3229f81eb`, tests `045382787a6456b481114df1486b0de28a4e2735`; sixteen/seven/twelve tests passed. Reviewer authored earlier workspace-key option, so independence covers only this safety follow-up. Cooperative locks only; no real shard/full gate/CI. |
| `m3c-shards-nano-reconcile` | Shard source unchanged from `2fbe024`, Nano source unchanged from `186d43a`; combined wiring and sixteen/ten offline tests passed. Lake changed hashed identity: earlier `901d53d9` cannot resume as this revision. Reviewer later inspected root's recorded gate exit 0/no skips, without rerunning it. |

The full local gates recorded for oracle publication, replay integration,
worker integration, final shard helper and shard/Nano reconciliation exited
0 without skips. This does not revalidate the present tree. Known historical
remote Gate evidence includes oracle run `36205678753` (1m52s), replay
`36209104840` on `94fd99e` (4m53s), and PR #22 `36213412457` on `93a2e8c`
(3m43s). Original reports explicitly left subsequent merged-head CI to the
publication owner; these reviews alone do not establish those later outcomes.
Current publication state belongs in status and must be checked separately.

The retained engineering constraints from these reviews live in
[corpus](corpus.md) and [overview](overview.md). Historical ignored logs,
temporary review scripts and secondary-worktree observations are not assumed
recoverable; committed source/report history is. None of these checks closes
the failed aggregate casting proof, full denominator, generated replay,
guarded type-fresh semantics, targets or all-definition certification.

## Executable generation stage (2026-10-04)

Independent read-only review of the uncommitted `m3b-generation` tree against `main`
(`cd6679e`), by a fresh Claude Fable 5.1 subagent that ran no build: it read the diff, the
generated `P4Spec/` text and the recorded gate log, and ran only the manifest check.
Verdict: no blockers. It confirmed by reading that pure-mode planning is unchanged, that
the explicit-state plan skips no bookkeeping, that the tuple encoder and decoder are
inverse for every admitted shape, that the replay refactor preserves the interpreter
leg's checks, and that the generated leg's externs match the interpreter's placeholders.

Findings and resolutions, all applied before the commit:

- The replay claim counted the rejected program (`issue-204.p4`) as returning upstream's
  outputs; any Lean failure matches there. Reworded in README, Certification, status and
  the overview, and the generated legs now require the decoded program to encode back to
  the booted value, so a rejection is about the same input.
- AGENTS said no committed library may import `P4Spec`, while the checker constrained only
  reusable libraries. Added a rule and test: a consumer library root must not reach
  ignored generated sources; only registered executables may.
- Stale "paused" and "no full-P4 quotation" sentences in three notes: rewritten.
- Latent: certificate groups hard-coded an import of the equality module, which an
  explicit-state library does not emit; now conditional. The generated `Refinement.lean`
  header no longer speaks of refinement theorems for a library without any.
- Not changed: `ctorNames` has no distinctness check (a clash with a real constructor
  named like a suffixed one fails loudly at elaboration); `validateTuples` does not expand
  generic tuple aliases (none exists at the pins; noted in its docstring).

Limits the reviewer stated: the recorded gate was warm for `P4Spec`; byte-identical
generation and a cold build on Linux are untested until CI runs; instance-resolution
arguments were made by reading. The resolutions above were checked by the author's
rerun of the full gate, not re-reviewed.

## Corpus sweep stage (2026-10-05)

Independent read-only review of the uncommitted `m3c-corpus` tree against `main`
(`6e57dcb`), by a fresh Claude Fable 5.1 subagent that ran no build: it read the diff and
the pinned OCaml, ran `test_sweep.py`, and checked the logs and summary. Verdict: no
defect producing false agreement and no faithfulness defect in the placeholder port. It
traced upstream's failure paths (`error_no_region` to an abort that nothing in the
interpreter catches; a failed callback to a mismatch through `call_func`) and confirmed
the port's `Fail.err`/`Fail.unmatch` choices, the trampoline wrapping in both upstream
runners, value shapes and evaluation order, and that `Corpus/Check.lean` preserves every
check of the old worker.

Findings and resolutions, applied before the commit and checked by the author's rerun of
the gate and the sweep, not re-reviewed:

- Blocker (policy): status had dangling evidence references and no gate, replay or review
  record. Rewritten.
- The generated externs decoded callback arguments inside the wrapper that turns callee
  failures into mismatches, so a codec failure would have looked like a semantic
  mismatch. Decoding is now outside it and stays a hard error.
- `sweep.py` could exit 0 with capture failures that were not bounds, or with nothing
  evaluated; its cache identity omitted the harness sources; an unexpected exception in a
  worker thread lost the record and left the worker running. Fixed, with fake-worker
  tests for crash, timeout, wrong name, error line, malformed answer and recycling, and
  `--retry-unobserved` for sticky failed captures.
- The public mutation sentence read as a standing property. It now says one manual run,
  generated leg, 1,186 programs, no committed suite. The failed branch of
  `static_assert` is stated to have no upstream evidence.
- Nits applied: MiB units, the placeholder header and `Make.lean` sentence, a repeated
  `--max-case-bytes` is rejected, worker digests are taken before the legs and rechecked,
  jobs and the recycle bound are recorded.
- Not changed: `shard.py` and `campaign.py` source digests still name `Corpus/Main.lean`
  only (the worker executable digest covers `Check.lean`); `--max-case-bytes` has no
  upper bound (an absurd value fails closed at the size check).

Limits the reviewer stated: nothing was built or run beyond the unit test; codec
correctness for `typingContext` rests on the two `static_assert` programs now matching.

## Logical relations stage (2026-10-05)

Independent read-only review of the uncommitted `m3b-relations` tree against `main`
(`f329af0`), by a fresh Claude Fable 5.1 subagent that ran no build: it read the diff and
ran read-only checks over the generated `P4Spec/` text, `coverage.json`, the export and
the manifest. Verdict: no blockers; the new encoding is the same relation as the inline
form, and the three shared fixes are right. What it checked over all 132 modules: the 880
attempt definitions have the binders, `[Externs]` and return type of their `R.run`, and
bodies equal to its alternatives in order; each of the 1,136 constructors has exactly one
rejected prefix listing the earlier attempts in order; no independent auxiliary predicate
(401) mentions a relation of its group or a later predicate, and every tied one (73)
does; relation modules import exactly their callees' modules. It also traced which atoms
reach the changed `have` branch and confirmed that the old behaviour there could only
have produced text that fails to elaborate.

Findings and resolutions, applied before the commit and checked by the author's rerun of
the gate, not re-reviewed:

- Four stale statements contradicted the change (Certification's implementation
  boundary, the staged-generation decision, the `StateProps` module header, the
  state-integration note; also roadmap and a Lake comment). Rewritten; the decision now
  withdraws its earlier rejection for `StateProps` in place, with the reason.
- The three shared fixes had no regression test outside the `P4Spec` build. Added:
  `ruleNames` with repeats and an unnamed rule, `substText`/`mentions` around quoted
  names, and a fixture relation binding a name to a constant under a rejected prefix.
- The generated legs' externs imported the root `P4Spec` and so every relation module;
  they import the quoted-spec module now.
- "A gate-checked fact" overstated what the gate asserts; reworded.
- Nits applied: relation modules no longer say "Rung 3"; attempt binders wrap; the
  relation-module collision check ignores case; comments and docstrings corrected.
- Not changed: a negative premise's relation still counts as a required module (a
  spurious import, no semantic effect); a collision aborts generation instead of
  recording an exclusion; attempt definitions are compiled; `Coverage.summary` does not
  print `logicalRelation` exclusions (there are none).

Limits the reviewer stated: nothing was elaborated, so the build, the fixture proofs
and Nano's byte-identity rest on the author's gate; timings and scratch-probe results
were not checked.
