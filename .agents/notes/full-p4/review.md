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

## M3 stages reviewed on 2026-10-04 and 2026-10-05 (compacted 2026-10-06)

Each stage was reviewed read-only by a fresh Claude Fable 5.1 subagent before its commit,
on the uncommitted branch against the `main` revision named; none built the tree (the
golden-samples reviewer ran the Python tests and the text, size and sample checks), and
the resolutions were checked by the author's rerun of the gate (and the sweep where it
changed), not re-reviewed. No blocking defect in a shipped artifact was found; one policy
blocker (status without evidence) was fixed before its commit. Prose records are at
`0d78b6e:.agents/notes/full-p4/review.md`.

| Stage, base | What the reviewer confirmed | Findings resolved | Not changed / limits |
|---|---|---|---|
| Executable generation (`cd6679e`) | Pure-mode planning unchanged; tuple codec inverse for every admitted shape; replay refactor preserves the interpreter leg; generated externs match the placeholders | Replay claim counted the rejected program as returning outputs (reworded; generated legs now require the decoded program to encode back); consumer-root boundary rule and test; stale "paused" sentences; conditional equality import | `ctorNames` has no distinctness check (a clash fails loudly); `validateTuples` does not expand tuple aliases (none at the pins). Warm gate; cold Linux build left to CI; instance-resolution arguments made by reading |
| Corpus sweep (`6e57dcb`) | Upstream failure paths traced to the port's `Fail.err`/`Fail.unmatch`; trampoline wrapping, value shapes and evaluation order; `Corpus/Check.lean` keeps every old check | Policy blocker: status without evidence (rewritten); generated externs decoded inside the mismatch wrapper (now a hard error outside it); sweep could exit 0 with non-bound capture failures or nothing evaluated, omitted harness sources from the cache identity, lost a record on a thread exception (fixed, fake-worker tests, `--retry-unobserved`); mutation sentence read as a standing property | `shard.py`/`campaign.py` digests name `Corpus/Main.lean` only; `--max-case-bytes` unbounded (fails closed). Codec correctness for `typingContext` rests on two programs |
| Logical relations (`f329af0`) | Over all 132 modules: 880 attempt definitions have their `R.run`'s binders and bodies equal to its alternatives in order; 1,136 constructors each have one rejected prefix in order; 401 free predicates mention no group relation, 73 tied ones do; imports equal callees | Four stale statements; regression tests for the three shared emitter fixes; generated externs import the quoted spec, not the root; "gate-checked fact" overstated | A negative premise's relation counts as a required module (spurious import); a collision aborts generation; `Coverage.summary` does not print `logicalRelation` exclusions (none). Nothing elaborated; timings and the scratch-probe measurements behind the encoding choices (101 types in 13 minutes; 30 MB, 93 to 95% repetition) were not checked and are author evidence |
| Golden samples (`c7ed36f`) | `--check` cannot pass when a sample differs or lacks its file | Sample set lacked an executable relation (added `9.0-eval-arch`, a builtin wrapper); samples could fail the line-length gate (exempt, with test); prior-art claims stronger than observed (dated observations); seven of fourteen tool mutants survived (tool resolves against the repository, validates before writing, rejects links) | Any file under the directory is a sample (fails closed); the set is not pinned |
| Run-soundness, 14 relations (`916c7ba`) | Statement quantifies inputs, output tuple and both states with outputs projected as the constructors use; claim and theorem share one statement, `checkClaim` compares an independently elaborated type; eligibility rule yields exactly the 14 modules with accurate exclusions; `projCases` right for projections and class methods | "Outside every recursive dependency" was false (ten call recursive functions; rule is about relation premises); stale "without a theorem" statements; `dependency` unset on "calls X" exclusions; direct `projCases` examples; per-branch normalization; zero-output and `[Externs]` statement forms checked as claims | Eligibility is syntactic (an eligible relation the tactic cannot close fails the build); claimed entries keep the general exclusion; `explain` reports AL status only. The Nano proofs and the scratch evidence of the then-planned recursive shape rested on the author |

## Recursive run-soundness stage (2026-10-05)

Independent read-only review of the uncommitted `m3b-recursive` tree against `main`
(`e0e7863`), by a fresh Claude Fable 5.1 subagent. It ran no Lake build and no gate; it
read the diff, the generated modules and `P4Spec/coverage.json`, used the tree's existing
build products, and ran scratch files with `lake env lean`. Verdict: no blockers; it found
no way for `#audit_axioms` or the test harness to pass an unproved theorem.

What it confirmed:

- `sharedAxioms` reads the same kernel environment and makes the same case analysis as
  `Lean.collectAxioms`, and delegates imported constants to it. Twelve scratch cases gave
  no instance where the audit passes and `#print axioms` shows a forbidden axiom: a private
  `sorry` lemma, an axiom in a constructor type, `opaque`, `native_decide`, a
  kernel-rejected proof and its user, an asynchronous elaboration failure, a realized
  equation lemma, structure defaults, multi-name orderings, an imported axiom. Its own scan
  with Lean's collector over the built products: 256 `run_sound` and 31 `run_sound_group`
  theorems, none with an axiom outside the allowed three.
- Corollaries, non-recursive theorems and coverage claims share `runSoundStatement`; the
  projection paths are right for one, two and three relations and for a group with a
  function member, which has no conjunct.
- With `Elab.async` off in scope, an elaboration error, a kernel rejection, a tactic
  failure and the budget wrapper each make the harness throw; a `sorry` is caught by the
  generated audit, itself elaborated through the harness.
- The counts in the documents (256 relations, 155 in 31 recursion groups of 1 to 50, 132
  modules, 87 formerly waiting, no `runSoundness` exclusion), the manifest and the samples.
- Every relation has one constructor more than it has named attempts, so the rule index
  from rejected attempts is right; a wrong index only reorders the search.
- Lean's `partial_correctness` does fail on `Copy_out_inner` and on a scratch definition
  of eight parameters, with the instance-resolution message.

Findings and resolutions, applied before the commit and checked by the author's rerun of
the gate, not re-reviewed:

- A fixture comment claimed Lean's derivation fails for a parameter passed on unchanged.
  It does not (the generator rebinds parameters, and the fixture's principle derives);
  what fails is a long parameter list, which no fixture had. Comment corrected; added the
  relation `wide` with seven inputs, which proves.
- A fixed point abstracted over a parameter of the statement was unsupported with
  misleading errors (no generated definition has one: all 155 recursive `run` definitions
  abstract only the instance). The tactic now rejects that shape by name, and the
  dependence on the generator's rebinding is recorded in decisions.
- Stale docstrings (planner, `StateProps` header), a wrong file pointer in decisions,
  "outcome induction" wording for what is now fixed-point induction, the singular audit
  docstring, the `RecursivePrefix` header, and "agree on successful runs" in
  Certification, which read as an equivalence. All rewritten.
- The pitfalls entry and harness comments merged two cases of a failed asynchronous
  proof (elaboration failure shows `sorryAx`; a kernel rejection is an axiom under its own
  name). Separated.
- No sample of a recursive group with the extern instance: added `Decls_inst`. The plan
  test did not assert module dependencies or imports: asserted. No negative fixture for
  the group tactic: a false statement about `count` is now checked to be rejected.
- Proof build products are about 387 MB (161 MB for `Expr_eval`), absent from the cost
  record: added to the overview.
- Not changed: `headAssumption` still falls back to `assumption` when no hypothesis of
  the same head closes the goal, at the old cost (now stated in its docstring).

Limits the reviewer stated: timing figures were not verified; its scan used build products
slightly older than the final tactic text; it did not rerun generation, Nano regeneration
or the Nano proofs against the changed shared helpers (the gate does); the proof-building
code was read for failure modes, not proved, and soundness rests on the kernel and the
audit; the meaning of the logical relations was the earlier stage's subject.

## Regression sweep stage (2026-10-05)

Independent read-only review of the uncommitted `m3c-regression` tree against `main`
(`00aa1c2`), by a fresh Claude Fable 5.1 subagent. It ran the offline sweep tests and the
text check, read the code, `Check.lean`, upstream's rule and test harness, and the
artifacts of the author's runs; it ran no Lake command and not the sweep. Verdict: no
blockers.

What it confirmed from the checkout and the observations: 37 candidates (13, 4, 20) with
the recorded digest, in group then name order; the pin, and that the revision guard covers
the enumerated tree; observation index and candidate correspond; the cache identity
separates the two sets and a shared output directory is wiped, never mixed; what
`Check.lean` compares (the counter before any classification; either Lean failure class
against upstream's one); all thirteen `neg` observations are `unmatch` on both relations,
exactly three with a nonzero counter; the exclusion-manifest counts quoted for
`p4_16_errors`.

Findings and resolutions, applied before the commit and checked by the author's reruns of
the sweep and the gate, not re-reviewed:

- "First corpus evidence about failure" was overstated: the bounded replay already has
  `neg/issue-204.p4` on both legs. Reworded to what is new (twelve more rejections, three
  after consumed identifiers).
- For a rejected program `Program_inst` is not independent: its first premise is
  `Program_ok`, and the two sessions have the same class and counter. The documents now
  say every rejection is a typing failure and no instantiation failure is exercised.
- `source` accepted empty and `.` path segments (`upstream//etc/passwd` resolved outside
  the root; not reachable from either candidate source). Segments are now checked as the
  inventory checks them, with the cases in the test.
- The enumeration was non-recursive over three fixed groups while upstream collects
  recursively, with nothing to detect a set that grew. It now fails on a nested directory
  or any other entry of the regression directory.
- The pass condition was weak (one matched rejection anywhere). It is now exact: every
  candidate observed, every `neg` program a matched rejection and every other program
  matched as accepted, on both relations and both legs. The summary also records the class
  each leg returned (`unmatch` for all thirteen, upstream's class), which the first
  version did not.
- Notes: the AL mode of the probe against upstream's SL-only regression harness, the zero
  counters, and the `AGENTS.md` comment. Added.
- Not changed: the regression exit composition stays inline in `main`; the functions it
  composes are tested.

Limits the reviewer stated: it did not run the sweep, Lake or the gate; the p4c-corpus
mode on the changed code was unexercised beyond unit tests; it did not review the Lean
workers beyond `Check.lean` and the two entry points.

## Working-state compaction (2026-10-06)

Independent read-only review of the uncommitted `tend-2026-10-06` tree against `main`
(`0d78b6e`), by a fresh Claude Fable 5.1 subagent that diffed every rewritten passage
against the old text and the tree and ran only the text check. Verdict: no lost obligation
or constraint absent from every owner, no blocking claim change. Findings, all applied
before the commit and not re-reviewed: three figures in the overview had drifted
(generation time, the 444 s gate's conditions, "seven groups" for seven traps); the merged
Nano entry had dropped the reasons behind several rejected alternatives and revisit
triggers (`PacketStateText`, the evaluator, the release digest, the heartbeat budget, the
audit layout, native tactics, the field-update mutation choice, the extern freshness
hypothesis, the shared-prefix history), now restored; one consumer note still named a
merged heading; the review table had dropped three reviewer limits; the profiling guidance
named a phase that is not timed and summed nested phases; the AGENTS sentence blamed the
text check for a late failure the build stage causes. Proposals not taken up: merging the
four 2026-09-26 to -28 Nano entries and moving the sweep entry's third paragraph into the
corpus note; compacting `notes/ci-performance.md` and `notes/proof-build-performance.md`
into `docs/performance/`. Limits: read-only; timings taken on trust from status.

A second pass the same day (performance notes compacted into `performance-history.md`;
the four Nano domain entries merged; skill lessons) was reviewed the same way by another
fresh subagent. Verdict: no blocker, no lost constraint, no changed claim. Resolved
before the commit: review provenance the new performance note had dropped (three
reviews, authorship of the stabilization and tactic work, a reviewer's scope), a
rejected-design constraint (imported-constant inventories per environment), a
measurement rule (report ranges, not a factor) and two limits, the discarded
experiments' figures, a reason clause and a wrong "pure-mode" scoping in the merged
Nano entry, two unverifiable figures in the skill's lesson, and CI reported as a run id
rather than as pending. Proposals not taken up: trimming the Nano certificate entry's
evidence pointers and moving implementation detail of two full-P4 entries into the
design; `repository-stewardship.md` and `corpus.md` as next candidates. Limits:
read-only; timings taken from the recorded text.
