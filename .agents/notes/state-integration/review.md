# Recorded state review and validation evidence

Compressed 2026-09-26; all reviews below occurred 2026-09-25. This preserves
AI-agent review provenance, not human review or a new re-review. Original
reports under `.agents/reviews/` and notes under `.agents/notes/` are in Git
`968ad65`. Use the source names below to recover complete commands/reproducers.
All reported Lean checks used the pinned Nix shell. “Root” denotes the
historical coordinating agent, independently of the implementation author.

| Former report | Reviewer and revision | Recorded independent evidence and boundary |
|---|---|---|
| `m3b-fresh-state.md` | GPT-6 Astra, base `7c1bfec`, not the author | StateEval focused build exit 0; no full gate/oracle. GPT-6 Sol separately reviewed integration plan. |
| `m3b-state-calculus.md` | GPT-6 Astra, diff from `1b34d71`; own earlier foundation excluded | 66-job StateCalc build, direct elaboration and audits exit 0. Sol reviewed documentation. Root subsequently recorded full gate exit 0/no skips. |
| `m3b-effect-interpreter.md` | Independent agent, `a81265d` vs `9bc0861`; own foundation excluded | 67-job build, direct StateInterp and sensitivity guards exit 0. No full gate/Nano rebuild by reviewer. Byte integration `a81265d,21ee889` over `e1c5555` independently checked. |
| `m3b-state-oracle.md` | Root reviewing Sol's `59525a2` | Rebuilt upstream oracle, built/read all 15 cases exit 0. Original author cross-reviewed root's adapters and ten corrupt-fixture tests, exit 0. Full gate separate. |
| `m3b-recursive-prefix.md` | Root, `981cc0b` | Direct RecursivePrefix elaboration, seven execution/state guards and exact audits exit 0. Bounded mutual fixture, no full gate/oracle. |
| `m3b-state-rules.md` | Root, `2c08752` | Direct StateRules elaboration, four guards, negative kernel test/audits exit 0. Integrated two-fixture build 44 jobs and two root full gates exit 0/no skips; Sol reviewed status/plan. |
| `m3b-state-codegen.md` | Independent agent, uncommitted tree at `bf7fb62` | 65-job focused build passed but three independent reproductions exposed medium findings below. No full gate. |
| `m3b-state-codegen-followup.md` | Root, `e0d7219` | Corrected optional/callback/codec cases and fixpoint lemmas inspected; 66-job focused build exit 0. Production guard and larger scaling obligations retained. |
| `m3b-state-iteration.md` | Root, `381dd6a,25ad4f2,815b671` with `e0d7219` | 78-job integration build and direct StateProps elaboration exit 0. Bounded nonrecursive structural support only. |
| `m3b-fresh-refinement.md` | Executable-codegen agent reviewing root's changes, base `7d9d356` | 44-job build and direct StateInterp/StateRefinement elaborations exit 0; reset counterexample audited. Author full gate not independently repeated. |
| `m3b-emitted-fresh-refinement.md` | Root, `ae91edd` | 75-job build and direct StateGeneratedRefinement elaboration exit 0. Actual emitter target; full gate/remote CI separate. |
| `m3c-state-refinement.md` | Root, `de73566` | Direct StateValidate elaboration exit 0; no bounded correctness findings. Production dependency closure remains integration obligation. |

## Findings resolved and failed experiments retained

- Effect negation tests initially used indistinguishable branch values.
  Distinct `first:`/`fallback:` tags fixed sensitivity: replacing IfNotHoldPr
  with IfHoldPr in a streamed test failed the two intended assertions.
- State oracle initially accepted either primitive failure tag. It now
  requires `.unmatch`, captures the real initial seed, checks initialization
  and git-index exit status, and rejects missing/duplicate/reordered or
  malformed cases. Public AL failure-kind collapse remains a real limit.
- Executable review found mixed optional expression inputs returning successful
  `none`, callback-only SCCs failing monotonicity elaboration, and direct
  function data admitted as 1/1 proof-eligible despite missing ToValue.
  Corrections distinguish mixed hard errors, prove consumer monotonicity,
  and preserve ExpP/DefP provenance. Tests elaborate/execute actual output
  in both carriers. The first partial recovery still failed on an already
  recursive consumer; subsequent invariant drafts failed and two runaway
  builds were terminated before final passing checks. They are not evidence.
- Root found selected-path substitutions capturing earlier `tmp_0` at another
  type. Closed input lambdas and free-argument relevance fixed it; reversed
  aliases and shadowed/captured iterator regressions preserve the boundary.
- Captured predicate lambdas fail nested-inductive positivity. Explicit
  chain inputs/mutual helper indices work; that negative fixture must survive.
- Concurrent Lake builds once raced on `Refine/Calc.olean`; final serial
  116-job library/StateInterp/Nano and 130-job test-root builds passed.
  Missing ignored Nano JSON was fixed by verified snapshot extraction.
  A mirror check in an uninitialized worktree failed; pointing the same
  checker at the real pinned checkout passed. None is a clean full-gate run.
- Generator `--check` embeds the input path in headers: an absolute-input
  review probe reported 48 stale files; canonical relative input passed
  without writing output. Recovery checks later confirmed all 48 unchanged.

## Integration evidence, not current publication tasks

The shared interpreter/oracle was recorded integrated via PR #13 with local
and remote gates passed. Fresh boundary PR #16 and generator integration
PR #17 (`b08ab8e`) are retained history. Earlier isolated notes' pending
integration/review instructions were superseded by these later records.

Bounded refinement author checks: `lake build --wfail P4SpecTec
P4SpecTecTest.StateValidate` exit 0, 78 jobs/37-second fixture. PR #19's
initial remote Gate passed at `c54e4eb`, run `36207315308` (5m25s).
After merging `ea9533d`, root reviewed the status-only reconciliation and
the four implementation/test modules were byte-identical to `c54e4eb`.
The author repeated the frozen full `scripts/check.sh`, exit 0/no skips,
including twelve incoming oracle contracts. That report still owed final
merged-head CI; it must not be retroactively called reviewer-run or remote
success. Later retained main includes merge `c974c3d`; current publication
state belongs to root status, not this historical review.

All this evidence remains bounded. It neither enables production state mode
nor validates the retired full-P4 aggregate or wider corpus. Its explicit
open obligations are consolidated in [overview](overview.md).
