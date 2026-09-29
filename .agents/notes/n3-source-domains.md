# N3 source-domain closure

Durable proof/review evidence, closed 2026-09-29. Implementation `67f67ae` is on
main with passing [CI 36538318591](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36538318591). The user requested quota-conscious N3 progress and a
resumable handoff. N4 implementation is outside this step.

## Implementation

All four formerly missing polymorphic source-domain certificates now generate:
`empty_set`, `empty_map`, `ite`, and `repeat_`. Arbitrary legal parameter codecs
and independent admission predicates remain explicit. Empty containers have
vacuous input coverage (`True`) and empty membership; choice returns an admitted
input. Repetition inducts on the actual natural count and uses the successful
recursive tail. It asserts no total-termination theorem.

Recognition checks source structure, not callable names. Repetition compares the
complete region-erased clause quotations against a two-clause template with the
actual distinct binder names and recursive callee. Its proof unfolds once per
induction case with `rw`; adding the recursive equation to `simp` loops.
Tests cover renamed positive shapes, malformed bodies/types/clauses/parameters,
wrong execution mode, changed branch order and a removed recursive guard.

The generator and new proofs add exactly four sourceDomain claims. Independent
review found no existing claim removed or changed. Inventory: 888 obligations,
762 compiled bindings, 126 unbound; source identity is checked by the CLI, leaving
125 unresolved across all stages. No unresolved core item is owned through N3;
78 core items remain owned by N4. Thus this is N3-owned proof closure, not full
core-stage or whole-Nano acceptance. The normal gate now requires
`--require-n2 --require-owned N3` without weakening bounded N2.

## Validation and review

- Final targeted source-polymorphic generator tests, including repeat mutation
  tests and consistent self-renaming, passed with `--wfail`, exit 0.
- All four actual generated `SourceDomain.*` modules built with `--wfail`, exit 0,
  including their axiom audits. A first regeneration used an absolute input path
  and changed header comments; canonical relative-input regeneration restored
  every existing proof file byte-for-byte. Only roots/metadata and four new
  generated proof files differ.
- Two initial full gates exited 1 on the renamed-recursion test's Lean layout.
  The final named-definition form passed the focused test build. Both strict N3
  inventory checks passed with zero unresolved items. The first library/certificate
  build took 38 seconds. Logs: `.artifacts/perf/n3-domain-gate.log` and
  `n3-domain-gate-final.log`. The corrected full gate, timed with
  `nix develop -c /usr/bin/time -l -p scripts/check.sh`, returned actual exit 0
  in 124.00s with no skips; `n3-domain-gate-validated.log` records it. Strict N3
  reports zero unresolved owned-through-N3 core items. Text, whitespace and all
  36 changed-document relative link targets pass; final review also checked and
  corrected the roadmap's historical-estimate anchor.
- Independent read-only Codex GPT-6 Astra review checked handwritten changes,
  all four generated theorem types/proofs/audits, coverage and completion diffs,
  and stronger gate flags. It found and required the zero-input coverage fix;
  re-review found no semantic blocker. Scope wording was corrected so the N3
  exit means owned-through-N3 validation, not full core acceptance. No reviewer
  builds were run. GPT-6 Sol authored the first three shapes and tests; the parent
  authored repetition, the zero-input fix and integration. These are AI reviews.

## Handoff

Local validation, independent review, main integration and exact-implementation CI
are complete. Main CI passed every gate and upstream pin check; the certificate
stage took 10s. Log: `.artifacts/perf/n3-domain-ci.log`. The merged
`n3-source-domains` ref was removed and branch listing verified removal. The final
evidence-only checkpoint reuses unchanged executable inputs with fresh text/link
checks and independent review. N3-owned proof closure is complete; the broader
core stage remains open. A new N4 scope should start with the Nano plan and target
note, preserving every corpus obligation. Do not start N4 implicitly.
One build per checkout.
The existing dirty replay worktree and non-ancestor `n3-decl-load` branch remain
preserved unrelated experiments. The expected upstream exporter patch is unchanged.
