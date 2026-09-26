# Performance and Certification guide review

2026-09-26. Independent read-only review by `/root/doc_guides_review` of the
documentation follow-up to `6134bb2`. No findings requiring changes.

Checked the certification directions, fuel semantics, failure preservation,
`Rel`, guards and `HoldsSpec` against the refinement definitions and generated
theorem types. Checked the field-update domain, initialization, reverse finite
witnesses and consumer exclusions against `Certificate.lean` and `Example.lean`.
The 18/153 count agrees with the generated refinement index; quotation identity
is correctly distinguished from a kernel proof of the exporter.

Independently summed the timing snapshot: 48 modules, 860.6 seconds. The guide
correctly distinguishes that sum from wall-clock build time and isolated kernel
checking, and records missing provenance without inventing it. The timing-script
changes affect comments and report wording only. No timing rebuild was run.

Reviewed navigation and preserved Design anchors; no stale old timing-path
references were found. Staged whitespace passed. This is a guide-accuracy review,
not new measurement evidence or a general semantic audit. Root separately checked
all 28 local README/docs links and shell syntax; full-gate evidence is recorded
in `.agents/status.md`.

## Intended-design rewrite

The user expanded the scope to a concise but technically precise intended
design, rather than a current implementation report. Root rewrote Design to
about 2,200 words and moved current limitations into Certification and milestone
planning into Roadmap. The required refinement, trust and deviation anchors
remain stable.

The same independent reviewer checked the final rewrite against the prior
design and actual refinement/effect code. No substantive correctness findings.
Both correspondence directions, finite reverse witnesses, failure/state
distinctions, source coverage, environment obligations and logical-soundness
limits survive the compression. Unsupported claims about Option fallback,
pure-only effects, trusted-base size and unconditional build parallelism were
removed or corrected.

Three minor findings were fixed: the AGENTS roadmap description, a stale M2
reference in the determinism tactic's docstring, and the missing explicit
quotation-normalization policy in Certification. Root checked all 33 local
README/docs links and Markdown anchors after these fixes. The determinism
change is a comment only. No source pin, generated artifact or semantic
implementation changed. Validation is recorded in status.
