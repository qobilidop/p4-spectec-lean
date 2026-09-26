# Decisions

Current cross-cutting choices and reasons. Updated 2026-09-26.
Rules belong in [AGENTS.md](../AGENTS.md), architecture in
[Design](../docs/design.md), and detailed constraints in the linked topic
notes. This register is not a chronological log.

## Scope and product (2026-09-26)

Keep AL as input, the handwritten Lean AL reference, and the generated model.
The bounded field-update consumer is complete; broader M3 is incomplete and
paused. The earlier blanket authorization to complete M3 is superseded by the
user's pause and subsequent bounded requests. New feature work needs a newly
agreed scope. Reason: demonstrate a complete usable source connection without
mistaking isolated generated/proof fixtures for full-P4 support.

The goal is a certifying compiler, technically a proof-producing semantics
translation, not a universally verified generator. Reusable models amortize
per-artifact checking and allow generator evolution. This is a tradeoff, not
a claim of general superiority over verified compilation.
[Discussion](notes/compiler-certification.md) retains the user-requested
rationale; [Related Work](../docs/related-work.md) owns sources.
Confidence high; revisit with measured scale or consumer evidence.

## Pins and reproducibility (2026-09-25)

P4-SpecTec is pinned at `8c8e0c6f` on `gsoc-nano-spec`, because Nano is
not yet on the chosen upstream main baseline. Its companion Nano spec is
`60dfd991`. A separate submodule avoids upstream's nested SSH checkout.
Return to upstream main when Nano lands there; possible branch rebasing
makes provenance checks important. Toolchain identities remain in pin files,
not a second manually maintained version list.

Nix owns the environment; elan supplies Lean, with Batteries pinned alongside
it and no Mathlib selected. Source-preserving compressed snapshots avoid huge
generated inputs in Git. Specific tradeoffs and revisit points are in
[translation choices](notes/translation-design.md#build-and-storage-rationale).

## Interface and correctness (2026-09-26)

Use `ExampleProofs/NanoP4FieldUpdate/` for the downstream example, with tests
beside proofs. The rename deliberately has no old-namespace compatibility shim.
Provided libraries remain usable without examples; reusable proof support
stays in `P4SpecTec.Refine`. Reason: make library versus consumer boundaries
visible and checked. Revisit if another client needs a stable wrapper API.

The target is two-way terminating correspondence on a declared source domain,
including relevant failures and state, not just relation run-soundness.
Existing generated certificates remain one-way and bounded. Initialization,
source/representation adequacy and observation contracts are separate
obligations. [Translation choices](notes/translation-design.md) preserve
implementation rationale and uncertainties without duplicating architecture.
[Field-update evidence](notes/field-update.md) records the completed consumer.

These topic constraints remain binding when their work resumes:

- [State integration](notes/state-integration/overview.md): allocation survives
  rejected attempts; bounded fixtures are not production integration.
- [Byte text](notes/byte-text.md), [type runtime](notes/type-runtime.md) and
  [print hints](notes/print-hints.md): checked semantic boundaries, no fallback
  success on unsupported values or exhaustion.
- [Full P4](notes/full-p4/overview.md) and its [corpus](notes/full-p4/corpus.md):
  emission census is not compilation; exact identities and retained failures
  constrain coverage claims.
- [Nano target](notes/nano-target.md): preserve raw ExternV and shared verify
  ABI mismatches; do not invent typed target or boot/STF coverage.

## Knowledge ownership (2026-09-26)

README is the short introduction/status; Design describes the intended system;
Certification records delivered guarantees; Performance owns measurement
interpretation with dated snapshots; Related Work owns literature synthesis.
Checked walkthroughs stay beside examples. Reason: readers should not reconcile
competing copies of the same claim.

The approved `.agents/` organization is a small current-state entry point,
this cross-cutting rationale register, deferred work in Roadmap, and working
knowledge grouped by topic. Plans, experiments and reviews belong together.
Start with one note; use a topic directory only for independently useful
supporting material. Git history is the archive, without new archive folders,
tags or an accumulating lessons journal.

Keep `tend-repo` versioned here and instruction-only until observed use
justifies automation. It applies AGENTS policy, preserves open obligations
during compaction and improves from evidence, including removing ineffective
guidance. Revisit packaging if another repository needs it.

## Workflow and recovery (2026-09-26)

Direct commits are the default because this is currently a personal project;
feature branches are optional isolation, PRs require explicit request.
Review, validation and protections still apply as specified in AGENTS.
Revisit when collaboration or protections make a PR useful.

Historical experiments were retired, not integrated or declared correct.
The user chose a small committed-history bundle over the 24 GiB checkout
snapshot. Ignored campaign data and exact checkout metadata were discarded;
the bundle cannot restore exact corpus execution. Recovery boundaries,
identities and the failed casting experiment remain in
[archive recovery](notes/archive.md). Removing that local-only backup is not
part of routine compaction.
