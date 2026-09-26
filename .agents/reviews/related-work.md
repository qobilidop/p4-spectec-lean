# Related-work revision review

Independent read-only reviews, 2026-09-26, by
`/root/priorart_semantics` and `/root/priorart_deep_shallow`.
The primary agent records their returned findings here; neither reviewer
edited the reviewed files. Implementation baseline: `395022a`.

## Scope and evidence

- The semantics reviewer checked the P4 and Wasm SpecTec comparisons against
  primary papers and official project sources, including Petr4, P4Cub and
  Verifiable P4's stated proof boundaries. HOL4P4's positive contributions
  were checked against its primary conference record; the ACM full-paper
  fetch was unavailable, and no unverified section numbers are supplied.
- The certification reviewer checked Cogent, AutoCorres, CakeML and Sail
  claims against their theorem sections, implementation report and pinned
  backend source. The reviewer did not independently re-audit this repo's
  implementation theorems.
- Root checked the current generated refinement inventory and field-update
  certificate, and read the complete final document. Additional source
  checks covered Leroy's terminology, CompCert's contract, Alive2's bounds,
  the Trivet preprint and the current P4 working specification.

## Findings and resolution

- Corrected the Cogent 2016 reference to an arXiv preprint. Neither the
  ASPLOS nor ICFP venue belongs to this exact title; those are different
  Cogent papers. Added the expanded JFP 2021 treatment with section numbers.
- Fixed a stray plus character in the P4 introduction.
- Added positive contributions before the limitations in the P4 comparisons,
  including Core P4 metatheory, P4Cub's retained constructs and HOL4P4's
  architecture semantics and metatheory.
- Completed P4 bibliographic entries, corrected the official Wasm news title,
  and dated the Sail implementation report.

Both reviewers reread their relevant final sections in `docs/related-work.md`
and reported no remaining findings. The title and filename follow the user's
explicit choice. No claim of exhaustive literature coverage or new methodology
is made. Historical design critique remains in its working note.

No Lean build or full gate was run for this documentation-only change.
Root performs text, size and local-link checks separately. No commit or push
is part of this review handoff.
