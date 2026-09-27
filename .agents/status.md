# Status

Session handoff, updated 2026-09-27. Only requested repository maintenance
has run since N2 closed; no feature work is active. N3–N6 have not started and
full-P4 M3 remains paused.

## Verified checkpoint

N0/N1/N2 are complete. N2 implementation and its clean-checkout test correction
are published through `76bed8485032a6bb2e95b248b37f99dcf0c45267`; closure is
recorded at `d85e82c02a4d714bdcc7a78ee681cf64490aee78` on `main`.
[Final closure CI 36316496027](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36316496027)
passed, following
[implementation CI 36314414521](https://github.com/qobilidop/p4-spectec-lean/actions/runs/36314414521).
The corrected full local `nix develop -c scripts/check.sh` returned actual
exit 0 (session 47761): all 44 stages, no skips. The 36 inventory tests also
passed with the ignored raw Nano export absent. Independent reviews and their
limits are summarized in the [Nano plan](notes/nano-certification.md).

N2 delivers all 162 source codecs, all 26 builtin contracts, and the required
30-definition dependency/SCC closure. Paired executable correspondence covers
39/153 definitions overall. The broader inventory has 888 obligations,
381 bindings and 507 unresolved; complete Nano certification is not claimed.
[Certification](../docs/certification.md) owns the detailed public guarantees.

## Resume point

On a future request to begin N3, start with Program_load/Expr_eval dependency
closures and both proof directions, including actual intermediate call domains.
The [remaining plan and estimate](notes/nano-certification.md#remaining-effort-estimate)
budget 45–90 elapsed working hours for N3–N6, about 60 as a working estimate;
reassess after a 4–8-hour first N3 checkpoint. This is a forecast, not new
implementation authorization. Preserve the full scope and all corpus cases.

## Maintenance and repository state

Maintenance since the N2 closure changed no semantics, pins or generated data.
The latest pass linked `.claude/skills` to `.agents/skills/` and added its gate
check. [Stewardship](notes/repository-stewardship.md) records each pass's
review, validation and CI. Inspect the latest main CI at the next session,
before new work.

One worktree remains on `main`. The merged N2 branch is removed; the older
`docs/repository-review` branch and local archive backup are preserved.
The expected upstream exporter patch remains applied. No source pins changed.
