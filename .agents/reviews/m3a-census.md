# M3A census review

2026-09-25, independent read-only reviewer `review_census`.
Scope: the census tool, report, underlying compiler routines and export.

Findings and disposition:

- Medium: raw type recursion included singleton self edges, while the
  generator filters them for mutual-block/alias-unfolding decisions.
  Fixed by recording raw `recursive` separately from
  `emitterMutualBlock` and using the latter for text estimates.
- Low: the generator does not unfold `PlainT` aliases inside mutual
  groups; the estimate originally did. Fixed by selecting `[]` for
  aliases, exactly like the emitter. Affected 15 aliases in six groups.

Independent metrics agree: 1,689 definitions, 1,055 callables, 80
top-level source files, four executable emission failures, one Prop
failure, thirteen failures among 567 bridges, 138 eligible functions,
865 callable SCCs (234 recursive), largest group 50 members across six
source files, 190 print hints on 67 types, no callable-name collisions.

The reviewer confirmed deterministic ordered traversal, lookup-only hash
maps, callable SCCs, transitive extern requirements and refinement
closure. Post-correction census `--check` passed in Nix, and the reviewer
confirmed both type fixes exactly match Emit. All prose counts and sizes
independently match the data. Review found old IL claims in design
section 1 contradicting the clarified section 3: changed to AL and
attributed execution structure to elaboration plus algorithmization.
Also clarified that Nano-P4's run command retains `-il`, not simulation.
Final incremental review confirms those fixes, no stale report paths,
correct gate/navigation links after moving work reports into
`.agents/notes/`, and no links from human-facing `docs/` into agent state.

Required report qualifications are present: only the first failure per
component; emission does not prove elaboration or theorem success; type
sizes omit encoders/quotation overhead; source ownership is not final
module placement. No full-P4 build was claimed or performed.
