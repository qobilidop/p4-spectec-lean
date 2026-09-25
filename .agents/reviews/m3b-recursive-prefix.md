# Recursive rejected-prefix proof review

2026-09-25. Independent root-agent review of `981cc0b`, read-only except
this report. No findings in the bounded proof fixture.

The executable really is a two-member `walk`/`reject` recursive SCC.
The earlier rejected attempt can recurse through `walk` before returning
its consumed state. `Walk` remains a structural successful-rule inductive,
with a `RejectedPrefix` over the final `reject`, not an approximant.

The strengthened partial-correctness motives carry exact all-terminating
result/poststate realization for both members. `transport` and `realization`
use identity state refinement, and compositional bind/choice lemmas justify
replacement of recursive approximants. The successful structural component
uses the transported rejected-prefix equation and the recursive successful
`Walk` witness. The auxiliary graph equality is not the definition of `Walk`.
Every new theorem has an immediate exact axiom guard; no axiom allowance or
proof obligation was weakened.

Independent command, through the pinned default Nix shell in the prototype
worktree: `lake env lean P4SpecTecTest/RecursivePrefix.lean` exited 0,
checking the complete proof, seven execution/state guards and axiom guards.
Source inspection also checked wraparound and the exact prefix state in
the `cons` constructor.

This validates the stronger-motive approach, not arbitrary generated SCCs.
The fixture's rejecting member has a proved no-success invariant; a generic
translator must also handle earlier attempts that can succeed and retain
the corresponding successful constructor case. Ordered iterated structural
premises and automated generated proof synthesis remain unproven here.
No full gate, integration, upstream comparison or push was performed.
