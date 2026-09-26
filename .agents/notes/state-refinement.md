# Stateful AL refinement boundary

Root branch `m3b-state-refinement`, based on merged main `7d9d356`.
Recovered work resumes the original M3 objective; this checkpoint does not
enable production state generation or claim full-P4 refinement coverage.

`Refine/StateInterp.lean` connects the actual effect-parameterized AL
interpreter to `StateRefines`. Fresh builtin dispatch and the complete
`invoke_func` route refine the typed byte-text allocator for every fuel,
every initial counter and every terminating outcome. The final counter is
exact, including signed wrap. Low fuel is divergence and is unconstrained
under the existing one-way partial-correctness contract.

The function theorem requires disabled guards, the expected declaration
in the global table (`Holds`), and an empty local function environment.
The lower lookup theorem also handles a local declaration with the same
name. It does not claim fidelity for raw builtin callback aliases. Debug
tracing is allowed and proved observationally transparent. A separate
arity equation proves malformed builtin arguments mismatch without
consuming state.

`StateRefinement` fixtures instantiate a concrete declaration table and
compose actual dispatch through mismatch, hard error, retry and negation.
A kernel-checked counterexample rejects an allocator that resets state,
even under a value relation accepting all results. These are hand-written
bounded proofs, not generated translation validation or broad mutation
coverage. All advertised theorems carry exact axiom audits.

`nix develop --command lake build --wfail P4SpecTecTest.StateRefinement P4SpecTec`
exited 0 (69 jobs). `nix develop --command
/Users/qobilidop/my/work/p4-spectec-lean/scripts/check.sh` exited 0 with no
skips, including both Nano differential legs, quotations, print/text/state
oracles, transport sensitivity and the full-P4 census. Import checks,
`git diff --check`, and explicit new-file 100-column checks also exited 0.
Initial drafts exposed axiom-audit expectations and opaque hash-table
reduction; the final tests use hash-map lookup lemmas rather than relying
on evaluator reduction. Independent read-only review found no correctness
issues: focused build exited 0 (44 jobs), and direct re-elaboration of both
modules exited 0. Report: `.agents/reviews/m3b-fresh-refinement.md`.
Remote CI remains owed. Next: use this boundary in generated
stateful refinement together with the structural generator integration.
