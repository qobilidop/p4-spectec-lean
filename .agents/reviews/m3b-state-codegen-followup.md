# Executable state generator follow-up review

2026-09-25. Root independently reviewed the recovered executable generator
at executable checkpoint `e0d7219` in the `m3b-state-codegen` worktree, including the earlier review's three
reproducers and the new fixpoint monotonicity lemmas. This review changes
no implementation. The reviewed executable changes remain separate from
production structural-proof selection.

No remaining correctness findings in this bounded checkpoint:

- Multi-input optional expressions now distinguish all-present,
  all-absent and mixed presence even when their body is pure. Emitted tests
  execute both mixed orders in stateful mode and also cover pure mode.
- `validateParam` preserves DefP/ExpP provenance. Direct function data,
  callable results, nested function-valued data and rank-polymorphic
  callbacks fail explicitly. Signature validation runs at planning and
  direct function/table/builtin emission boundaries.
- The new least-fixed-point monotonicity lemmas are kernel proofs, with
  exact axiom guards. The tactic unfolds only named generated consumers;
  it supplies no unchecked extern/callback assumption. The actual emitted
  callback-only cycle elaborates and runs in both carriers, including a
  call through a previously recursive consumer. Both cycle axiom audits
  contain only propext, Classical.choice and Quot.sound.
- Full relation attempts retain input matching, shared premises, path
  premises and output evaluation on each retry. State is neither invented
  nor reset internally. Raw builtin/extern function arguments are rejected
  because upstream dispatches copied declarations by their local alias.
- The inherited production guards, table-callback refinement exclusion,
  signature-validation call and conditional monotonicity import were
  reviewed explicitly. Production state generation remains disabled.

The review requested avoiding whole-spec reachability computation for
nonrecursive definitions. The author guarded that computation in function,
table and relation emission and stops reachability once it stabilizes.
Large recursive full-P4 groups still require a measured scaling check.

Independent command (original flake, executable worktree cwd):

```
nix develop /Users/qobilidop/my/work/p4-spectec-lean --command lake build --wfail P4SpecTecTest.StateCodegen P4SpecTecTest.Updates P4SpecTecTest.Text.Main
```

Exit 0, 66 jobs. This executes the emitted optional/callback regressions
and kernel audits. The author separately records the unchanged Nano
generation check. Full integration gate, current full-P4 capability census,
remote CI, guarded callback fidelity and general recursive proof automation
remain separate obligations; this report establishes none of those.
