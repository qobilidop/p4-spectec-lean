# Failure-retaining fresh state

2026-09-25. Independent read-only review by OpenAI Codex (GPT-6 Astra)
in the isolated `m3b-fresh-state` worktree, based on `7c1bfec`. The
reviewer did not author the implementation. No findings requiring changes.

`BitVec 63` with signed `toInt` matches the pinned 64-bit OCaml counter
and spelling, including wrap. Allocation returns the old name and advances
state. State below `Except` preserves consumed IDs on either failure;
sequential choice retries only mismatch with the failed branch's post-state.
Negation retains the post-state for all terminating outcomes. These match
the scoped behavior in upstream `fresh.ml`, `backtrack.ml` and negative
premise evaluation.

Pure lifting preserves state on success/failure and leaves divergence
unchanged. The five run equations have appropriately scoped statements
and exact axiom audits. Tests cover wrapping, sequencing, collection
failure, alternatives, negation, continuation/reset and pure lifting.
The working note explicitly defers generator/interpreter integration,
registration/memoization, deterministic checking, recursive integration
and effect-sensitive refinement. No claim was silently strengthened.

Independent `lake build --wfail P4SpecTecTest.StateEval` in the required
Nix shell exited 0. The reviewer did not run the full gate or upstream
differential fixtures. Root's full-gate evidence is recorded in status.

## Integration-plan follow-up

An independent read-only OpenAI Codex (GPT-6 Sol) review found no issue
with `state-integration.md` or its decision/status entries. It checked
agreement with the upstream audit, confirmed the shared-prefix mismatch
between current generator and upstream, and verified that the plan
requires exact final state on success, mismatch and hard error. The
recursive allocator probe is correctly labeled scratch evidence, not a
delivered generator/proof API. No full gate was run by that reviewer.
