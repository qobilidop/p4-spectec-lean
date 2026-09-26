# Actual-emitted fresh allocator refinement fixture

2026-09-25, branch `m3b-generated-state-refinement`, based on `c215d10`.
Own changes: `P4SpecTecTest/StateGeneratedRefinement.lean`, its test-root
import and this note. Executable generator dependencies were copied from
`e0d7219` for focused checking and remain uncommitted, unowned dependency
copies in this isolated worktree. Integrate after that executable commit;
do not mistake the fixture commit alone for a standalone branch build.

The fixture invokes `Funcs.builtinDecl` on a real `fresh_typeId` builtin
declaration, checks declaration-selected state mode, parses and elaborates
the returned Lean text, and proves `StateRefines` against
`ExceptT.mk «$fresh_typeId»` itself. There is no hand-written replacement
allocator in the theorem target. `freshStateRefinesOfHolds` discharges the
general theorem for every interpreter fuel, initial state, guard-disabled
configuration, internal/external invocation choice and admissible table.

Further audited theorems instantiate a concrete table and compose the
actual emitted definition through either failure, ordered retry and
negation. A resetting wrapper around that emitted definition is rejected
by a kernel proof at fuel 3, initial state 5, even with a value relation
that accepts all values. Every theorem has its exact axiom check; the
sets are `propext`, `Classical.choice`, `Quot.sound`.

Checks used `nix develop /Users/qobilidop/my/work/p4-spectec-lean --command`
with explicit isolated-worktree cwd:

- `lake build --wfail P4SpecTecTest.StateGeneratedRefinement`: exit 0,
  53 jobs.
- `lake env lean
  /Users/qobilidop/my/work/p4-spectec-lean-generated-state-refinement/P4SpecTecTest/StateGeneratedRefinement.lean`:
  exit 0, direct re-elaboration of the actual emitter and all proofs.
- `git diff --check` and an explicit 100-column scan of the new Lean file:
  exit 0.

Initial drafts needed a `change Holds globals declaration` step before
hash-map simplification and shorter theorem names for stable exact-axiom
message wrapping. Those drafts failed the focused check and were fixed.
No full gate or push was performed. Root independently read the complete
fixture and found no correctness findings; independent re-elaboration and
the full gate remain for integration. This is bounded actual-emitter validation, not generated
per-definition theorem emission or full-P4 refinement coverage.
