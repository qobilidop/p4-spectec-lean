# Root-index list updates

2026-09-25. Independent read-only review by OpenAI Codex (GPT-6 Sol),
of the slice based on `7c1bfec`. The reviewer did not author the changes.

No high or medium findings. `Exp.compileExp` hoists base and replacement
before the index, matching pinned upstream `interp/interp-al/interp.ml`
lines 1009–1014 and 886–930. `Iter.setIdx` rejects out-of-bounds access;
`Eval.err?` preserves the hard-error classification. Text, nested and
sliced paths remain rejected. The refinement classifier still excludes
indexed updates, separately from executable/Prop emission support.

Low finding: the milestone paragraph still described all indexed updates
as blocked. Fixed to distinguish supported root-index list updates from
byte-oriented text updates. The reconnaissance summary agrees.

Evidence: direct Lean elaboration of `P4SpecTecTest/Updates.lean` and
`git diff --check` both exited 0. Tests elaborate and execute real compiler
output for synthetic `List Nat` updates, verify bounds errors and inspect
evaluation order. They do not elaborate the four full-P4 update sites;
the census is explicitly emission-only evidence, not a full-P4 build.

Root validation: focused implementation/test builds, `lake test`, and
the full `scripts/check.sh` passed with exit 0, no skipped gates. Nano
generation is unchanged; differential, quotation and printer checks pass.
