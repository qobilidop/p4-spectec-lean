# Byte-text foundation

2026-09-25. Independent read-only review by OpenAI Codex (GPT-6 Sol)
in `m3b-byte-text`, based on `3b8175f`. This reviewer was separate from
the GPT-6 Sol implementation agent. No findings.

`ofBytes` and `toBytes` preserve arbitrary byte arrays; decoding through
`fromUTF8?` is explicit and checked. Index/slice operations reject invalid
bounds, and updates require exact replacement lengths. Array lexical
comparison on UInt8 gives unsigned byte order with proper prefixes first.
LawfulBEq and LawfulEqOrd relate equality/comparison to the exact bytes.
Both advertised theorem axiom guards pass.

Tests cover invalid UTF-8, byte indexing/slicing/replacement, bounds and
replacement lengths, concatenation and order. This is a substrate only;
no IL, generator, interpreter, builtin or refinement integration is claimed.

Independent `lake build --wfail P4SpecTecTest.ByteText` in the required
Nix shell exited 0 (three jobs); `git diff --check` exited 0. The author
also built both library/test roots with warnings failing and checked
imports/line hygiene. A missing ignored Nano export in the new worktree
initially failed Decode; unpacking the pinned snapshot and rerunning passed.
The reviewer did not run the full gate; primary-worktree integration
records that evidence separately in status.

Follow-up documentation review found one imprecise phrase: "equality/order
laws" could imply proved transitivity; changed to equality/compare-equality
laws, which is the actual theorem scope. The first full gate caught a
missing "not a mirror" declaration in the new Util module header; added
the required provenance statement. That first gate exited 1 and is not
a passing result. The fresh gate after the fix exited 0, no skips.
