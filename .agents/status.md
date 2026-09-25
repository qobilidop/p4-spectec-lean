# Status

Where the work stands now. Updated at every checkpoint; holds current
state only.

Last updated: 2026-09-25. **Active: nothing.** The design is agreed and
the scaffolding is in place; the next scope is milestone M1 (Nano-P4,
rungs 1 and 2) and needs the user's go-ahead.

## Current state

| Scope | Result | Revision |
|---|---|---|
| Design | agreed; revised after the prior-art design review (thesis and claims, refinement theorem, recursion strategy, per-file text emission, timing at M1, encodings) | this commit |
| Scaffolding | Lake package, agent state, gate stubs, upstream submodule at the pin | `7d613a1` |
| Engineering conventions | prior-art study applied: build flags, linters, test driver, CI, text and import checks | this commit |

The library roots are doc-comment-only modules plus one smoke test.
`scripts/check.sh` checks layout, the absence of `CLAUDE.md`, that
`docs/` does not link into `.agents/`, text hygiene, that every module is
imported by its root, then `lake build --wfail` and `lake test`.

## Last checked evidence

2026-09-25, at the conventions commit, `nix develop --command
scripts/check.sh`: exit 0. Lean `v4.34.1`, Batteries at the revision
`lake-manifest.json` records, four libraries and the test library built,
the smoke test's `#guard` and `#guard_msgs` pass. CI has not run yet (no
remote). No differential test, export, or upstream build exists yet.

## Open threads

- Milestone M1 has not started. Its first concrete steps: build
  upstream in the `upstream` Nix shell (verifies the OCaml version
  risk), the JSON export patch (`upstream/patches/0001-json-export.patch`;
  IL `def` and `spec` need the deriving added), then
  `P4SpecTec/IL/Ast.lean` mirroring `p4spec/lib/lang/il/ast.ml`.
- Before the interpreter port in M2: decide the failure/divergence
  split of its return type (design section 5.1), since `<|>` on
  `Option` blocks `partial_fixpoint`.
- Open points in `docs/design.md` section 10: harness language, fuel
  policy location, meta-circular spec, Lean version policy.
- The `upstream` Nix shell has been entered but P4-SpecTec has not been
  built in it; nixpkgs package versions differ from upstream's README pins
  (see decisions, "Environment"). First M1 step verifies the build.
- Risk noted from Sail: a 246-constructor inductive elaborated slowly
  (rems-project/sail#1049). Per-file timing is added at M3.

## Blocked

Nothing.
