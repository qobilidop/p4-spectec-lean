# Status

Where the work stands now. Updated at every checkpoint; holds current
state only.

Last updated: 2026-09-25. **Active: nothing.** The design is agreed and
the scaffolding is in place; the next scope is milestone M1 (Nano-P4,
rungs 1 and 2) and needs the user's go-ahead.

## Current state

| Scope | Result | Revision |
|---|---|---|
| Design | agreed, `docs/design.md` | `051ce06` |
| Scaffolding | Lake package, agent state, gate stubs, upstream submodule at the pin | this commit |

The library roots are doc-comment-only modules; `lake build` succeeds on
them. `scripts/check.sh` checks layout, the absence of `CLAUDE.md`, that
`docs/` does not link into `.agents/`, and runs the Lean build.

## Last checked evidence

2026-09-25, at the scaffolding commit, `nix develop --command
scripts/check.sh`: exit 0. Lean `v4.34.1` installed by elan, Batteries
cloned at the revision `lake-manifest.json` records, all four libraries
built. No differential test, export, or upstream build exists yet.

## Open threads

- Milestone M1 has not started. Its first concrete step is the JSON
  export patch to upstream (`upstream/patches/0001-json-export.patch`),
  then `P4SpecTec/IL/Ast.lean` mirroring `p4spec/lib/lang/il/ast.ml`.
- Open points in `docs/design.md` section 10: harness language, fuel
  policy location, meta-circular spec, Lean version policy.

## Blocked

Nothing.
