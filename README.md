# p4-spectec-lean

A compiler from [P4-SpecTec](https://github.com/kaist-plrg/p4-spectec)'s
IL to Lean 4, validated per definition against a Lean formalization of the
IL, plus a small P4 primitives library.

Status: design agreed, scaffolding in place, no code yet. The design is
[`docs/design.md`](docs/design.md); the entry point for working here is
[`AGENTS.md`](AGENTS.md).

## Layout

| Path | What |
|---|---|
| `P4SpecTec/` | core library: IL deep embedding, IL semantics, prelude, codegen, validation tactic |
| `P4SpecTecTest/` | test-only modules for the core library |
| `P4Lib/` | P4 primitives for downstream users; independent of the generated specs |
| `NanoP4Spec/` | the pilot specification, generated from `exports/nano-p4.il.json` |
| `P4Spec/` | the full P4 specification, generated from `exports/p4.il.json` |
| `exports/` | committed JSON exports of the IL, the OCaml → Lean handoff |
| `upstream/` | P4-SpecTec as a pinned submodule, and our patches to it |
| `test/diff/` | the differential-testing harness |
| `scripts/` | the gates and the export scripts |
| `docs/` | the design |
| `.agents/` | agent working state: status, decisions, roadmap |

## Development

The development environment is defined by `flake.nix` and pinned by
`flake.lock`; CI uses the same shells. Install [Nix](https://nixos.org/download/)
with flakes enabled, then:

```
git submodule update --init      # P4-SpecTec at the pin (its p4c submodule is not needed)
nix develop                      # Lean side: elan installs the toolchain lean-toolchain names
lake build                       # the Lean packages
scripts/check.sh                 # every gate CI runs; exit 0 is the verdict
nix develop .#upstream           # OCaml side, only to rebuild P4-SpecTec and regenerate exports/
```

Lean itself is installed by elan from `lean-toolchain`, not from nixpkgs,
which lags Lean releases; the pin is the file, the lock is the toolchain
version it names.

If you use [direnv](https://direnv.net/), an `.envrc` containing `use flake`
enters the default shell on `cd`. It is ignored by git as a personal
convenience; the project's tooling is the flake.

## License

Apache-2.0. See [LICENSE](LICENSE).
