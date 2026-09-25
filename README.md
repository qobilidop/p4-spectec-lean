# p4-spectec-lean

A compiler from [P4-SpecTec](https://github.com/kaist-plrg/p4-spectec)'s
IL to Lean 4, validated per definition against a Lean formalization of the
IL, plus a small P4 primitives library.

Status: milestone M1 done. The Nano-P4 specification (34 files, 161
types, 76 functions, 77 relations) is rendered into Lean as executable
definitions that kernel-check and agree with upstream's interpreter on
all 78 programs of upstream's Nano-P4 corpus. The design is
[`docs/design.md`](docs/design.md); the entry point for working here is
[`AGENTS.md`](AGENTS.md).

## Layout

| Path | What |
|---|---|
| `P4SpecTec/` | core library: the IL and AL deep embeddings, the prelude and mirrored runtime, the code generator (the IL semantics and validation tactic arrive at M2) |
| `P4SpecTecTest/` | test-only modules for the core library |
| `P4Lib/` | P4 primitives for downstream users; independent of the generated specs |
| `NanoP4Spec/` | the pilot specification, generated from `exports/nano-p4.al.json` |
| `P4Spec/` | the full P4 specification, generated from `exports/p4.al.json` at M3 |
| `exports/` | committed JSON exports of the IL, the OCaml → Lean handoff |
| `upstream/` | P4-SpecTec and the Nano-P4 spec as pinned submodules, and our patches |
| `test/diff/` | the differential-testing harness |
| `scripts/` | the gates and the export scripts |
| `docs/` | the design and the elaboration-time table |
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
scripts/build-upstream.sh        #   (in that shell) apply the patches and build p4spectec
scripts/export-spec.sh nano-p4 upstream/nano-p4-spec   # regenerate exports/nano-p4.al.json
scripts/export-program.sh        # re-boot the Nano-P4 corpus and record upstream's verdicts
lake exe p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --update   # regenerate NanoP4Spec/
```

Lean itself is installed by elan from `lean-toolchain`, not from nixpkgs,
which lags Lean releases; the pin is the file, the lock is the toolchain
version it names.

If you use [direnv](https://direnv.net/), an `.envrc` containing `use flake`
enters the default shell on `cd`. It is ignored by git as a personal
convenience; the project's tooling is the flake.

## License

Apache-2.0. See [LICENSE](LICENSE).
