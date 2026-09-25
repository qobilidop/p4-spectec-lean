# p4-spectec-lean

A compiler from [P4-SpecTec](https://github.com/kaist-plrg/p4-spectec)'s
AL (algorithmic language) to Lean 4, with per-definition validation against
a Lean port of the AL interpreter, plus a planned P4 primitives library.
AL is produced from the elaborated IL by upstream's algorithmization pass;
the representations and this trust boundary are explained in
[the design](docs/design.md#31-representations-and-the-compiler-boundary).

Status: milestones M1 and M2 done; M3 has started with the full P4 export
and a capability census. Full P4 generation still needs print hints,
indexed path updates, stateful fresh identifiers and some subtype bridges.
The Nano-P4 specification (34 files, 161 types, 76 functions, 77
relations) is rendered into Lean as executable definitions
(`partial_fixpoint`, no fuel) that kernel-check and agree with upstream's
interpreter on all 78 programs of upstream's Nano-P4 corpus, and as
inductive relations with a generated, machine-checked soundness theorem
for every one of the 77 relations. The AL interpreter is ported to Lean,
file by file, and agrees with upstream on the same corpus. Every
definition is also quoted as Lean data, and for 18 of them a generated
theorem proves that the ported interpreter run on the quoted definition
refines the generated code, which takes the code generator out of the
trusted base for those definitions. All 342 quoted Nano-P4 definitions
are compared with the decoded export in CI. The design is
[`docs/design.md`](docs/design.md); the entry point for working here is
[`AGENTS.md`](AGENTS.md).

## Layout

| Path | What |
|---|---|
| `P4SpecTec/` | core library: the IL and AL deep embeddings, the prelude and mirrored runtime, the AL interpreter port, the code generator, the proof tactics |
| `P4SpecTecTest/` | test-only modules for the core library |
| `P4Lib/` | P4 primitives for downstream users; independent of the generated specs |
| `NanoP4Spec/` | the pilot specification, generated from `exports/nano-p4.al.json` |
| `P4Spec/` | the full P4 specification, generated from `exports/p4.al.json` at M3 |
| `exports/` | committed AL snapshots (lossless gzip) and program values, the OCaml → Lean handoff |
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
python3 scripts/spec-snapshot.py unpack exports/nano-p4.al.json  # for direct tools; gate also does this
nix develop .#upstream           # OCaml side, only to rebuild P4-SpecTec and regenerate exports/
scripts/build-upstream.sh        #   (in that shell) apply the patches and build p4spectec
scripts/export-spec.sh nano-p4 upstream/nano-p4-spec   # regenerate exports/nano-p4.al.json
scripts/export-program.sh        # re-boot the Nano-P4 corpus and record upstream's verdicts
lake exe p4spectec-gen exports/nano-p4.al.json --lib NanoP4Spec --update   # regenerate NanoP4Spec/
```

Lean itself is installed by elan from `lean-toolchain`, not from nixpkgs,
which lags Lean releases; the pin is the file, the lock is the toolchain
version it names.

Spec snapshots are checksum-verified before extraction. The gate rejects
tracked files above 5 MiB; growing artifacts belong in external,
checksum-pinned storage rather than an ever-growing Git history.

If you use [direnv](https://direnv.net/), an `.envrc` containing `use flake`
enters the default shell on `cd`. It is ignored by git as a personal
convenience; the project's tooling is the flake.

## License

Apache-2.0. See [LICENSE](LICENSE).
