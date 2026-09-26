# P4-SpecTec in Lean 4

A compiler from [P4-SpecTec](https://github.com/kaist-plrg/p4-spectec)’s
algorithmic language (AL) to executable definitions and inductive relations
in Lean 4.

[Nano-P4](https://github.com/pacokwon/nano-p4-spec) is the current working
example. Full P4 support and proof coverage are incomplete.

## Why this project?

- **Follow the evolving P4 specification.** P4-SpecTec has been
  [conditionally adopted as the official P4 specification authoring toolchain](https://p4lang.github.io/p4-spec/docs/P4-16-working-spec.html).
  Generating our Lean model from it helps us track specification changes.
- **Provide a reference for verification in Lean 4.** Use the model to prove
  properties of P4. Other Lean libraries can build models that make proofs
  easier, then prove that those models agree with this reference.

## Build and check

Requires [Nix](https://nixos.org/download/) with flakes enabled. From the
repository root:

```sh
git submodule update --init
nix develop --command scripts/check.sh
```

This builds the project and runs the checks used by CI.

## Start here

- [Checked field-update proof](NanoP4Proofs/FieldUpdate/Example.lean)
- [Design and verification boundaries](docs/design.md)
- [Development guide](AGENTS.md)

## License

[Apache-2.0](LICENSE).
