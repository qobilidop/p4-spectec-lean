# P4-SpecTec to Lean 4

A [certifying compiler](https://xavierleroy.org/publi/compiler-certif.pdf#page=2)
from [P4-SpecTec](https://github.com/kaist-plrg/p4-spectec)’s algorithmic language
(AL) to executable definitions and inductive relations in Lean 4.

## Status

- [Nano-P4](https://github.com/pacokwon/nano-p4-spec): generated semantics,
  differential tests, and a checked verification example. Certification
  coverage is partial.
- Full P4 support and broader proof coverage are in progress.

## Rationale

### Why this project?

We aim to provide a reference for P4 verification in Lean 4 that stays aligned
with the evolving language specification.

- **Follow the evolving P4 specification.** P4-SpecTec has been
  [conditionally adopted as the official P4 language specification authoring toolchain](https://p4lang.github.io/p4-spec/docs/P4-16-working-spec.html).
  Generating our Lean model from it helps us track specification changes.
- **Support proof-friendly models.** Other Lean libraries can model P4 in
  ways that make proofs easier, then prove agreement with this reference.

### Why a certifying compiler?

Our goal is to generate a correctness proof alongside each translated definition,
rather than prove the generator itself correct. This lets us adapt the generator
as P4-SpecTec evolves while independently checking its outputs in Lean.

Certification happens when we build the language model. Downstream users can
reuse that checked model without repeating certification for each P4 program.

## Design principles

- **Mirror the reference semantics.** Preserve upstream structure and names
  rather than independently redesigning the reference model.
- **Certify generated models.** Check correspondence with an explicit AL
  reference, not just whether the generated code compiles.

## Build and check

Requires [Nix](https://nixos.org/download/) with flakes enabled. From the
repository root:

```sh
git submodule update --init
nix develop --command scripts/check.sh
```

This builds the project and runs the checks used by CI.

`nix develop --command lake build` builds the libraries without downstream
examples. Build those explicitly with `nix develop --command lake build ExampleProofs`;
the full check above includes them.

## Start here

- [Checked field-update proof](ExampleProofs/NanoP4FieldUpdate/Example.lean)
- [Certification and its limits](docs/certification.md)
- [Design](docs/design.md)
- [Performance](docs/performance.md)
- [Related Work](docs/related-work.md)
- [Development guide](AGENTS.md)

## License

[Apache-2.0](LICENSE).
