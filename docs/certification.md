# Certification

What does a certificate from this project guarantee?

It connects a generated Lean definition to the meaning of its quoted
P4-SpecTec AL definition in our Lean reference interpreter, under explicit
input and environment assumptions. Certification happens when building the
language model, not separately for every P4 program that uses it.

A successful Lean build alone does not establish this connection. Nor does
a certificate prove that the reference interpreter faithfully implements
upstream OCaml or the intended P4 language.

## What is certified today?

Nano-P4 generates a Lean model that builds and is differential-tested against
the pinned upstream corpus. That executable support is broader than the
AL correspondence coverage below. Full-P4 support is not yet a usable
generated library. The README gives the short project status; this guide is
the user-facing account of current capabilities and their guarantees.

| Artifact | Checked claim | Boundary |
|---|---|---|
| Generated Nano-P4 refinement theorems | Every terminating reference outcome has a matching generated outcome | One direction, for the supported fragment and related inputs under the theorem's environment assumptions |
| Field-update certificate | Both directions of executable correspondence, representation coverage and initialization; distinct-name update commutation transfers to reference executions | One helper on a declared scalar source domain, not arbitrary P4 assignments |
| Generated relation soundness theorems | Successful generated execution implies the generated logical relation | Does not by itself connect that relation to AL or prove every relational witness executable |

The [generated coverage report](../NanoP4Spec/coverage.json) and its
[refinement index](../NanoP4Spec/Refinement.lean) currently record forward
AL theorems for 18 of 153 bodied definitions, all functions. Both come from
the same generation plan. They record exclusions, including blockers inherited
from dependencies or other members of a recursive group.
These counts are not a percentage of P4 language behavior certified.

Full-P4 production generation remains incomplete. Bounded stateful emitter
and proof fixtures do not constitute production full-P4 certification.
General generated-to-reference proofs are also not yet generated.

### Coverage metadata and checked evidence

`coverage.json` inventories the emitted per-definition claims. Schema version 1
records the library and export path, each callable's AL identifier and source
file, its recursive group and direct dependencies, theorem names and expected
types, and exclusions. The claim kinds distinguish forward AL refinement,
generated-run soundness and relation determinism. Types, source variables and
helper group theorems are outside this inventory; externs and builtins are
included as dependency boundaries, but excluded from the bodied denominator.

The report is metadata, not a certificate or a stored build verdict.
`check-coverage` regenerates it from the current export, requires an exact
match, then checks that every claimed declaration is a compiled theorem with
the expected type and only the allowed axioms. This also rejects omitted or
forged claims. Statement construction is shared with theorem emission; checking
does not independently prove that the generator chose the right contract.
Source identity still needs the separate freshness and quotation checks below.

The machinery belongs to `P4SpecTec`; the report belongs to the generated
library. Full-P4 will use the same machinery when production generation is
supported. Its capability census is an emission probe, not certificate coverage.
The stronger handwritten field-update certificate remains a separate consumer
artifact and does not increase the generated forward or reverse coverage.

### Implementation boundaries

These limitations describe the implementation, not the intended design:

- Production stateful planning is rejected even though stateful interpreters,
  emitters and bounded proof fixtures exist. Fresh-state tests are not full-P4
  generation or certification.
- Dynamic Nano packet and driver ports have bounded observation tests, not
  a complete generated typed target, Lean boot/STF implementation or proof of
  all packet behavior. The shared verify helper retains upstream's full-P4
  calling convention, which does not establish Nano source-level support.
- Printing is tested under supported hint policies, but lacks a general
  hinted-print correspondence theorem. Builtin, cast, iteration and
  higher-order proof coverage must be read from the generated exclusions,
  not inferred from executable support.
- Some legacy proof-facing matching/substitution helpers retain bounded-fuel
  false/identity fallbacks. Interpreter paths use checked APIs with explicit
  exhaustion and errors. Nonempty substitution through function types remains
  unsupported; the separate upstream type-fresh allocator is not modeled.
- Function-type comparison uses internal binder markers rather than allocating
  upstream type-fresh names. Its bounded comparison evidence does not cover
  later operations that could observe allocation history.

These exclusions prevent an end-to-end full-P4 claim. A consumer must use the
actual certificate's admitted domain and contracts, not assume that a callable
helper is covered by the translation proof.

## Reading a generated certificate

For a related reference input and generated input, a forward refinement
theorem says: if the reference interpreter finishes with a result at any
fuel, the generated definition produces a matching result. Success values
are related by the theorem's value relation; failures preserve their kind.
Exhausting the interpreter's fuel is not a semantic failure and imposes no
matching-result obligation. The theorem does not prove termination or
provide a reference execution for every generated result.

Check the actual theorem's hypotheses before using it. The current pure
certificates require dynamic guards to be disabled, no local function
overrides, and a global environment containing the quoted specification
(`HoldsSpec`). Their input relation (`Rel`) compares canonicalized runtime
values. It is not literal equality of all metadata, and does not justify
every observation, such as hinted printing.

There are further obligations when making a source-level claim:

- **Source identity:** the quotation must correspond to the intended export.
  `check-quotes` compares compiled Nano-P4 quotations with the decoded pinned
  export. The [comparison](../P4SpecTecTest/Quote.lean) erases regions and hints
  and omits source `VarD` declarations; expression/path type notes, type
  origins, input positions and ordering remain significant. This is a runtime
  check, not a kernel proof of the exporter.
- **Representation coverage:** every input in the claimed source domain must
  have an appropriate generated representation. A theorem conditional on
  `Rel` alone does not prove that no relevant input was left out.
- **Environment and dependencies:** establish the theorem's assumptions for
  the actual initialized environment and account for the called definitions.
  An extern signature alone is not a semantic contract.
- **Observations:** state which values, failure kinds and state changes the
  claim preserves. Canonical equality alone is not a printing or packet
  behavior theorem.

The precise refinement statement and proof machinery are in
[Design, section 5.1](design.md#51-the-refinement-theorem).

## A complete bounded example

The [field-update certificate](../ExampleProofs/NanoP4FieldUpdate/Certificate.lean)
packages proof terms for the actual generated `update_fieldValue`, its quoted
definition, representation coverage, successful reference initialization and
both directions of correspondence. The reverse direction supplies finite
reference execution witnesses rather than assuming termination.

Its source domain is finite ordered field lists with exact byte names and
scalar W/S/B/MATCH_KIND payloads. Duplicates retain first-match behavior;
absent names leave the list unchanged. The domain is a shape restriction,
not a P4 typing or numeric-range theorem. Nested payloads, printing and
externs are excluded.

The [worked example](../ExampleProofs/NanoP4FieldUpdate/Example.lean) transfers
commutation of updates to distinct names, with already evaluated replacement
values, to reference executions. It does not justify reordering arbitrary P4
assignments whose expressions may have effects. The proof and its mutation
tests stay beside the example code.

`ExampleProofs` is a downstream example library, not reusable semantics or
proof infrastructure. It is excluded from the default `lake build`, but the
full gate explicitly builds it and runs its colocated tests. Reusable
libraries cannot import example or test-only modules; the gate checks that
boundary, including indirect local imports. Reusable initialization and
refinement support remain under `P4SpecTec.Refine`.

## What remains trusted?

| Boundary | What supports it | What is not proved |
|---|---|---|
| Lean proof checking | Kernel checking and audits permitting only `propext`, `Classical.choice` and `Quot.sound` | Correctness of the Lean kernel itself |
| P4-SpecTec source to exported AL | Pinned upstream parser, elaborator, algorithmization and JSON exporter | Preservation of source-language meaning by those stages |
| Exported AL to Lean quotation | Decoding and `check-quotes` comparisons | Universal correctness of the exporter, decoder or quoting implementation |
| Lean reference semantics to upstream behavior | Side-by-side port review and differential tests, including bounded builtin and target observations | General equivalence of the OCaml and Lean interpreters, complete extern coverage or device fidelity |
| Generated code to Lean reference | Checked correspondence proofs for the recorded fragment | Definitions and input domains outside the proved claims |

The reference includes the runtime helpers and builtin implementations it
uses. A certificate is relative to that reference, not an independent
verification of those implementations. Known port deviations are recorded
in [Design, section 5.3](design.md#53-deviations-forced-by-lean).

The Lean executable toolchain is also trusted when running differential
tests. Passing tests is useful evidence about selected executions, not a
replacement for a theorem. Mutation tests check that selected incorrect
artifacts are rejected; they do not prove detection of every possible bug.

## Inspect and check

From the repository root:

```sh
nix develop --command scripts/check.sh
```

This is the same gate used by CI. It builds the Lean libraries and proofs,
checks generated-source and coverage freshness, theorem types and axioms, compares quotations,
runs differential tests, and replays the bounded example and its mutation
checks. A passing gate means those recorded checks passed, not that every
definition has an AL correspondence certificate.

For a focused inspection, start at the generated refinement index or the
field-update `Certificate` structure linked above. Follow the actual theorem
types and proof dependencies, rather than inferring guarantees from a file
name. Targeted checks, after the normal build has prepared dependencies, are:

```sh
nix develop --command lake build NanoP4Spec.Refinement
nix develop --command lake build ExampleProofs.NanoP4FieldUpdate.Certificate
nix develop --command lake exe check-quotes
nix develop --command lake exe check-coverage
nix develop --command lake exe check-coverage update_fieldValue
```

The optional AL identifier prints the entry's dependency closure and blockers
after checking the whole report. It does not discharge the theorem's input or
environment assumptions, or change an uncovered entry into a certificate.

These targeted commands do not replace the full gate. Changes to coverage
or theorem assumptions should update this guide with the code; detailed
theorem inventories and worked proofs remain in their own Lean modules.
