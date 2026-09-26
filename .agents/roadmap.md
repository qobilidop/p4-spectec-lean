# Roadmap

Implementation planning, separate from the intended architecture in
`docs/design.md`. The first consumer
checkpoint, brought forward from M4, is complete: bounded field-update
correspondence and commutation are checked in `NanoP4Proofs/FieldUpdate/`.
No IL backend or broad redesign is scheduled. Broader M3 and the backlog
below remain paused; an item becomes work only when the user scopes it.

## Milestone register

Moved here from Design so milestones do not masquerade as architecture:

- M1: Nano-P4 generation, kernel checking, upstream export and differential
  replay. Closed; current evidence is in status and Certification.
- M2: generated logical relations, forward AL certificates and reusable proof
  support. Closed as a bounded fragment, not complete Nano certification.
- M3: full-P4 generation, effect integration, broader correspondence and
  target support. M3A export/census is closed; broader M3 remains incomplete.
  Full-P4 reconnaissance holds the remaining technical phases and exclusions.
- M4: reusable P4 consumer libraries, broader examples and documentation site.
  The first bounded consumer proof was brought forward and is complete;
  that does not close the broader library/interface work.

The approved library/example separation remains a distinct later task:
`ExampleProofs/NanoP4FieldUpdate/`, with examples removed from default client
builds but retained explicitly in the gate. No implementation change is part
of the documentation checkpoint.

## Backlog

- A random well-typed P4 program generator, either p4c's p4smith or
  enumeration of derivations of the generated inductive typing relation.
- Generating the IL semantics from upstream's meta-circular spec, if it
  matures, keeping one hand-written semantics at the bottom of the stack.
- A shallow embedding of P4 programs (program → Lean functions), proved
  correct against the generated deep semantics.
- A P4 parser in Lean as a verified replacement for upstream's.
- Upstreaming the JSON export patch (`elab -json`, `algo -json`,
  `nano parse -json`).
- Returning the P4-SpecTec pin to upstream `main` once Nano-P4 lands there
  (the pin follows `gsoc-nano-spec` today; decisions, "Pins").
- Readability of generated code: fewer temporaries, flatter alternatives,
  hard-wrapped headers. Not needed for correctness; wanted for review.

Rung 3 beyond M2's fragment (the M3 work order, in order of payoff):

- Builtin calls: a lemma per builtin relating `Builtin.Call.invoke` on
  values to the generated wrapper; then iterated expressions and premises
  (`Ctx.sub_list`/`mapM` against `List.map`/`mapM`); then casts and
  subtype checks (per-type lemmas about `upcast`/`downcast`/`Match.sub`
  against the generated bridges); then indexing, slicing, membership,
  type parameters, externs. The first relation to enter the fragment
  exercises the relation form of the statement in the build.
- `Match.sub_`, `Match.check'` and `Subst.subst_typ_inner` answer
  something at fuel zero instead of diverging (the class of wart fixed in
  `is_iter_var_exp`); recursion on size, as there, before casts enter the
  fragment.
- Broader codegen mutation checks (mutate the generator, require rung 3 to
  fail). The colocated field-update tests replay an emitted AL refinement
  proof against one mutated generated helper; this is bounded artifact
  sensitivity, not mutation coverage of the generator implementation.
- A spec tuple nested inside a tuple needs a wrapper type: `ToValue (α ×
  β)` flattens.

Website, sequenced against the milestones (decisions, "Documentation"):

- After M1: doc-gen4 API reference under `docs/api/`, published to GitHub
  Pages under `api/` by a Pages workflow running in the Nix shell.
- At M4: a Verso site under `website/` with the design narrative and a
  checked tutorial against the frozen public surface, doc-gen4 output
  beside it, same Pages site.
