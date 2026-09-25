# Roadmap

Backlog beyond the four milestones in `docs/design.md`. Nothing here is
active; an item becomes work only when the user scopes it.

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

Website, sequenced against the milestones (decisions, "Documentation"):

- After M1: doc-gen4 API reference under `docs/api/`, published to GitHub
  Pages under `api/` by a Pages workflow running in the Nix shell.
- At M4: a Verso site under `website/` with the design narrative and a
  checked tutorial against the frozen public surface, doc-gen4 output
  beside it, same Pages site.
