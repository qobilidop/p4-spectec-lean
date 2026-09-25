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
- Upstreaming the JSON export patch.
