# AGENTS.md

The entry point for anyone, human or agent, working in this repository.
It is written so that work can be resumed without any memory of how it
was done: everything needed is in the files named here.

## What this is

p4-spectec-lean: a compiler from P4-SpecTec's IL to Lean 4, validated
per definition against a Lean formalization of the IL, plus a small P4
primitives library. The design, principles and milestones are in
`docs/design.md`.

## Where things live

Documentation is split by what it describes, not by who reads it:

- `docs/` describes the artifact: what it is, how it works, what is
  trusted and what is checked. Written for people; nothing in it links
  into `.agents/`.
- `.agents/` describes the work: where it stands, what was decided and
  why, what is parked. Committed narrative state, never runtime state.
  Logs and scratch output stay out of git.

| File | Holds |
|---|---|
| `.agents/status.md` | current state, last checked evidence, open threads, next step |
| `.agents/decisions.md` | the decisions in force, by topic, each with its reason and date |
| `.agents/roadmap.md` | backlog beyond the milestones in the design |
| `.agents/notes/` | live working notes |
| `.agents/reviews/` | independent review reports for the current work |

`.agents/` is a hidden directory; `rg` and `fd` skip it unless told to
include hidden files. Git history is the archive; nothing is tagged.

## Read first, in this order

1. `.agents/status.md`: where the work stands and what is open.
2. `.agents/decisions.md`: what is decided and why. Overrule an entry by
   rewriting it in place with the new date and reason.
3. `docs/design.md`: the goal, the principles (section 2), the
   architecture, the verification ladder with the refinement theorem
   (section 5.1), the code organization, the named list of deviations
   from upstream (section 5.3), the per-construct encodings (5.4), and
   the milestones.

## Environment

The environment is `flake.nix`, pinned by `flake.lock`, and every
command in this repository is run inside it: `nix develop` for the Lean
side (elan installs the toolchain `lean-toolchain` names) and
`nix develop .#upstream` for building the pinned P4-SpecTec to regenerate
`exports/`. CI uses the same shells. A personal `.envrc` is ignored by
git.

```
scripts/check.sh            # every gate CI runs; exit 0 is the verdict
scripts/build-upstream.sh   # build P4-SpecTec at the pin with our patches (upstream shell)
scripts/export-spec.sh      # regenerate exports/<name>.al.json (upstream shell)
scripts/export-program.sh   # re-boot the Nano-P4 corpus with upstream's verdicts (upstream shell)
scripts/check-mirror.py     # mirrored modules have upstream's constructors in order
scripts/gen-keywords.sh     # regenerate the keyword table from Lean's token table
scripts/time-elab.sh <Lib>  # per-module elaboration times, to docs/timing-<lib>.md
lake exe p4spectec-gen <export> --lib <Lib> [--update|--check]   # the compiler
test/diff/run.py            # rung 2: generated typing relation vs upstream's verdicts
```

Keep `main` green. Check exit codes, not output. CI
(`.github/workflows/ci.yml`) runs the same `scripts/check.sh` after
`lean-action` installs the toolchain and restores the `.lake` cache, and
checks that the upstream submodule commit is on upstream `main`.

To bump the upstream pin: move the submodule, rebuild upstream, rerun the
exports (spec and programs), regenerate `NanoP4Spec/`, run the mirror
checks, re-read every module that mirrors a changed upstream file, and
record the new commit in `.agents/decisions.md`. The Nano-P4 spec is its
own submodule (`upstream/nano-p4-spec`) with the same procedure.

## Conventions

- **Agent instructions live in `AGENTS.md` alone.** Never create
  `CLAUDE.md` or `CLAUDE.local.md`; Claude-specific notes belong in
  `.claude/rules/`.
- **Correct by construction first** (`docs/design.md` section 2.1). Where
  upstream has a name, file split, constructor order or function
  structure, mirror it exactly. Every module that mirrors an upstream
  file says which in its header. Deviations forced by Lean go in the
  named list in the design, nowhere else.
- **File naming, by provenance.** A module that mirrors upstream OCaml
  sits at the OCaml file's path under `p4spec/lib/`, capitalised
  (`P4SpecTec/Lang/Il/Ast.lean` mirrors `lang/il/ast.ml`,
  `Interface/Builtin/Texts.lean` mirrors `interface/builtin/texts.ml`);
  `scripts/check-mirror.py` derives the pairs from the paths, and a module
  of our own under those roots says "not a mirror". A generated module is
  named after its spec file verbatim (`NanoP4Spec/3.2-bits.lean`). Our
  own code follows Lean conventions (`Codegen/Emit.lean`, `Prelude/`),
  scripts and documents kebab-case.
- **The Lean package and namespace are `P4SpecTec`.** `SpecTec` alone
  names the Wasm-DSL project and is not used here.
- **Every external input is pinned**: P4-SpecTec by commit (the
  submodule), the opam repository by commit (`scripts/build-upstream.sh`),
  Lean by `lean-toolchain`, Batteries by tag in `lakefile.toml`.
- **JSON exports are committed, and so is generated Lean**, under
  `NanoP4Spec/` and `P4Spec/`, one module per upstream spec file, with a
  grep-able header (`-- GENERATED by p4spectec-gen`). CI regenerates from
  the exports and fails on any diff; never hand-edit a generated file,
  regenerate it with `--update`. `P4SpecTec/Codegen/Keywords.lean` is
  generated too, from Lean's token table.
- **Build hygiene.** `scripts/check.sh` is the gate: `lake build --wfail`
  (a warning fails, and a `sorry` is a warning), `lake test`, every module
  imported by its library root, no trailing whitespace, Lean lines at most
  100 characters, precise imports (no bare `import Lean`). Never set
  `warningAsError` in Lake options; it rewrites the severities that
  `#guard_msgs` tests observe.
- **Docstrings on every declaration** in a client-importable library
  (`linter.missingDocs` is on package-wide, off in the test library).
  Modules open with a `/-! -/` docstring. A module that mirrors an
  upstream file names it there.
- **Naming.** Modules that mirror upstream OCaml keep upstream's names,
  including `snake_case`, so the side-by-side audit holds. Our own code
  (codegen, prelude, P4Lib) follows Lean style: `lowerCamelCase` for
  definitions and theorems, `UpperCamelCase` for types and namespaces.
- **Tests** are `#guard` and `#guard_msgs` files under `P4SpecTecTest/`,
  built by `lake test`. Every advertised theorem is followed by a
  `#guard_msgs in #print axioms` check naming its exact axiom set; every
  generated theorem by `#audit_axioms`, which fails on any axiom outside
  `propext`, `Classical.choice` and `Quot.sound`. `native_decide` is not
  used in proofs: it adds the `Lean.ofReduceBool` axiom, which the audit
  rejects.
- **Generated code** carries a grep-able first line naming the generator
  and its input, and a fixed preamble of options. Generated modules live
  in their own library so a default build can skip them.
- **Every decision the design does not settle** goes in
  `.agents/decisions.md` under its topic, with reason and date, and with
  a confidence and revisit trigger when uncertain.
- **`.agents/status.md` is updated at every checkpoint**: exact checks
  run, skipped gates, remaining obligations, next concrete step.
- **Commits**: Chris Beams' seven rules; imperative subject under 50
  characters; a body that says why, not what. One logical change per
  commit. Agent commits end with a `Co-Authored-By: <agent> <email>`
  trailer. Small self-contained changes go directly to `main`;
  multi-commit or build-affecting work gets a branch.
- **Unfinished work is a pushed branch** with a work-in-progress commit
  saying what it holds and lacks, never an uncommitted worktree.
- **A push is gated on the recorded exit status** of the full gate, never
  on a command that reads a log.
- **Independent read-only review after each step**, filed under
  `.agents/reviews/`, findings fixed on `main`.

## Checkpoints and compaction

At each checkpoint, update `.agents/status.md`, any changed decision, and
this file when scope or navigation changes. When a milestone closes, or
when the resume read grows past roughly a thousand lines, compact
`.agents/`: rewrite status and decisions to what is true now, delete
finished notes and reviews, promote notes that describe the artifact into
`docs/`. Compaction changes no claim. Git history is the archive.

## Resuming

Read the files above in order. Nothing needed to continue the work lives
outside the repository. If `.agents/status.md` says nothing is active,
ask for a scope before starting one.
