# AGENTS.md

The entry point for anyone, human or agent, working in this repository.
It is written so that work can be resumed without any memory of how it
was done: everything needed is in the files named here.

## What this is

p4-spectec-lean: a compiler from P4-SpecTec's AL to Lean 4, validated
per definition against a Lean port of the AL interpreter, plus a small P4
primitives library. The intended architecture and correctness contract are in
`docs/design.md`.

## Where things live

Documentation is split by purpose and audience:

- `docs/` contains polished, human-facing documentation of the artifact:
  what it is, how it works, what is trusted and what is checked. No
  agent-oriented plans, working reports or raw analysis dumps; nothing
  in it links into `.agents/`.
- `.agents/` describes the work: where it stands, what was decided and
  why, what is parked. Agent-oriented plans, working notes and reproducible
  analysis reports belong here. Committed working state, never runtime state.
  Logs and scratch output stay out of git.

| File | Holds |
|---|---|
| `docs/certification.md` | user-facing current capabilities, guarantees, limitations and certificate checks |
| `docs/performance.md` | measurement interpretation and reproduction; snapshots under `docs/performance/` |
| `docs/related-work.md` | related work on generated semantics, certification and P4 verification |
| `.agents/notes/design-review.md` | advisory design critique and proposed priorities |
| `.agents/notes/compiler-certification.md` | terminology discussion, closest certification precedents and sourced reading notes |
| `.agents/status.md` | current state, last checked evidence, open threads, next step |
| `.agents/decisions.md` | the decisions in force, by topic, each with its reason and date |
| `.agents/roadmap.md` | implementation milestones, paused work and backlog |
| `.agents/notes/` | live working notes |
| `.agents/notes/archive.md` | retired experimental history, artifacts and recovery instructions |
| `.agents/reviews/` | independent review reports for the current work |
| `.agents/notes/full-p4-reconnaissance.md` | full-P4 census findings and the remaining M3 phases |
| `.agents/notes/p4-census.json` | reproducible machine-readable capability census |
| `ExampleProofs/NanoP4FieldUpdate/` | bounded consumer proof, checked `Certificate.lean`, `Example.lean` walkthrough and colocated `test/` |

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
   the acceptance criteria and open design questions. User-facing current
   capabilities and limitations live in `docs/certification.md`; implementation
   progress and milestone planning live under `.agents/`.
4. `docs/lean-pitfalls.md`, before writing Lean in the code generator or
   the tactics: the traps already hit on this toolchain.

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
scripts/fetch-p4c.sh        # optional pinned full-P4 sample/include checkout under .artifacts/
scripts/check-mirror.py     # mirrored modules have upstream's constructors in order
lake env python3 scripts/check-library-boundaries.py  # libraries cannot import examples/tests
scripts/gen-keywords.sh     # regenerate the keyword table from Lean's token table
scripts/time-elab.sh <Lib>  # per-module build durations; see docs/performance.md
lake exe p4spectec-gen <export> --lib <Lib> [--update|--check]   # the compiler
test/diff/run.py            # rung 2: generated relation and interpreter port vs upstream's verdicts
lake exe check-quotes       # compiled Nano-P4 quotation vs current decoded export
lake exe check-print        # printer/builtin/interpreter vs pinned upstream observations
lake exe p4spectec-census exports/p4.al.json --check .agents/notes/p4-census.json
python3 scripts/spec-snapshot.py unpack exports/p4.al.json  # verified full-P4 extraction
```

Keep `main` green. Check exit codes, not output. CI
(`.github/workflows/ci.yml`) runs the same `scripts/check.sh` in Nix, with
the elan toolchain and `.lake` build artifacts cached by their pins, and
checks that the upstream submodule commit is on upstream `main` or on its
`gsoc-nano-spec` branch, where Nano-P4 lives until it lands on `main`
(decisions, "Pins"). The `upstream/p4-spectec` working tree is expected
to show local changes to four OCaml files: that is
`upstream/patches/0001-json-export.patch`, applied by
`scripts/build-upstream.sh`; `git -C upstream/p4-spectec checkout -- .`
removes it.

To bump the upstream pin: move the submodule, rebuild upstream, rerun the
exports (spec and programs), regenerate `NanoP4Spec/`, run the mirror
checks, re-read every module that mirrors a changed upstream file, and
record the new commit in `.agents/decisions.md`. The Nano-P4 spec is its
own submodule (`upstream/nano-p4-spec`) with the same procedure.

## Conventions

- **Agent instructions live in `AGENTS.md` alone.** Never create
  `CLAUDE.md` or `CLAUDE.local.md`; Claude-specific notes, if one is ever
  needed, belong in `.claude/rules/` (none exists; everything so far
  applies to any agent).
- **Correct by construction first** (`docs/design.md` section 2.1). Where
  upstream has a name, file split, constructor order or function
  structure, mirror it exactly. Every module that mirrors an upstream
  file says which in its header. Deviations forced by Lean go in the
  named list in the design, nowhere else.
- **File naming, by provenance.** A module that mirrors upstream OCaml
  sits at the OCaml file's path under `p4spec/lib/`, capitalised
  (`P4SpecTec/Lang/Il/Ast.lean` mirrors `lang/il/ast.ml`,
  `Interface/Builtin/Texts.lean` mirrors `interface/builtin/texts.ml`; a
  hyphenated directory is camel-cased, `Interp/InterpAl/Ctx.lean` mirrors
  `interp/interp-al/ctx.ml`); `scripts/check-mirror.py` derives the pairs
  from the paths, and a module of our own under those roots says "not a
  mirror". A generated module is
  named after its spec file verbatim (`NanoP4Spec/3.2-bits.lean`). Our
  own code follows Lean conventions (`Codegen/Emit.lean`, `Prelude/`),
  scripts and documents kebab-case.
- **The Lean package and namespace are `P4SpecTec`.** `SpecTec` alone
  names the Wasm-DSL project and is not used here.
- **Every external input is pinned**: P4-SpecTec by commit (the
  submodule), the Nix/OCaml environment by `flake.lock`,
  Lean by `lean-toolchain`, Batteries by tag in `lakefile.toml`.
- **Keep the repository lean; do not commit very large files.** Prefer
  reproducible generation or small, losslessly compressed snapshots for
  generated inputs; use checksum-pinned external artifacts when size or
  churn makes those unsuitable. Assess Git history growth, not just the
  current checkout. Rewriting published history requires explicit user
  agreement on the affected refs and disruption; do not infer it from a
  request to reduce repository size.
  `scripts/check-file-sizes.py` rejects tracked files above 5 MiB in
  either the index or working tree. No size exceptions are currently allowed.
- **JSON exports are committed, and so is generated Lean**, under
  `NanoP4Spec/` and `P4Spec/`, one module per upstream spec file (none
  for a file whose definitions all sit in a recursive group completed by a
  later file), with a
  grep-able header (`-- GENERATED by p4spectec-gen`). CI regenerates from
  the exports and fails on any diff; never hand-edit a generated file,
  regenerate it with `--update`. `P4SpecTec/Codegen/Keywords.lean` is
  generated too, from Lean's token table.
  Both spec snapshots are committed as `exports/<name>.al.json.gz` plus
  a raw SHA-256; the gate verifies and extracts the ignored JSON files.
  Full-P4 generation remains
  blocked on the constructs in `.agents/notes/full-p4-reconnaissance.md`, and the
  gate checks its decoded capability census until generation is supported.
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
- **Downstream examples live in `ExampleProofs/`**, outside default targets.
  The full gate explicitly builds them and runs colocated example tests.
  Reusable libraries (`P4SpecTec`, `P4Lib`, `NanoP4Spec`, `P4Spec`) must not
  import examples or test-only modules, directly or through local helpers.
  Keep reusable proof support in the library, not in an example namespace.
- **Generated code** carries a grep-able first line naming the generator
  and its input, and a fixed preamble of options. Generated modules live
  in their own libraries; default targets include the provided libraries,
  not the downstream examples.
- **Every decision the design does not settle** goes in
  `.agents/decisions.md` under its topic, with reason and date, and with
  a confidence and revisit trigger when uncertain.
- **`.agents/status.md` is updated at every checkpoint**: exact checks
  run, skipped gates, remaining obligations, next concrete step.
- **Commit messages** follow [Chris Beams](https://cbea.ms/git-commit/)
  and [Git's contribution guidance](https://git-scm.com/docs/SubmittingPatches).
  Use a specific, capitalized imperative subject under 50 characters,
  without a final period. Separate the body with a blank line and wrap
  prose at 72 columns (leave URLs and required trailers intact). Explain
  the prior problem, intended outcome and why this approach was chosen;
  include consequential alternatives or compatibility effects when
  relevant. Do not merely restate the diff or depend on chat/PR context.
  Keep one logical change per commit, including its tests and necessary
  documentation; split unrelated work instead of hiding it behind a
  vague subject. A PR explains the whole proposal; each commit explains
  its own change. Inspect the staged diff and final message before
  committing. Agent commits end with the required coauthor trailer.
- **Direct commits to `main` are the default for this personal project.**
  Use a feature branch only when isolation is useful. Keep independent
  review and the full local gate before pushing; check remote CI after
  pushing and address failures before declaring the work complete.
  Merge finished feature branches locally after review and validation,
  rerun the full gate if integration changes the tested tree, then push
  main and verify CI. Delete their local and remote refs promptly after
  verifying integration and successful main CI; remove any extra worktrees.
  Create a PR only when the user explicitly requests one. Repository
  protections still apply: if they prevent this workflow, report the
  conflict rather than bypassing them or changing settings.
- **Preserve meaningful commits when integrating a feature branch.**
  Prefer a fast-forward when possible; use a merge commit when needed to
  preserve coherent history. Do not rewrite published commits just to make
  history linear. For an explicitly requested PR, choose its merge strategy:
  use a merge commit when individual commits are coherent
  changes worth retaining, preserving their messages, hashes and the PR
  boundary. Squash when one logical change is spread across WIP/fixup
  commits; write a considered final message preserving rationale and
  coauthor attribution, not a concatenation of progress notes. Use
  rebase-and-merge only when a linear-history preference is explicit,
  accepting that GitHub changes commit hashes. Keep this workflow choice
  out of the PR description unless requested; a merge-strategy section
  is unnecessary. Requested PRs require independent review and passing
  remote CI for the final revision before merging.
- **When a PR is requested, its description is a durable explanation for
  reviewers.** Use a specific, outcome-focused title. Lead with the problem and why the
  change is needed; summarize the approach and consequential tradeoffs,
  not a file-by-file changelog. Supply enough context to stand alone
  without chat history; link supporting issues/designs rather than
  making readers reconstruct the rationale from them. Record exact
  validation commands and results, distinguishing local tests, remote
  CI, and checks not run. State meaningful risks, compatibility changes
  and scope limits. For complex diffs, give a short review order and
  identify where judgment is needed. Scale the length to the change;
  omit empty sections and boilerplate. Re-read the description against
  the final diff before merging and update stale claims.
  This follows [GitHub's review guidance](https://docs.github.com/en/pull-requests/concepts/helping-others-review-your-changes)
  and [Google's change-description guidance](https://google.github.io/eng-practices/review/developer/cl-descriptions.html).
- **AI disclosure in PRs:** one short sentence naming the authoring agent
  and exact model, e.g. "Authored by OpenAI Codex (GPT-6 Astra)." Verify
  attribution from active-session evidence, not a configured default;
  never guess. Keep review claims accurate elsewhere in the description:
  AI-agent review is not human review. Coauthor trailers remain required.
- **Checkpoint unfinished work explicitly.** Commit coherent, validated
  changes; isolate incomplete or failing experiments on a feature branch
  with a work-in-progress commit saying what it holds and lacks. Never push
  without a passing full local gate. If validation blocks publication,
  record the local commit and remaining obligations in the handoff.
- **A push is gated on the recorded exit status** of the full gate, never
  on a command that reads a log.
- **Independent read-only review after each step**, filed under
  `.agents/reviews/`; fix findings before pushing directly to main or
  merging a feature branch. Direct commits do not waive review.
- **Use subagents and worktrees when useful, choosing models by task.**
  Prefer Astra for difficult semantics/proof analysis, Sol for bounded
  implementation and tests, and Luna for straightforward inventories.
  Give each writer explicit file ownership or an isolated worktree.
  During authorized autonomous work, make reasonable reversible choices
  and record consequential decisions for later user review instead of
  waiting for routine input; do not weaken correctness requirements.

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
