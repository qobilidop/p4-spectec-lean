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
   architecture, the verification ladder, the code organization, the
   named list of deviations from upstream (section 5.3), and the
   milestones.

## Environment

Lean comes from `elan`; `lean-toolchain` selects the version. The
upstream P4-SpecTec toolchain (OCaml 5.1, opam) is needed only to
regenerate `exports/`; `scripts/build-upstream.sh` builds it at the pin.
`flake.nix` provides both pinned, entered with `nix develop` or direnv;
the documentation does not assume Nix.

```
scripts/check.sh            # every gate CI runs; exit 0 is the verdict
scripts/build-upstream.sh   # build P4-SpecTec at the pin with our patches
scripts/export-spec.sh      # regenerate exports/*.il.json
```

Keep `main` green. Check exit codes, not output.

## Conventions

- **Agent instructions live in `AGENTS.md` alone.** Never create
  `CLAUDE.md` or `CLAUDE.local.md`; Claude-specific notes belong in
  `.claude/rules/`.
- **Correct by construction first** (`docs/design.md` section 2.1). Where
  upstream has a name, file split, constructor order or function
  structure, mirror it exactly. Every module that mirrors an upstream
  file says which in its header. Deviations forced by Lean go in the
  named list in the design, nowhere else.
- **The Lean package and namespace are `P4SpecTec`.** `SpecTec` alone
  names the Wasm-DSL project and is not used here.
- **Every external input is pinned**: P4-SpecTec by commit (the
  submodule), the opam repository by commit (`scripts/build-upstream.sh`),
  Lean by `lean-toolchain`, Batteries by tag in `lakefile.toml`.
- **JSON exports are committed**; generated Lean is not.
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
