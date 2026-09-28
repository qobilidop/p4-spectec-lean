# Status

Session handoff, updated 2026-09-28. N3 is authorized and in progress on the local
feature branch `n3-core` (not pushed); `main` still holds the first N3 checkpoint.
N4–N6 have not started and full-P4 M3 remains paused.

## Verified checkpoint on `main`

N0/N1/N2 are complete (closure `d85e82c`, CI 36316496027). The first N3 checkpoint
(68 of 153 bodied definitions two-way) and the replay tooling are on `main`, with
passing full local gates; details in the
[Nano plan](notes/nano-certification.md#n3-first-checkpoint-in-progress).

## Work in progress on `n3-core`

WIP commits (each message states what it holds and lacks): `2018bf5`, `97754b5`,
`608a0a3`, `9f28d30`; later tactic fixes are uncommitted in the main worktree.

- Fragment gate: every one of the 153 bodied definitions is admitted and emitted with
  forward and reverse theorems (extern-dependent ones under the abstract
  `externsContract`); relation rule paths are flattened like `invoke_defined_rel`;
  group budgets scale with rule paths (draft decisions in the session scratch, to be
  recorded in `decisions.md`).
- Last full build (`lake build NanoP4Spec` at `9f28d30` plus fixes): only
  `TableEntry_ok`, `TableActions_ok` and `ParserStateList_ok` failed. The first and
  last now pass by replay with the current tactics; `TableActions_ok` (overlapping
  singleton and cons paths over a list) is being fixed. Modules downstream of these
  three (the rest of the typing chain to `Program_ok`, `NanoSwitch_init`) have not
  been checked yet. The whole evaluation group, `Call_eval`'s six-member group
  included, builds.
- Domain evidence (the 64 N3-owned `domain` obligations): the evaluation side needs
  the runtime-inclusive profile (draft decision "Runtime-inclusive evaluation
  domain"). Done: `Source.Valid` takes a `Domain` with a runtime alternative
  (source profile unchanged), `SourceRuntime.lean` (monotonicity, checked closure
  certificate, codec lifting). In progress on branch `n3-runtime` (worktree
  `../p4-spectec-lean-runtime`, delegated): generated runtime codecs for the
  `value`/`evalContext` closure. Remaining: runtime entry/producer/call-admission
  claims, producers for multi-output and multi-group relations, the five
  "argument note differs" call admissions, the extern relation's domain binding, and
  the completion manifest.

## Resume point

1. Finish `TableActions_ok`, then run a full `lake build NanoP4Spec` and fix the
   downstream typing-chain certificates.
2. Integrate `n3-runtime`, then emit the runtime-profile domain claims and teach
   `scripts/nano-certification.py` to accept them for runtime-closure callables.
3. Record the draft decisions, update the Nano plan and `docs/certification.md`,
   regenerate `completion.json`, run `--require-owned N3` and the full gate, get an
   independent review, then squash the WIP history into coherent commits.

Iteration: `scripts/replay-cert.py` in the main tree with `--no-build` after
`lake build P4SpecTec` (never while a full build runs there); it is faithful only for
tactic-only changes.

## Maintenance and repository state

Worktrees: main (`n3-core`), `../p4-spectec-lean-replay` (scratch replays, detached),
`../p4-spectec-lean-runtime` (`n3-runtime`). Older local branches `n3-decl-load` and
`n3-expr-eval` are superseded by `n3-core`. The expected upstream exporter patch
remains applied. No source pins changed.
