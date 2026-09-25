# Status

Where the work stands now. Updated at every checkpoint; holds current
state only.

Last updated: 2026-09-25. **Milestone M1 (Nano-P4, rungs 1 and 2) is
closed; nothing is active.** The executable rendering of the Nano-P4
spec builds, kernel-checks, and agrees with upstream on the whole Nano-P4
corpus. M2 (rung 3 and the lemma library; design section 10) is the next
scope; the `Prop` encoding of relations and the fuel-free recursion
strategy are its first items (open threads below).

## Current state

| Scope | Result | Revision |
|---|---|---|
| Design | agreed; revised for M1's findings (AL not IL as the export, fuel, module grouping, naming rule) | `main` |
| Upstream build | P4-SpecTec at the `gsoc-nano-spec` pin builds in the `upstream` Nix shell on nixpkgs' OCaml 5.5 with `scripts/build-upstream.sh` | `main` |
| Export | `elab -json`, `algo -json` and `nano parse -json` from `upstream/patches/0001-json-export.patch`; `exports/nano-p4.al.json` (8.5 MB), 78 booted programs with upstream's verdicts under `exports/programs/nano-p4/` | `main` |
| Deep embedding | `P4SpecTec/Lang/Il/Ast.lean`, `Lang/Al/Ast.lean` and their JSON decoders mirror `lang/il/ast.ml`, `lang/al/ast.ml` at the same paths; `scripts/check-mirror.py` derives every mirrored pair from the paths and checks constructor lists and order | `main` |
| Prelude | `Runtime/Value/Value.lean` and `Interface/P4/Unparse.lean` mirror value comparison and the printer; `Interface/Builtin/` ports every builtin file, with unit tests in `P4SpecTecTest/Builtins.lean`; `Prelude/` holds `ToValue`/`OfValue`, numerics and iteration helpers | `main` |
| Codegen | `lake exe p4spectec-gen`: types, subtype bridges, functions, builtins, relations (executable), `Externs` class, per-file modules, `--check`/`--update` | `main` |
| Generated | `NanoP4Spec/`, 28 modules named after the spec files, 13.5k lines, builds with `--wfail`; 161 types, 76 functions, 77 relations | `main` |
| Rung 2 | `test/diff/run.py`: 78 of 78 programs agree with the AL interpreter's `Program_ok` verdict (48 pass, 30 fail: 32 positive, 21 negative, 25 exercises); for the 48 that pass, the output typing context equals upstream's value | `main` |
| Timing | `docs/timing-nano-p4.md`: about 12 s over 28 modules; `1-syntax` at about 3 s is the largest | `main` |

## Last checked evidence

2026-09-25, on `main` at `d8003ec` (M1 merged, plus the CI fix for the
pin check), CI run 36116792883: exit 0. Locally, on the same tree,
`nix develop --command scripts/check.sh`: exit 0. That run covered the
layout and text checks, the path-driven mirror check (20 modules),
`lake build --wfail` of every library including the 28 generated modules,
`lake test` (the decode test: 8/26/76/161/1/77/1 definitions by kind; the
builtin unit tests), the keyword-table check, `p4spectec-gen --check` (28
files up to date), and the harness: 78 of 78 verdicts agree with the AL
interpreter, and the 48 output typing contexts equal upstream's values.
Upstream itself was built with `scripts/build-upstream.sh` in
`nix develop .#upstream` (OCaml 5.5.0, dune 3.23.1 from the locked
nixpkgs).

## Open threads

- **`Prop` encoding of relations (design section 4.1) not generated.** The
  executable encoding is complete; the `Prop` inductive per relation is
  deferred to M2 because its treatment of function calls depends on the
  fuel-free recursion strategy M2 decides (a hypothesis `f args = some r`
  needs a fuel today). Recorded in decisions, "Generated code".
- **Packet leg of rung 2** (nano-switch simulation) is M3 by the design
  ("target instances arrive with the packet leg"); the `Externs` class is
  generated, no instance exists yet.
- **Recursion strategy is uniform fuel** (every generated function and run
  function takes `fuel : Nat` first; recursive groups consume one per
  call). The decision's "structural first" ordering is revisited at M2 with
  the counts from Nano-P4: 12 recursive function groups, 8 recursive
  relation groups (`lake exe p4spectec-gen` plan).
- Path updates with indexing (`e[p[i] = v]`) are rejected by codegen;
  Nano-P4 has none. Needed for M3.
- `fresh_typeId` (a stateful builtin) has no port; not used by Nano-P4.
- `print` hints are rejected by codegen (Nano-P4 has none); hint-driven
  printing is needed for the full spec at M3. The AL's `subcheck` is not
  consulted for subtype checks: codegen asserts that a shared case has the
  same argument types on both sides and fails otherwise.
- The M1 review (in git history, `.agents/reviews/m1-nano-p4.md` before
  the M1 close) is fully dispositioned; its two high findings are fixed on
  `main`. Its open fidelity notes are the last item below.
- Sizes: `exports/programs/nano-p4/` is 11 MB of JSON (regions with paths
  dominate). Acceptable; revisit if the full corpus at M3 is unwieldy.
- Generated code is functional but verbose (a temporary per hoisted
  call, alternatives nested in parentheses). Readability work is a
  candidate for M2's review; the format is stable to diff.
- Small fidelity gaps noted by the review, not yet closed: `Value.compare`
  orders `ExternV` by key-sorted compressed JSON where upstream compares
  Yojson structurally; `Lang/Xl/Num.lean` mirrors the types but not
  `compare`/`bin`/`cmp` (those live under Lean names in `Prelude/Num.lean`
  and `Runtime/Value/Value.lean`); text length and indexing count
  characters where upstream counts bytes; `Texts.text_to_int` accepts
  less than `Bigint.of_string`; `Names.ctorName` is invertible only up to
  the `_` join and the `_2` suffix.

## Blocked

Nothing.
