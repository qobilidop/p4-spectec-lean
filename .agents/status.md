# Status

Where the work stands now. Updated at every checkpoint; holds current
state only.

Last updated: 2026-09-25. **Active: milestone M2 (Nano-P4, rung 3 and
the lemma library), on branch `m2-nano-p4`; phases A, B and C of the plan
in `.agents/notes/m2-plan.md` are done** (fuel-free executable encoding
in the `Eval` monad with `partial_fixpoint`; the `Prop` encoding of every
relation with a generated, tactic-proved run-soundness theorem and an
axiom audit; the AL interpreter ported to Lean and agreeing with upstream
on the corpus as the second leg of rung 2). Phase D (value relations and
the refinement theorems, rung 3) is next.

## Current state

| Scope | Result | Revision |
|---|---|---|
| Design | agreed; revised for M1's findings (AL not IL as the export, fuel, module grouping, naming rule) | `main` |
| Upstream build | P4-SpecTec at the `gsoc-nano-spec` pin builds in the `upstream` Nix shell on nixpkgs' OCaml 5.5 with `scripts/build-upstream.sh` | `main` |
| Export | `elab -json`, `algo -json` and `nano parse -json` from `upstream/patches/0001-json-export.patch`; `exports/nano-p4.al.json` (8.5 MB), 78 booted programs with upstream's verdicts under `exports/programs/nano-p4/` | `main` |
| Deep embedding | `P4SpecTec/Lang/Il/Ast.lean`, `Lang/Al/Ast.lean` and their JSON decoders mirror `lang/il/ast.ml`, `lang/al/ast.ml` at the same paths; `scripts/check-mirror.py` derives every mirrored pair from the paths and checks constructor lists and order | `main` |
| Prelude | `Runtime/Value/Value.lean` and `Interface/P4/Unparse.lean` mirror value construction, accessors, comparison and the printer; `Interface/Builtin/` ports every builtin file, with unit tests in `P4SpecTecTest/Builtins.lean` and the dispatcher on values `Call.lean`; `Prelude/` holds `ToValue`/`OfValue`, the `Eval` monad, numerics and iteration helpers | `m2-nano-p4` |
| Interpreter | `Interp/InterpAl/{Backtrack,Ctx,Interp}.lean` mirror `interp/interp-al/` function by function, with fuel, over `Runtime/Value/Match.lean`, `Runtime/Type/{Typdef,Typ,Subst}.lean`, `Runtime/Dynamic/Var.lean`, `Runtime/DynamicAl/{Rel,Func}.lean`, `Lang/Hints/Input.lean`; `lake exe nano-p4-interp` (`P4SpecTecTest/Diff/NanoP4Interp/Main.lean`) runs `Program_ok` on the deep terms against the AL export | `m2-nano-p4` |
| Codegen | `lake exe p4spectec-gen`: types, subtype bridges, functions, builtins, relations in both encodings, run-soundness theorems with audits, `Externs` class, per-file modules, `--check`/`--update`; every definition in `Eval := ExceptT Fail Option`, recursive groups by `partial_fixpoint`, no fuel | `m2-nano-p4` |
| Tactics | `P4SpecTec/Tactic/RunSound.lean`: `run_sound` (symbolic execution of a run function against its `Prop` constructor) and `run_sound_group` (over `mutual_partial_correctness`, matching conjuncts by function); `Tactic/Audit.lean`: `#audit_axioms` | `m2-nano-p4` |
| Generated | `NanoP4Spec/`, 28 modules named after the spec files, 21k lines, builds with `--wfail`; 161 types, 76 functions, 77 relations in both encodings (77 `Prop` inductives, 98 theorems: 77 `R.run_sound` and 21 group theorems, each audited); 65 `partial_fixpoint` definitions in 20 recursive groups | `m2-nano-p4` |
| Rung 2 | `test/diff/run.py`, two legs: the generated `Program_ok.run` and the interpreter port each agree with the AL interpreter's verdict on 78 of 78 programs (48 pass, 30 fail: 32 positive, 21 negative, 25 exercises); for the 48 that pass, the output typing context equals upstream's value on both legs | `m2-nano-p4` |
| Timing | `docs/timing-nano-p4.md`: 25.9 s over 28 modules including the monotonicity and soundness proofs (13.5 s before the theorems); `1-syntax` and `5.13-typing-call-convention` at about 3.3 s each are the largest | `m2-nano-p4` |

## Last checked evidence

2026-09-25, on `m2-nano-p4` after phase B, `scripts/check.sh` in the
Nix shell: exit 0 (layout, text, imports, mirror, `lake build --wfail`
with the 28 generated modules, their `partial_fixpoint` monotonicity
proofs and the 98 run-soundness theorems with `#audit_axioms`,
`lake test`, keyword table, `p4spectec-gen --check`, and the harness: 78
of 78 verdicts agree, 48 output typing contexts equal). On `main` at
`d8003ec`, CI run 36116792883: exit 0.

## Open threads

- **Rung 3 (value relations, refinement theorems) is not started**:
  phase D of the M2 plan. The interpreter port, the `Prop` encoding and
  run-soundness are done; the completeness direction
  (`R i o → R.run i = some (.ok o)`) is not stated (design section 12).
- The interpreter's `Value.Match.sub_` yields `false` for function values
  (`FuncT`), since `Type.Equiv` is not ported; Nano-P4 has none, the full
  spec has (M3).
- **Determinism theorems** (phase E) are not attempted yet.
- **Readability of the `Prop` encoding**: a `matches` check on a value
  that a pattern later substitutes appears as `match C x with | C _ =>
  true | _ => false = true`, and an unzipped iteration variable appears
  as `List.map (·.1) tmp_n`; both are faithful and provable, both could
  be simplified by the generator later (roadmap, readability).
- **Packet leg of rung 2** (nano-switch simulation) is M3 by the design
  ("target instances arrive with the packet leg"); the `Externs` class is
  generated, no instance exists yet.
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
