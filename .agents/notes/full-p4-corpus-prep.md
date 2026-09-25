# Full-P4 corpus preparation for M3C

Preparation checkpoint at P4-SpecTec `8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`,
the gitlink in this worktree and the checked-out commit in both it and the
primary repository. Before restoration, this worktree's `upstream/p4-spectec`
was empty; `git -C` inside that directory silently resolved to the parent
repository's unrelated `59525a2` HEAD. It was initialized non-recursively
with a reference to the primary checkout. Counts initially came from the
primary pinned source; the corpus counts and smoke results below are from
the worktree's now-restored pinned inputs on 2026-09-25. This is bounded
M3C preparation, not full differential validation. Reproduce commands from
any directory with absolute paths and the named Nix shell.

## Corpus actually present

The documented M3C primary source is upstream's p4c sample set
(`p4c/testdata/p4_16_samples`, mostly well-typed). At the pinned P4-SpecTec
commit, `p4c` is a nested submodule gitlink at
`6b7ec98e77dfc71c6e1309d9a76183cb31f35a8a`; its `.gitmodules` URL is
`https://github.com/p4lang/p4c`. The nested submodule remains uninitialized
in both upstream checkouts; the state-oracle worktree now has a shallow,
blob-filtered sparse checkout at that exact pin in ignored `.artifacts/p4c`.
The pinned upstream `excludes/` records references to this corpus but cannot
supply source files. Count only actual restored files when choosing a test
denominator.

Other full-P4 material in the pinned upstream checkout is much smaller and
differently purposed:

| Source | P4 | STF | Use / limitation |
|---|---:|---:|---|
| `testdata/regression/pos/` | 4 | 0 | Focused positive regressions; restored p4c includes now permit boot probes |
| `testdata/regression/neg/` | 13 | 0 | Focused negative regressions; restored p4c includes now permit boot probes |
| `testdata/p4testgen/` | 0 | 2,126 | Packet fixtures; program `.p4` source is absent, so not runnable alone |
| `nano-p4/testdata/{positive,negative,exercise}/` | 78 | 39 | Separate Nano-P4 dialect, not a full-P4 M3C sample |

The 37 regression `.p4` files count 4 positive, 13 negative and 20
under `sim/`. The p4testgen fixture tree has 2,126 STF files and no P4 files.
The Nano-P4 exported oracle is already booted, but its 78 programs (32
positive, 21 negative, 25 exercise) are not evidence about full P4.

The sparse p4c tree contains 1,352 `.p4` sample paths: 1,347 regular files
and five symlinks into `backends/ubpf/tests/testdata`, whose targets are now
included. All paths resolve. The restored `p4include/` contains `core.p4`,
`v1model.p4`, `pna.p4`, `ebpf_model.p4`, `ubpf_model.p4` and `xdp_model.p4`.
Every literal `#include` in the 1,352 sample paths resolves from the
sample's directory, the sample tree or this include tree. This static
scan does not prove every program parses or that preprocessor macros reach
no other include.

## Exclusions

There are 60 `*.exclude` files at the pin. The upstream summary scripts give
120 static `.p4` references (68 positive, 52 negative) and 56 dynamic `.stf`
references (10 under `dynamic/p4c`, 46 under `dynamic/p4c-specific`). These
are references in exclusion manifests, not additive corpus counts, and should
be intersected with the restored corpus before deciding which cases to skip.
Of 68 positive static references, 67 match restored sample paths; the one
stale path is `p4c/testdata/p4_16_samples/issue3291-1.p4`. Thus 1,285
restored sample paths remain after the matching static references alone.
That arithmetic is not a successful/eligible oracle denominator: parsing,
other exclusion policy and relation outcomes have not been measured.
The 52 negative static references target `p4_16_errors`, which was not
restored in this bounded step; dynamic STF references are also outside it.

Static manifest categories and references:

| Category | Positive | Negative | Meaning |
|---|---:|---:|---|
| `static/p4-spec` | 10 | 0 | Pending interpretation/coverage questions in the P4 spec |
| `static/p4c` | 33 | 4 | Confirmed upstream/p4c disagreement plus pending cases |
| `static/p4c-specific` | 25 | 26 | Behavior specific to p4c, including implicit typing choices |
| `static/target-specific` | 0 | 22 | Known target-specific cases |

The dynamic manifests mark runtime exclusions: known p4c cases, patched
upstream cases, and p4c/target-specific gaps such as unimplemented externs,
expected infinite loops, undefined values, and known output mismatches.
Keep their individual file and reason attached to every skipped test;
do not convert a missing file or any unexplained failure into an exclusion.
The manifests under `excludes/static/` and `excludes/dynamic/` are the source
of truth; `excludes/static.py` and `excludes/dynamic.py` only summarize counts.

Exact count commands against the primary checkout (exit 0):

```sh
nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean#upstream --command python3 /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec/excludes/static.py
nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean#upstream --command python3 /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec/excludes/dynamic.py
nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean --command python3 -c 'from pathlib import Path; u=Path("/Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec"); r=u/"testdata/regression"; d=u/"testdata/p4testgen"; n=u/"nano-p4/testdata"; print("regression p4",sum(1 for p in r.rglob("*.p4")),"pos",sum(1 for p in (r/"pos").glob("*.p4")),"neg",sum(1 for p in (r/"neg").glob("*.p4"))); print("p4testgen p4",sum(1 for p in d.rglob("*.p4")),"stf",sum(1 for p in d.rglob("*.stf"))); print("nano p4",*[sum(1 for p in (n/x).glob("*.p4")) for x in ("positive","negative","exercise")],"stf",sum(1 for p in n.rglob("*.stf")))'
```

## Pinned restore and refusal checks

`scripts/fetch-p4c.sh` derives the nested p4c commit from this worktree's
verified P4-SpecTec gitlink and the URL from its pinned `HEAD:.gitmodules`
blob, independent of working-tree edits. It fetches
that commit directly with `--depth=1 --filter=blob:none`, sets sparse paths
*before* checkout, and materializes only `p4include/`,
`testdata/p4_16_samples/` and the five samples' symlink targets under
`backends/ubpf/tests/testdata/`. The exact pin was available via shallow
fetch; no branch tip was substituted, no broad history was fetched, no
recursive submodule was initialized and p4c was not built. The source is
ignored under `.artifacts/p4c`; the nested `upstream/p4-spectec/p4c`
directory remains uninitialized. The primary checkout was not changed.

To reproduce after non-recursively initializing this worktree's
`upstream/p4-spectec`, run from any directory:

```sh
nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean --command /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/scripts/fetch-p4c.sh
```

The initial two-path checkout had 1,347 regular files and five unresolved
symlinks. After adding their one target directory, the script exited 0
with 1,352 resolved sample paths at
`6b7ec98e77dfc71c6e1309d9a76183cb31f35a8a`. A repeat run exited 0
with the same pin/count and no fetch. Git reports it as shallow, with
exactly the three sparse paths above and a clean status.
The offline `scripts/test-fetch-p4c.py` suite exited 0 (10 cases, temporary
miniature Git repositories, HTTPS transport disabled). It checks clean
exact-pin idempotence; refusal of dirty, wrong-pin, wrong-origin,
non-checkout and wrong-root destinations; artifact-root and destination
symlinks; a broken sample symlink; and use of the pinned `.gitmodules` blob
despite a dirty working copy. It mutates no global Git configuration and
removes its own temporary fixtures. Before the durable suite, manual
non-checkout and dirty-checkout refusal probes each exited 1; their
temporary targets were removed and absence verified. The exact source is
sufficient for the sample/include stage; `p4_16_errors` and packet fixture
source remain future scope. Do not commit duplicate p4c source.

## Upstream boot and AL oracle boundary

`scripts/export-program.sh` is Nano-specific: it calls `nano.exe parse -json`
then `nano.exe check -il -json`, and records the verdict and returned output
values. Do not point it at full-P4 sources; it uses Nano includes/spec and
stores files under `exports/programs/nano-p4/`.

For full P4, `p4spec/bin/main.ml` exposes `parse` and `run`. `parse` invokes
`Simulator.Interface.parse_program includes [path]` and then un-parses the
booted value as P4 text; it does not emit typed-value JSON. `run` builds the
AL simulator and invokes `Simulator.Interp.eval_program rel includes path`;
`Program_ok` or `Program_inst` can be selected with `-rel`, and `-al` selects
the sequential AL interpreter (SL is the default). The CLI prints only
`passed` on success and does not serialize returned values. The library call
returns `Pass values` or syntax/runtime failure; `eval_program` clears call
caches, boots via `Interface.parse_program`, then calls `do_eval_rel`.
`Program_ok` returns one `p4programIR`; `Program_inst` returns a global
instantiation layer and store and invokes `Program_ok` internally. Thus
independent runs of both relations cover typing and instantiation; chaining
one relation's output into the other would change the upstream workflow.

Therefore full-P4 oracle exports need a small upstream-side probe/adapter
(analogous in purpose to `scripts/export-program.sh`) that captures the
booted `Value.t`, runs each relation on that value under an independently
initialized AL simulator/session, and serializes the result values plus
syntax/runtime failure class and diagnostic. Reuse the same boot JSON input
for both relation comparisons, but match the CLI's per-run state boundary;
do not execute `Program_ok` and then `Program_inst` in one mutable session.
`main.exe parse` and `main.exe run` are smoke probes, not a complete
booted-value/output exporter. Keep sequential mode: omit `-det`
(deterministic checking explores alternatives). The parser's value-ID
allocator and the builtin `fresh_typeId` counter are distinct; the latter
is initialized at zero when the builtin module is made and can advance
during a relation. Preserve literal fresh-ID outputs and establish the
adapter's reset behavior against one process per relation before bulk use.

The first verdict smoke used p4c's documented
`testdata/p4_16_samples/basic_routing-bmv2.p4`, a sample absent from the
static exclusion manifests. Upstream's `Frontend.Parse.expand_path`
recursively accepts the spec directory, avoiding a shell glob. `-i` is
the CLI's include-path option, not an interactive flag. For each relation,
the primary checkout's existing pinned `main.exe` was a *separate process*
under the upstream Nix shell with `-al`, no `-det`, and the restored include
directory. The `Program_ok` command was:

```sh
nix --no-warn-dirty develop /Users/qobilidop/my/work/p4-spectec-lean#upstream --command /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec/_build/default/p4spec/bin/main.exe run /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec/spec -rel Program_ok -i /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c/p4include -p /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c/testdata/p4_16_samples/basic_routing-bmv2.p4 -al
```

Changing only `-rel Program_ok` to `-rel Program_inst` gave the second
command. Both recorded exit 0 and stdout `passed`; wall time was 0.61 s
and 0.59 s, respectively. Both emitted the pinned `$sink` missing-clauses
warning. CLI output has no boot value, relation output value or fresh-ID
counter, so these remain unknown from this smoke. Raw stdout/stderr and
timing are in ignored `.artifacts/m3c-program-{ok,inst}.*`; those logs are
not fixtures. A prior syntax probe with positional `al` rather than
`-al` exited 1 (`I/O error: al: No such file or directory`).

## Lean consumers and state/mode cautions

Current Nano pattern: `scripts/export-program.sh` emits one JSON value and
verdict sidecars per program; `test/diff/run.py` feeds those paths to both
`lake exe nano-p4-run` (generated relation) and `lake exe nano-p4-interp`
(ported AL interpreter), then compares verdicts and outputs. For full P4,
reuse the validated JSON boundary and differential harness shape, but use
distinct full-P4 binaries/library roots and do not conflate it with the
Nano artifact paths. The eventual full-P4 tests must cover both
`Program_ok` and `Program_inst`, including negative programs and exact
outputs on success.

The primary M3B status records a stateful interpreter integration on a
later branch; this preparation worktree at `59525a2` contains only the
explicit-state foundation/tests and does not itself expose that integrated
entry point. In the stateful API, state sits below failure, choice retries
after mismatch with the consumed post-state, and negation retains the
called relation's post-state. Only a caller-selected session boundary
starts at zero. Fresh IDs are literal observable text; never alpha-normalize
them. Run oracle comparisons without `-det`. Stateful generated code and
stateful refinement are not established by the presence of `StateEval`.

## Suggested slice and repository size

Start with a small, dependency-focused subset of the restored canonical
`p4_16_samples`: a simple well-typed program, one using structs/headers,
and one control/parser path. Pair these with known-negative regressions;
the canonical `p4_16_errors` tree is a later, separately bounded restore.
For each, record boot, `Program_ok` and (where meaningful) `Program_inst`,
exact outputs and exclusion status. Then expand by feature strata (type
parameters/functions, externs, tables, fresh IDs/printing) before the
full eligible corpus. The 17 regression pos/neg tests remain an adapter
smoke slice, not M3C completion.

Current local Nano boot artifacts occupy about 20 MiB for 78 programs
(312 files, including sidecars); full P4 will be materially larger if it
includes typed values and outputs. Keep runtime probe logs and scratch
exports in ignored `.artifacts/`. Before committing any corpus, measure
individual and aggregate sizes: tracked files above 5 MiB are rejected, and
the full spec snapshot already uses 2.61 MiB compressed. Prefer small
per-case fixtures or deterministic compression plus checksum for snapshots;
do not commit a monolithic generated JSON file over the cap. Avoid checking
in complete duplicate source corpora already pinned in upstream.
