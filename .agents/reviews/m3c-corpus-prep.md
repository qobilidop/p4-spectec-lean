# M3C corpus preparation review

Initial read-only source review, 2026-09-25, followed by a bounded restore
checkpoint. Scope: the corpus preparation note, the primary checkout of
P4-SpecTec at `8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`, this
worktree's submodule state and the restored pinned p4c sample/include slice.
This report is not an independent review of the newly authored fetch script;
root review is required before publication. No M3C completion claim follows.

## Findings and disposition

1. **High, corrected: the source checkout was misidentified.** Initially
   this worktree's `upstream/p4-spectec` was empty; top-level `git
   submodule status` prefixed its pin with `-`. `git -C` in that empty
   directory silently resolved the parent repo and reported its unrelated
   `59525a2` HEAD. The primary checkout was at the actual P4-SpecTec pin.
   The note now gives that provenance; this worktree's containing
   submodule has since been initialized at the same pin.
2. **Medium, corrected: p4c has a known exact pin.** The pinned
   P4-SpecTec tree has a `160000` gitlink for `p4c` at
   `6b7ec98e77dfc71c6e1309d9a76183cb31f35a8a`; its `.gitmodules`
   URL is `https://github.com/p4lang/p4c`. The nested checkout is
   uninitialized in the primary tree. The containing submodule was
   initialized non-recursively in this worktree. The nested pin was
   fetched directly, shallow and blob-filtered, into ignored `.artifacts/`.
   Sparse paths are `p4include/`, `testdata/p4_16_samples/` and the one
   uBPF symlink-target directory. No recursive submodule or p4c build was
   needed.
3. **Medium, corrected: relation sessions were conflated.** At the pin,
   `main.ml` selects `-al` and `-rel`, `interp-al/interp.ml` parses and
   evaluates one relation per `eval_program`, and
   `7.07-inst-declaration.watsup` calls `Program_ok` from within
   `Program_inst`. Two independent relation sessions match the CLI
   workflow; explicit chaining would change state and input shape. The
   note now requires separate sessions, records both output shapes, and
   distinguishes the parser's value-ID allocator from the builtin fresh
   type-ID counter. The adapter's exact reset behavior needs a smoke
   comparison against one CLI process per relation.
4. **Low, corrected: the smoke command used a shell glob.** Upstream's
   `Frontend.Parse.expand_path` accepts the spec directory recursively,
   so the note uses that path. `-i` is correctly retained: `main.ml`
   defines it as the repeatable P4 include-path option, not an
   interactive switch.

## Evidence checked

- Top-level gitlink and submodule status in the state-oracle worktree;
  actual primary upstream HEAD, nested p4c gitlink, `.gitmodules`, and
  uninitialized nested status. Expected four JSON-export patch files
  were the only primary upstream modifications.
- Primary pinned `excludes/static.py` and `excludes/dynamic.py` both
  exited 0 and reproduced the note's 120 static references, 56 dynamic
  references, and 60 exclusion files. Direct file counts reproduced 37
  regression P4 files (4 positive, 13 negative, 20 simulation) and
  2,126 p4testgen STF files with no P4 source in that tree.
- Pinned `p4spec/bin/main.ml`, `frontend/parse.ml`,
  `interp/interp-al/interp.ml`, `interface/interface.ml`,
  `interface/builtin/call.ml`, `interface/p4/parse.ml`,
  `runner/make.ml`, and the two `Program_ok`/`Program_inst` spec rules.

## Bounded restore evidence and limits

- `scripts/fetch-p4c.sh` first fetched exactly the gitlink commit with
  `--depth=1 --filter=blob:none`. Its final repeat run exited 0 without
  fetching; the checkout HEAD, origin, sparse paths and clean status were
  verified. The offline `scripts/test-fetch-p4c.py` suite exited 0 across
  ten miniature-repository cases; HTTPS transport was disabled, and each
  temporary fixture was removed. It covers idempotence, dirty/wrong-pin/
  wrong-origin/wrong-root/non-checkout refusal, both artifact symlink
  guards, dirty working `.gitmodules`, and a broken sample symlink.
  Manual non-checkout and dirty refusals also exited 1, then their
  temporary targets were removed and absence verified. Root's preliminary
  review caught a working-tree
  `.gitmodules` read and missing artifact-root symlink guard; the script
  now reads `HEAD:.gitmodules`, rejects a symlink root, and checks `find -L`
  status explicitly. `bash -n` and the repeat idempotence run exited 0
  after these changes; root's final independent review remains pending.
- 1,352 sample paths resolve: 1,347 regular `.p4` files and five uBPF
  symlinks. A static include scan found no missing literal includes.
  Sixty-seven of 68 positive static exclusion references match those
  paths; `issue3291-1.p4` is absent. The arithmetic remainder, 1,285,
  is not an oracle eligibility or success denominator. Negative
  `p4_16_errors` and dynamic STF inputs were not restored.
- One documented non-excluded p4c sample, `basic_routing-bmv2.p4`, passed
  upstream `Program_ok` and `Program_inst` in separate `main.exe` AL
  processes, each exit 0 (`passed`), at 0.61 s and 0.59 s wall. The CLI
  does not report boot/result values or fresh-ID counters; those remain
  unknown until an adapter records them. The full corpus was not run.

## Independent root script review

Root read the final script and all ten offline tests, independently checked
the restored p4c HEAD and clean status, reran the real idempotence path
(exit 0, 1,352 samples) and the offline suite (exit 0, ten tests). Earlier
root findings on pinned configuration, symlink roots and swallowed `find`
errors are fixed. Tests disable HTTPS transport and isolate fixture Git
configuration; they do not download source or change global user settings.
No outstanding findings in this input-restoration scope. The initial real
network fetch is author evidence, not independently repeated by the root.

Root integrated the script, tests and notes into the primary checkpoint;
the gate now invokes the offline suite and syntax check, never the fetch.
Integrated gate/CI remain separate checks. Next implement the boot/result
oracle adapter and measure actual eligible cases. This input checkpoint
does not establish M3C differential validation.
