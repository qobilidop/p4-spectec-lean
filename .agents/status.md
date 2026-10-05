# Status

Active: full-P4 M3, resumed by the user on 2026-10-04 with autonomous authorization
(decisions, "Scope and product"). The Nano-P4 completion milestone stays closed at
`42ffad6` (2026-09-30); [`notes/nano-release.json`](notes/nano-release.json) records its
review and exact-revision CI for that tree digest.

## Where M3 stands

- M3B: the whole full-P4 export generates as the library `P4Spec` (ignored sources,
  pinned by `P4Spec.manifest.json`): executable definitions, quotations matching the
  export, and since 2026-10-05 a state-indexed logical relation for each of the 256
  relations. Everything builds with `--wfail`. No certificate of any kind exists: M3B's
  exit needs audited run-soundness, which no full-P4 relation has in committed code.
  [Full-P4 overview](notes/full-p4/overview.md) has the measurements and what is missing.
- M3C, sweep (`f329af0`): the generated library and the reference interpreter both agree
  with upstream on 1,266 of the 1,267 corpus candidates, for typing and instantiation.
  [Corpus note](notes/full-p4/corpus.md) has the evidence and its limits.
- M3C's durable campaign, M3D, M3E and M3F are open.

## Verified state

Evidence for the working tree of the commit that adds the logical relations:

- Full gate, after the review resolutions: `nix develop -c /usr/bin/time -p
  scripts/check.sh` returned actual exit 0 in 502.41 s, all 55 stages, 207 s of it
  rebuilding the relation modules (`.artifacts/m3b/props/gate-2.log`); Nano completion 888
  obligations, 0 unresolved, review and release pending under the allowance as on every
  tree after `42ffad6`. Generated Nano output is byte-identical; `P4Spec` (204 files)
  matches its manifest and its 132 relation modules build.
- Not rerun for this commit: the corpus sweep and the four-case replay. Their evidence is
  for `f329af0` (sweep exit 0 in 1,228.0 s; replay exit 0). This commit changes the
  relation emitters, not the executable definitions: per the manifest diff the only
  changed files are the root `P4Spec.lean` and `Refinement.lean` (new imports and
  header) beside the 132 new relation modules. The generated legs' externs now import
  the quoted-spec module instead of the library root, so the workers were rebuilt and
  not re-swept.
- Independent review: [full-P4 review](notes/full-p4/review.md), "Logical relations
  stage"; no blockers, should-fix items resolved before the commit, not re-reviewed.
- Remote CI: `c7ed36f` passed (run 37288431358, 19 min); `f329af0` passed in 12 min with
  a restored build cache; `6e57dcb` took 33 min cold.
- Golden samples (the commit after `c7ed36f`): `P4Spec.samples/` holds copies of ten
  generated modules, checked by a new gate stage. Full gate on that commit's working
  tree, after the review resolutions: actual exit 0 in 243.69 s, all 57 stages
  (`.artifacts/m3b/samples-gate-2.log`). Independent review:
  [full-P4 review](notes/full-p4/review.md), "Golden samples". The user confirmed keeping
  `P4Spec` out of the repository (decisions, "Staged explicit-state generation").

## Open threads and next step

1. Next: run-soundness (M3B's exit). First the tactic gaps that stop two of the fourteen
   relations needing no recursive support (`ConstructorType_ok`, `Constructor_inst`: a
   single-constructor `let` pattern left as projections, a guard `none == some _` left
   undecided), then emit those theorems in modules beside the relations, then the
   recursive motives (`RecursivePrefix`, `StateRules`) for the 31 recursive groups,
   measuring `Cast_impl` and `Expr_eval` early.
2. M3C: extend the shard campaign to the generated worker and a larger bound for a
   durable, CLI-checked record; add rejected programs (negative regressions,
   `p4_16_errors`); commit a generated-code mutation suite for the sweep.
3. Generated `==` converts both operands to IL values (`valueEq`); on the largest programs
   the generated leg is about five times slower than the interpreter. Fix before any
   generated-leg target work (M3D); untried options are in the corpus note.
4. `Expr_eval`'s relation module takes 195 s of the 203 s the relation modules add to a
   cold build. Acceptable now; revisit if proofs over it are slow for the same reason.
5. A warm `lake build` log shows `PANIC at Lean.Meta.whnfEasyCases ... loose bvar` replayed
   as an info message from `NanoP4Spec.Refinement.Reverse.TableEntry_ok` (line 36). The
   module builds and its audits pass; the message predates this work and is unexplained.

## Repository state

M3 work is committed directly on `main`. Preserve local `n3-decl-load`
(`82fbe2e`, non-ancestor WIP), unrelated `docs/repository-review`, and the dirty old
`../p4-spectec-lean-replay` worktree. The expected four-file upstream exporter patch
remains applied; no source pins changed. `.artifacts/p4c` holds the pinned p4c samples.
