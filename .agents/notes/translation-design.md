# Translation choices and revisit points

Durable implementation rationale, consolidated from the decision register
on 2026-09-26. [Design](../../docs/design.md) owns the intended architecture;
this note retains reasons and unresolved engineering choices without
duplicating repository policy. Most choices originated 2026-09-25.

## Translation and generated interface

- Consume AL, not IL: upstream algorithmization already performs binding
  analysis, single-level pattern preparation, subtype tests and iteration
  length checks. Reimplementing that pass would enlarge the semantic boundary.
  Shared IL syntax is still necessary. An IL backend is not scheduled.
- The compiler is Lean so reference syntax, decoder and generator share
  representations. This aids checking but does not verify the generator.
  Upstream adoption of our generator language is not a criterion.
- Emit committed ordinary Lean text, one source-spec file per module, with
  recursive groups completed in their last owning source file. This supports
  review and incremental builds; the abandoned import-command approach added
  nothing to correspondence. Cross-file groups cannot be split arbitrarily.
- Use our `Std.Format` printer for deterministic width-constrained output;
  Lean's formatter needs elaboration context and has heuristic layout.
  Keyword escaping still uses Lean's actual token table.
- The naming scheme in `Codegen/Names.lean` preserves spec spelling,
  qualified references and source-file names. Type/function names must have
  separate maps: the quoted `id`/`$id` collision was caught by independent
  compiled-quotation comparison. Naming changes are compatibility changes;
  source variables must not shadow generated global references.
- Recursive generated groups use `partial_fixpoint` uniformly, never
  unchecked `partial`. A common partial-correctness principle simplifies
  generated soundness; structural recursion remains useful for encoders, not
  an alternate generated-function proof strategy. Reference recursion takes
  explicit fuel to match the port's large mutually recursive block.
- Logical premises mirror the executable statement sequence in A-normal form
  so generic symbolic execution can construct derivations. Run-soundness is
  not logical completeness: ordered alternatives and negative premises need
  separate contracts. The generic `run_sound_group` matches mutual proof
  components by function, not assumed conjunction order.
- Generated equality/order go through IL runtime values, not derived nested
  `BEq`, whose opaque implementation prevents ordinary proof reduction.
  Encoders recurse structurally through generated container helpers; decoders
  take fuel. Dummy generated notes are not arbitrary-observation equivalence.
- Extern syntax becomes `ExternValue`; extern calls are fields of a generated
  `Externs` class threaded through transitive callers. Having that interface
  does not establish a target implementation or its contract.
- Prefer per-construct encodings to a second IL-rewriting pipeline. Partial
  operations retain explicit effects/side conditions; never use defaults
  merely to produce total-looking prover definitions.

## Correspondence automation

The value bridge uses `Rel v x := canon v = canon (toValue x)`.
Canonical equality and inversion lemmas avoid maintaining another inductive
similarity definition. `canon` is not generally proved idempotent on
ExternV JSON, so use the actual congruence lemmas rather than assume a normal
form. Observation-specific adequacy remains separate.

One `HoldsSpec` table hypothesis, an empty local function environment and
guards disabled supply callee lookup contracts. Pure forward refinement
quantifies over every fuel and both terminating failure kinds; recursive
reference proofs use strong induction on fuel. Divergence/exhaustion at one
bound does not supply reverse realization. Initialization and representation
must be discharged before advertising a concrete consumer guarantee.

The `refine_al` driver unfolds reference equation lemmas and uses the small
`Refine/Calc.lean` effect calculus instead of a duplicated per-form
interpreter lemma library. Projection-based conditional equations may need
explicit unfolding. This keeps auditing direct but can make concrete proof
reduction expensive; revisit from measured full-scale bottlenecks.

Eligibility is syntactic and closed under callees, with unsupported reasons
reported, not `sorry`. Determinism is generated only when its tactic proves
the restricted single-path/noniterated/callee-deterministic case. General
rule disjointness and reverse automation remain open; generated logical
properties are not universal executable correspondence.

State, type-runtime, print and full-P4 constraints are maintained in their
topic notes. Stateful fixtures do not imply that production generation has
been enabled. The checked census probes emission capabilities, not successful
full-P4 compilation.

## Build and storage rationale

Nix replaces the former opam-repository pin. The locked default OCaml set
was selected for binary-cache availability; the older set incurred long
source builds. Upstream requires OCaml >= 5.1. Revisit this choice on an
actual upstream incompatibility, not merely because versions differ.
Lean and Batteries are pinned together; no Mathlib dependency was selected.

Lossless deterministic gzip snapshots plus raw SHA-256 retain all export
bytes without committing the 93.83 MiB full-P4 JSON. Deleting the old Nano
JSON from history would save only its compressed Git object; history rewriting
was not justified. Reassess Git history growth at pin bumps, not only checkout
size. No size exception or new external artifact service is assumed.

Per-module timing began early to expose scale risks while encodings were cheap
to change. The historical 48-module / 860.6-second total is neither wall-clock
build time nor isolated kernel time; provenance limitations are maintained in
[Performance](../../docs/performance.md), not silently repaired here.

Repository gate lessons already live in regressions: warning-as-error belongs
to `lake build --wfail`, not severity-rewriting Lake options; tracked-file
enumeration must handle NUL-separated names and missing/read-failed inputs;
a failed upstream Dune build must not pass because old binaries exist.
The 2026-09-26 independent `ci_timeout` review plus final root tests covered
the text checker (eleven tests) and upstream wrapper (five). Historical
review details and actual recorded exits are at `968ad65` in
`.agents/reviews/repository-checkpoint.md`; no new implementation audit is
claimed by this consolidation.
