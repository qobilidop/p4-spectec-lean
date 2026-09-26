# NanoSwitch target boundary: independent review

2026-09-25. Independent AI-agent source review of
`.agents/notes/nano-target-boundary.md`. No target, interpreter, generated
source, upstream checkout or pin was changed. The only write is this report.

## Verdict

The reported mismatch is real at the pinned source boundary. Returning
`PACKET typeId objectState` instead of the target's raw `ExternV objectState`
would be a semantic repair, not a faithful port or note normalization.
Keep the dynamic target faithful and report the typed boundary explicitly.
Do not count unguarded upstream packet success as typed extern agreement.

Known, reproducible affected-case exclusions are compatible with M3D's
written scoped exit criterion, which expressly accounts for exclusions and
failure cases. They do not establish a fully faithful generated typed
NanoSwitch instance on extract calls. A closure claim must distinguish those
two facts, and cannot be based on the present upstream-only probes.

## Independently checked source evidence

The primary upstream checkouts have the recorded HEADs:

- P4-SpecTec `8c8e0c6ffa604c533f5ad2f1db0503c0c601e6f3`.
- Nano spec `60dfd9912011bd5b1746ac88b26b58f7b3981991`.

`git diff --exit-code HEAD -- <reviewed paths>` exited 0 in each checkout.
The reviewed target/spec files are therefore unchanged from these pins;
this check does not revalidate the unrelated four-file exporter patch.

1. `p4spec/lib/backend-sim/nano_switch/pipe.ml` first destructs the receiver
   as `PACKET typeId objectState`. Its sole supported method branch is
   `PacketIn` / `extract` / `["hdr"]`. Both the short-packet branch and the
   successful 24-bit parse branch ultimately return
   `[Value.Make.extern objectState ...; value_ctx]`, without a PACKET wrapper.
   `backend-sim/extern.ml` forwards that list as `Run.Pass`; it does not
   rewrap or convert the value.
2. Nano `3.0-value.watsup:39–41` declares objectState as an extern syntax
   and packetValue as a PACKET constructor containing it. The `value`
   union contains packetValue, not bare objectState. Nano
   `8.01-eval-relation.watsup` declares ExternMethodCall_eval's outputs as
   `value` and `evalContext`.
3. Nano `8.13-eval-call.watsup` writes the returned value into the receiver
   with `Lvalue_write`. Its callee-selection rule subsequently requires a
   PACKET-shaped receiver. Thus the difference is stored in semantic context
   and can affect later dispatch; packet-only agreement is insufficient.
4. Generated `NanoP4Spec/3.0-value.lean:233` has the expected closed value
   constructors, including PACKET but no raw ExternV alternative.
   `NanoP4Spec/8.01-eval-relation.lean:462` gives the extern field result
   `Option (Except Fail (value × evalContext))`.
5. `Refine/Value.lean` preserves the distinction between CaseV and ExternV
   in `canon`. The generated PACKET encoder produces CaseV. Consequently
   the proposed rewrapping cannot meet the existing equality-based `Rel`
   for this raw output. This is a source-level obstruction, not a new
   kernel-checked impossibility theorem in this review.

The reported direct and three real STF runs, and the guarded field-access
failure, are author-provided runtime evidence. I inspected the probe source
and boundary note, but did not independently rerun the OCaml probes. The
current scratch packet probe selects `guard=true` and prints `RESULT runtime`
on a recorded runtime failure without setting a failing process exit status.
Its process exit 0 must therefore never be used alone as a packet-pass verdict.
Earlier unguarded runs need durable configuration-tagged fixtures; the
mutable scratch source does not preserve both configurations by itself.

## Principled implementation options

### 1. Faithful dynamic target plus explicit typed exclusions

This is the smallest compatible next step. Port the pinned target over IL
runtime values, including its raw return shape, packet state and failure
behavior. Use that target in the Lean AL interpreter and compare complete
observations against pinned upstream. Keep any generated typed adapter a
separate boundary, with an explicit representability condition or checked
conversion failure. A conversion failure is `unsupported typed boundary`,
not an upstream runtime error, matching verdict, successful typed execution,
or permission to insert a default value.

Affected-case accounting must be explicit: enumerate the pinned corpus,
identify extract reachability/observations, keep excluded cases in the
denominator, record reason and configuration, and retain distinguishing
regressions. Reaching any unsupported result ends the typed comparison as
excluded; it must not quietly resume with a repaired context. Propagate the
restriction through callers. The dynamic comparison can still cover these
same cases faithfully. A free-pass case with no extern call is useful but
does not by itself exercise Nano's typed extern interface.

### 2. Upstream correction followed by a reviewed pin update

An upstream-supported alignment of target and spec can remove the boundary.
The reviewer does not assume which side upstream intends to change, or that
rewrapping is its complete fix. Do not patch the pinned simulator locally
and label it the oracle. After an actual upstream revision is selected,
follow the documented pin procedure: rebuild, regenerate exports and
observations, regenerate Lean, re-audit mirrors and affected semantics,
and run complete gates. An upstream issue or fix proposal is separate
external coordination, not performed by this review.

### 3. A separately proved representation boundary

This is possible only with a new explicit contract, not by reusing the
current `Rel` unchanged. A candidate relation would have to account for
receiver identity/type tags, stored contexts, target object state and all
subsequent operations, including repeated method calls, guarded failures,
packet outputs, failure tags and final state. It must prove preservation
of that relation by callers, not merely equality of emitted packets in
the current fixtures. Guarded and unguarded modes need separate scopes.

The pinned raw result does not retain the PACKET type tag; an adapter that
recovers it from the input uses additional contextual information. A later
PACKET pattern can distinguish the repaired representation from the raw
one. Hence a blanket observational-equivalence claim is unsupported and
unlikely without restrictions on future receiver uses. Changing all
generated value types, weakening full-context comparison, or quotienting
away this distinction is not a bounded representation proof and would
require explicit design review. Do not pursue that expansion implicitly.

## v1model/eBPF are separate boundaries

The same raw objectState construction does not demonstrate this Nano bug
in v1model or eBPF. Their reviewed `pipe.ml` implementations take context,
architecture and object ID, update objectState inside the architecture,
then return `[context; architecture; callResult]`. This matches the shape
of full-P4 `8-dynamic/8.02-evaluation-relation.watsup:432`, whose declared
outputs are `evalContext arch callResult`, not Nano's updated receiver value.

Therefore do not apply the Nano wrapper repair or Nano typed exclusion to
those targets by analogy. Port and validate their own pinned behavior,
including packet state, callbacks and unsupported operations. This source
check supports proceeding independently; it does not establish complete
v1model/eBPF fidelity or packet coverage.

## Conditions for an honest M3D checkpoint

The written M3D exit criterion is target instances plus reproducible
upstream-versus-Lean packet results, with exclusions and failures accounted
for. It can accommodate this known Nano limitation if the final coverage
record explicitly separates:

- faithful dynamic Nano target execution and its real extract observations;
- generated typed Nano coverage, with affected extract cases excluded;
- actual independently checked v1model/eBPF instances and their supported
  STF cases, failures and exclusions.

Such a scoped milestone is not completion of the all-definition thesis or
of a fully supported typed Nano target. If the intended milestone instead
requires faithful generated typed Nano extraction itself, exclusions do not
meet that requirement: an upstream correction or proved representation
boundary remains necessary. Record the chosen scope explicitly before
declaring the milestone closed; do not quietly reinterpret the target claim.

At present none of the options closes M3D: the note contains upstream-side
reconnaissance, no implemented Lean target, no durable target oracle, no
upstream-versus-Lean packet replay, and no complete target coverage counts.
Recommended next increment is option 1 with durable boundary observations
and shared packet primitives, while v1model/eBPF proceed faithfully on
their own contracts. Full gates and independent implementation review are
still owed. No code changes, runtime reruns or milestone closure are claimed
by this source review.
