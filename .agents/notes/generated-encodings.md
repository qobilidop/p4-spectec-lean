# Bounded subtype and update encodings

Compacted 2026-09-26 from decisions and 2026-09-25 independent reviews
`m3b-subtypes.md` and `m3b-indexed-updates.md`, recoverable at Git `968ad65`.
Durable encoding constraints for paused expansion, not a new review or full-P4
compilation claim.

Variant bridges specialize complete source/destination type applications.
Thirteen `continueResult` failures came from erased arguments, not different
payload semantics. Instantiate both variants and compare payloads after
alias normalization, matching upstream `runtime/type/sub.ml`. Structural
region-free keys delimit names/child lists and retain both argument lists;
child namespaces preserve monomorphic names without hashing or encounter-order
dependence. Placement follows both argument lists and nested expression
notes. Same-head/different-argument cases still require bridge validation.

Missing constructors, malformed argument counts, unknown/free arguments,
nonvariant heads and unequal payloads reject. Open polymorphic contexts,
explicit function-type arguments and general payload conversion remain
outside support; do not invent covariant casts. Confidence high at this pin;
revisit when an export needs polymorphic bridge declarations.

GPT-6 Astra independently reviewed Types/Exp/Emit/census/synthetic tests:
no high/medium findings. Nano `--check` kept 48 files unchanged; direct
Subtypes elaboration/execution and census check passed (567 bridges,
zero emission failures, all thirteen specializations). Parent separately
recorded full gate exit 0. Emission does not establish full-P4 elaboration
or refinement.

Root-index list updates preserve base/replacement/index order (upstream
`interp.ml:1009–1014,886–930`), reject bounds through `Iter.setIdx` and
retain hard errors via `Eval.err?`. GPT-6 Sol independently reviewed the
slice based on `7c1bfec`: no high/medium findings. Direct Updates elaboration
and diff checks exited 0; synthetic List Nat fixtures execute actual output
and inspect order/bounds. Parent separately recorded focused builds, lake
test and full gate exit 0/no skips. A stale milestone claim was corrected.

Those tests did not elaborate the four full-P4 list-update sites. Indexed
updates remain excluded from refinement independently of executable/Prop
support. Two later text updates use [byte text](byte-text.md), preserving
invalid UTF-8 and one-byte replacement. Nested index prefixes and sliced
updates remain explicit rejections in both families.
