# M3B subtype specialization review

2026-09-25, independent read-only AI review by OpenAI Codex (GPT-6
Astra). Scope: `Types.lean`, `Exp.lean`, `Emit.lean`, the census and
compiled synthetic bridge tests. No high- or medium-priority findings.

The implementation retains complete type applications during collection
and generation. Specialization keys delimit names and child lists,
include both argument lists, and ignore source regions. Their child
namespace preserves existing monomorphic names. Region-independent
deduplication distinguishes different specializations.

Variant cases are instantiated before comparing shared payloads. Alias
normalization permits definitionally equivalent payloads while retaining
rejection of actual differences. Missing constructors, malformed argument
counts, unknown/free arguments and nonvariant heads reject explicitly.
Same-head applications with different arguments reach bridge validation.

Placement includes types inside both argument lists. Consumer placement
includes nested expression notes, accounting for specializations absent
from a callable's outer signature.

Independent checks, all in Nix, each exit 0:

- Nano-P4 generator `--check`: all 48 files unchanged.
- `lake env lean P4SpecTecTest/Subtypes.lean`: real emitted declarations
  elaborate and their executable checks pass.
- Full-P4 census `--check`: 567 bridges, zero emission failures. All
  thirteen `continueResult` specializations match the independent AL audit.

Successful emission is not a full-P4 build or refinement proof. General
payload conversion and open polymorphic bridge contexts remain outside
this change. The parent agent separately ran `scripts/check.sh`: exit 0.
