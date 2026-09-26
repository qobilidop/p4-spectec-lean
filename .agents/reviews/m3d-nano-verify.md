# Shared verify and Nano dispatch review

Root independent review, 2026-09-25. Read the complete new Lean ports,
original OCaml functions, probe, replay, fixture contract, capture script,
request set and offline tests. No semantic findings in the bounded port.
The source-identity finding below is fixed and independently reviewed.
Gate wiring and combined publication validation are separate obligations.

The shared getter keeps upstream's full-P4 prefixed-name/cursor ABI, not
Nano's different argument order. Both ordered lookups precede Boolean
unpacking, even for true or malformed checks. RETURN's optional-value note,
REJECT's result note, unchanged context/architecture and callback failure
post-state match the original source. The exact `_B bool` shape check agrees
with upstream's structural mixop comparison; it does not flatten sequences.
Function dispatch retains getter order and exact parameter names. Other
functions remain unsupported, rather than receiving invented semantics.

The original probe records callback arguments and final counters separately
from output values. Lean compares semantic payloads and nested type notes.
Nineteen direct cases, all five actual replay mutations and seven offline
contracts independently reran with exit 0. The real Nano AL boundary also
matches: no ExternFunctionCall_eval declaration, and the full-P4 getter
against Nano produces mismatch without consuming fresh state. The dummy
context is explicitly not booted program evidence. No successful Nano
source-level verify execution is claimed.

## Resolved finding: exact spec source identity

The new capture runner checks Nano HEAD and tracked diff but not repository
root identity or untracked consumed input. A subdirectory of the pinned
repository or an added `.watsup` can therefore pass those guards without
being the complete pinned specification. The existing packet capture runner
has the same inherited gap. Add a shared exact-root/input guard and focused
negative tests, including ignored untracked specification inputs, before
closing this review. Do not alter semantic fixtures to hide the boundary.

The separately authored shared `scripts/check-spec-pin.py` now requires an
absolute canonical repository root, exact pin, clean tracked tree/index and
no untracked entries, including ignored files. Both capture runners call it.
Rejecting all extra inputs is deliberately conservative and does not guess
the collector's suffix or symlink traversal. This is a cooperative local
source-identity check, not protection against concurrent hostile edits.
Root read all four changed files and independently reran six guard tests
(exit 0), including the old false acceptance, ignored nested inputs, wrong
pin, indexed/worktree edits and untracked directory symlinks. No semantic
source or fixture changed. The checked real spec root passes the new guard.

For root's independent real re-observation, the actual supplied path was
separately verified to be the exact repository root at `60dfd991`, with no
tracked changes and no untracked files (including ignored files). The
capture independently exited 0: all nineteen direct observations and the
real AL boundary match (`.artifacts/root-verify-oracle.exit`). After the shared
guard fix, root reran both capture runners: all nineteen verify observations,
the real AL boundary and all four original-driver packet sessions again
match (actual combined exit 0). Semantic fixture bytes are unchanged.

No gate wiring, full local gate or remote CI is claimed by this review.
