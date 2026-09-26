# Independent canonical corpus inventory review

2026-09-25. Root reviewed `test/p4-corpus/inventory.py`, its offline tests,
README and the generated manifest against the pinned upstream collector and
exclusion parser. No findings remain for this inventory-only tranche.

Directory traversal preserves upstream's literal `include` skip and symlink
path identity; exclusions preserve exact line spelling, leading-comment
semantics and a final line without a newline. The manifest deliberately sorts
complete canonical paths for deterministic sharding rather than claiming the
same execution order as upstream's recursive traversal. Source and exclusion
byte hashes, symlink spelling and exclusion line provenance are retained.

The corrected accounting is 1,352 raw paths: 18 include-directory helpers,
67 statically excluded collected programs, and 1,267 canonical candidates.
Five paths are symlinks. There are 68 positive exclusion references, one of
which is stale. Root independently inspected the upstream collector and
listed the eighteen helpers before approving this correction; helpers are
not silently counted as standalone program executions.

Independent commands in the byte-identical pinned default shell exited 0:

- `python3 test/p4-corpus/test_inventory.py`: five tests, including thirteen
  corruption cases, literal exclusion-line/EOF handling, symlink collection
  and disjoint deterministic shards.
- `python3 test/p4-corpus/inventory.py --p4c
  /Users/qobilidop/my/work/p4-spectec-lean-state-oracle/.artifacts/p4c
  --upstream /Users/qobilidop/my/work/p4-spectec-lean/upstream/p4-spectec --check`:
  exact equality with a fresh inventory under the reused strict pin/source
  guards; the counts above were reproduced.

Checksums detect accidental corruption, not a coordinated malicious rewrite.
Standalone schema validation does not establish source correspondence;
the pinned rebuild comparison does. Snapshot extraction is explicitly left
to the existing checksum-verifying gate. This review establishes no AL
execution, resumable run, resource bound, generated-code replay, target or
whole-corpus fidelity. Those remain separate required implementation stages.
