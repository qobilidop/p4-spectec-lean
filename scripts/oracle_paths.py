"""Resolve stable oracle provenance identifiers to their current source locations.

Committed observations keep their original logical IDs. Source digests still
read current bytes, so a harness edit invalidates cached replay evidence.
"""
from pathlib import Path

LOCATIONS = {
 'test/nano-certification/corpus.json': 'P4SpecTecTest/Oracle/Nano/Certification/corpus.json',
 'test/p4-oracle/invalid.p4': 'P4SpecTecTest/Oracle/P4/Replay/invalid.p4',
 'test/nano-target/packet-observed.json.gz': 'P4SpecTecTest/Oracle/NanoSwitch/Packets/packet-observed.json.gz',
 'test/p4-corpus/shard.py': 'P4SpecTecTest/Oracle/P4/Corpus/shard.py',
 'test/p4-corpus/run.py': 'P4SpecTecTest/Oracle/P4/Corpus/campaign.py',
 'test/p4-corpus/contract.py': 'P4SpecTecTest/Oracle/P4/Corpus/contract.py',
 'test/p4-corpus/inventory.py': 'P4SpecTecTest/Oracle/P4/Corpus/inventory.py',
 'test/p4-corpus/probe.ml': 'P4SpecTecTest/Oracle/P4/Corpus/probe.ml',
 'P4SpecTecTest/Diff/P4Corpus/Main.lean': 'P4SpecTecTest/Oracle/P4/Corpus/Main.lean',
 'test/p4-oracle/check.py': 'P4SpecTecTest/Oracle/P4/Replay/check.py',
 'test/p4-oracle/replay.py': 'P4SpecTecTest/Oracle/P4/Replay/replay.py'}

def source_path(root: Path, logical: str) -> Path:
    """Resolve a repository source identifier without altering its recorded ID."""
    return root / LOCATIONS.get(logical, logical)
