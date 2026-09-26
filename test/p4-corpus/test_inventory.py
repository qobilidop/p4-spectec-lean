#!/usr/bin/env python3
"""Offline canonical inventory and corruption checks; no external checkout needed."""

import copy
import json
from pathlib import Path
import tempfile
import unittest

import inventory


def fixture():
    cases = [{"path": inventory.PREFIX + name + ".p4", "sha256": "a" * 64,
              "symlink": None, "exclusions": [], "collectorOmission": None}
             for name in ("a", "b", "c")]
    cases[1]["exclusions"] = [{"manifest": "excludes/static/p4c/a.exclude", "line": 2}]
    value = {"schemaVersion": 1, "upstreamRevision": "1" * 40, "p4cRevision": "2" * 40,
             "snapshotSha256": "3" * 64, "cases": cases,
             "exclusionFiles": [{"path": "excludes/static/p4c/a.exclude", "sha256": "b" * 64}],
             "staleExclusions": [], "counts": inventory.counts(cases, [])}
    value["inventorySha256"] = inventory.digest(inventory.encode(value))
    return value


class InventoryTests(unittest.TestCase):
    def test_literal_exclusion_lines_and_eof(self):
        self.assertEqual(inventory.exclude_lines(b"#comment\n x\n\nend"),
                         [(2, " x"), (3, ""), (4, "end")])
        self.assertEqual(inventory.exclude_lines(b""), [])
        self.assertEqual(inventory.exclude_lines(b"x\r\n"), [(1, "x\r")])

    def test_traversal_and_symlink_identity(self):
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            (root / "include").mkdir()
            (root / "include/skipped.p4").touch()
            (root / "nested").mkdir()
            (root / "nested/target.p4").touch()
            (root / "alias.p4").symlink_to("nested/target.p4")
            self.assertEqual([p.relative_to(root).as_posix()
                              for p in inventory.collect_files(root, ".p4")],
                             ["alias.p4", "nested/target.p4"])

    def test_shards_partition_only_candidates(self):
        value = fixture()
        inventory.validate_manifest(value)
        parts = [inventory.shard(value, i, 3) for i in range(3)]
        self.assertEqual([[c["path"] for c in part] for part in parts],
                         [[inventory.PREFIX + "a.p4"], [inventory.PREFIX + "c.p4"], []])
        for index, total in ((0, 0), (-1, 2), (2, 2), (True, 2), (0, True)):
            with self.subTest(index=index, total=total), self.assertRaises(ValueError):
                inventory.shard(value, index, total)

    def test_corruption_cannot_pass(self):
        mutations = [lambda v: v["counts"].update(candidates=3),
                     lambda v: v.update(inventorySha256="0" * 64),
                     lambda v: v["cases"][0].update(sha256="0" * 64),
                     lambda v: v["cases"].reverse(),
                     lambda v: v["cases"].append(copy.deepcopy(v["cases"][0])),
                     lambda v: v["cases"][0].update(path=inventory.PREFIX + "../a.p4"),
                     lambda v: v["cases"][1]["exclusions"][0].update(line=True),
                     lambda v: v["cases"][1]["exclusions"][0].update(
                         manifest="excludes/static/unknown.exclude"),
                     lambda v: v.update(schemaVersion=True),
                     lambda v: v.update(cases=[]),
                     lambda v: v.update(upstreamRevision="bad")]
        mutations += [lambda v: v["cases"][0].update(collectorOmission="include-directory"),
                      lambda v: v["counts"].update(staleReferences=True)]
        for index, mutate in enumerate(mutations):
            value = fixture()
            mutate(value)
            with self.subTest(index=index), self.assertRaises(ValueError):
                inventory.validate_manifest(value)

    def test_committed_manifest(self):
        value = json.loads(inventory.MANIFEST.read_text())
        inventory.validate_manifest(value)
        self.assertEqual(value["counts"], {"paths": 1352, "symlinks": 5, "excluded": 67,
                                        "candidates": 1267, "positiveReferences": 68,
                                        "staleReferences": 1, "collectorPaths": 1334,
                                        "collectorOmitted": 18})
        omitted = [case for case in value["cases"] if case["collectorOmission"]]
        self.assertEqual(len(omitted), 18)
        self.assertTrue(all(case["path"].startswith(
            inventory.PREFIX + "fabric_20190420/include/") for case in omitted))
        self.assertEqual(value["staleExclusions"][0]["path"],
                         inventory.PREFIX + "issue3291-1.p4")


if __name__ == "__main__":
    unittest.main()
