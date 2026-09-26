#!/usr/bin/env python3
"""Offline contract checks for the bounded full-P4 Lean replay driver."""

import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
MODULE = ROOT / "test/p4-oracle/replay.py"
spec = importlib.util.spec_from_file_location("p4_replay", MODULE)
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)
check = replay.load_check()


class ReplayContractTest(unittest.TestCase):
    def setUp(self):
        self.revision = "a" * 40
        self.fixture = {
            "upstreamRevision": self.revision,
            "cases": [
                {"name": name, "source": source, "path": path,
                 "expected": {"bootSha256": "digest"}}
                for name, source, path in check.EXPECTED_CASES
            ],
        }

    def validate(self, fixture):
        return replay.validate_fixture(fixture, self.revision, check.EXPECTED_CASES)

    def test_fixed_manifest_passes(self):
        self.assertEqual(len(self.validate(self.fixture)), 4)

    def test_revision_mismatch_fails(self):
        fixture = copy.deepcopy(self.fixture)
        fixture["upstreamRevision"] = "b" * 40
        with self.assertRaises(ValueError):
            self.validate(fixture)

    def test_missing_reordered_or_duplicated_case_fails(self):
        for cases in (self.fixture["cases"][:-1],
                      list(reversed(self.fixture["cases"])),
                      [self.fixture["cases"][0]] * 4):
            fixture = copy.deepcopy(self.fixture)
            fixture["cases"] = cases
            with self.subTest(cases=cases), self.assertRaises(ValueError):
                self.validate(fixture)

    def test_missing_or_empty_expectation_fails(self):
        for expected in (None, {}, []):
            fixture = copy.deepcopy(self.fixture)
            fixture["cases"][0]["expected"] = expected
            with self.subTest(expected=expected), self.assertRaises(ValueError):
                self.validate(fixture)

    def test_extra_fixture_field_fails(self):
        fixture = copy.deepcopy(self.fixture)
        fixture["cases"][0]["allowFailure"] = True
        with self.assertRaises(ValueError):
            self.validate(fixture)

    def test_changed_observation_digest_fails_before_lean(self):
        source = ROOT / "test/p4-oracle/invalid.p4"
        self.assertTrue(source.is_file())
        fixture = {"upstreamRevision": self.revision,
                   "cases": [{"name": "syntax-error", "source": "repo",
                              "path": "test/p4-oracle/invalid.p4",
                              "expected": {"bootSha256": "expected"}}]}

        class FakeAdapter:
            def revision_guard(self, _upstream):
                return "a" * 40

            def compile_probe(self, _upstream):
                return Path("/unused/probe")

            def observe(self, *_args):
                return {"boot": None, "relations": {}}

        class FakeCheck:
            EXPECTED_CASES = (("syntax-error", "repo", "test/p4-oracle/invalid.p4"),)

            def load_export(self):
                return FakeAdapter()

            def p4c_pin_guard(self, *_args):
                pass

            def summarize(self, *_args):
                return {"bootSha256": "corrupted"}

            def check_cli(self, *_args):
                pass

        with tempfile.TemporaryDirectory() as scratch:
            path = Path(scratch) / "fixture.json"
            path.write_text(json.dumps(fixture), encoding="utf-8")
            with patch.object(replay, "FIXTURE", path):
                with self.assertRaisesRegex(ValueError, "differs from fixture"):
                    replay.collect(FakeCheck(), Path("/unused/upstream"),
                                   Path("/unused/p4c"))


if __name__ == "__main__":
    unittest.main()
