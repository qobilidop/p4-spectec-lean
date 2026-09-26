#!/usr/bin/env python3
"""Offline packet fixture provenance, shape and resource-bound sensitivities."""

import copy
import gzip
import pathlib
import tempfile
import unittest
from unittest import mock
import fixture


class Contract(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bundle, cls.raw = fixture.read()

    def test_current_fixture(self):
        fixture.validate(self.bundle)
        self.assertEqual(sum(len(c["observation"]["events"])
                             for c in self.bundle["cases"]), 7)

    def test_envelope(self):
        for key, bad in [("schemaVersion", True), ("schemaVersion", 2),
                         ("upstreamRevision", "bad"), ("nanoSpecRevision", "bad"),
                         ("cache", True), ("det", True), ("relation", "Program_ok")]:
            with self.subTest(key=key, bad=bad), self.assertRaises(ValueError):
                fixture.validate({**self.bundle, key: bad})

    def test_missing_reordered_or_added_case(self):
        for cases in [self.bundle["cases"][:-1], list(reversed(self.bundle["cases"])),
                      self.bundle["cases"] + self.bundle["cases"][:1]]:
            with self.assertRaises(ValueError):
                fixture.validate({**self.bundle, "cases": cases})

    def test_forged_source_hash(self):
        for key in ("programSha256", "stfSha256"):
            bad = copy.deepcopy(self.bundle)
            bad["cases"][0][key] = "0" * 64
            with self.assertRaisesRegex(ValueError, "pinned Git object"):
                fixture.validate(bad)

    def test_event_shape_and_counter(self):
        for key, value in [("inputs", []), ("outputs", []),
                           ("counterBefore", 2**62), ("counterAfter", True),
                           ("class", "skip")]:
            bad = copy.deepcopy(self.bundle)
            bad["cases"][0]["observation"]["events"][0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                fixture.validate(bad)

    def test_duplicate_keys(self):
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            fixture.strict_json('{"schemaVersion":1,"schemaVersion":1}')

    def test_nonfinite_constants(self):
        for value in ("NaN", "Infinity", "-Infinity"):
            with self.assertRaisesRegex(ValueError, "nonfinite JSON constant"):
                fixture.strict_json('{"value":' + value + '}')

    def check_bad_file(self, packed, expected):
        with tempfile.TemporaryDirectory(prefix="nano-packet-contract-") as temporary:
            path = pathlib.Path(temporary) / "packet.json"
            path.with_suffix(".json.gz").write_bytes(packed)
            path.with_suffix(".json.sha256").write_text("wrong checksum\n")
            with mock.patch.object(fixture, "PACKET", path):
                with self.assertRaisesRegex(ValueError, expected):
                    fixture.read()

    def test_checksum(self):
        self.check_bad_file(gzip.compress(self.raw, mtime=0), "checksum mismatch")

    def test_compressed_bound(self):
        self.check_bad_file(b"x" * (1024 * 1024 + 1), "compressed size")

    def test_expanded_bound(self):
        self.check_bad_file(gzip.compress(b"x" * (8 * 1024 * 1024 + 1), mtime=0),
                            "expanded size")


if __name__ == "__main__":
    unittest.main()
