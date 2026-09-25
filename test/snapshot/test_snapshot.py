"""Lossless, deterministic snapshots; failed verification preserves the cache."""

import importlib.util
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("snapshot", ROOT / "scripts/spec-snapshot.py")
snapshot = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(snapshot)


class SnapshotTest(unittest.TestCase):
    def test_round_trip_and_determinism(self):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "fixture.json"
            original = b'{"unicode": "\xc3\xa9", "whitespace": [ 1, 2 ]}\n'
            path.write_bytes(original)
            snapshot.pack(path)
            archive = path.with_suffix(".json.gz")
            first = archive.read_bytes()
            snapshot.pack(path)
            self.assertEqual(archive.read_bytes(), first)
            path.unlink()
            snapshot.unpack(path)
            self.assertEqual(path.read_bytes(), original)
            self.assertEqual(sorted(p.name for p in path.parent.iterdir()),
                             ["fixture.json", "fixture.json.gz", "fixture.json.sha256"])

    def test_bad_checksum_preserves_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "fixture.json"
            path.write_bytes(b"{}")
            snapshot.pack(path)
            path.with_suffix(".json.sha256").write_text("wrong\n")
            path.write_bytes(b"existing cache")
            with self.assertRaisesRegex(ValueError, "checksum mismatch"):
                snapshot.unpack(path)
            self.assertEqual(path.read_bytes(), b"existing cache")

    def test_corruption_preserves_cache(self):
        with tempfile.TemporaryDirectory() as directory:
            path = pathlib.Path(directory) / "fixture.json"
            path.write_bytes(b"{}")
            snapshot.pack(path)
            path.with_suffix(".json.gz").write_bytes(b"not gzip")
            with self.assertRaises(OSError):
                snapshot.unpack(path)
            self.assertEqual(path.read_bytes(), b"{}")


if __name__ == "__main__":
    unittest.main()
