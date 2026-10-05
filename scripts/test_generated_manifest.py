"""The generated-library manifest rejects every kind of drift from the recorded files."""

import importlib.util
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "generated_manifest", ROOT / "scripts/generated-manifest.py")
manifest = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(manifest)


class GeneratedManifestTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.directory.name)
        (self.root / "Lib.lean").write_text("import Lib.A\n")
        (self.root / "Lib/Sub").mkdir(parents=True)
        (self.root / "Lib/A.lean").write_text("def a := 1\n")
        (self.root / "Lib/Sub/coverage.json").write_text("{}\n")
        self.recorded = self.root / "Lib.manifest.json"

    def tearDown(self):
        self.directory.cleanup()

    def run_tool(self, mode):
        return manifest.main([mode, "Lib", str(self.recorded), "--root", str(self.root)])

    def test_round_trip_and_drift(self):
        self.assertEqual(self.run_tool("--update"), 0)
        first = self.recorded.read_text()
        self.assertEqual(self.run_tool("--update"), 0)
        self.assertEqual(self.recorded.read_text(), first)
        self.assertEqual(self.run_tool("--check"), 0)
        self.assertEqual(
            sorted(manifest.inventory(self.root, "Lib")["files"]),
            ["Lib.lean", "Lib/A.lean", "Lib/Sub/coverage.json"])

        changed = self.root / "Lib/A.lean"
        changed.write_text("def a := 2\n")
        self.assertEqual(self.run_tool("--check"), 1)
        changed.write_text("def a := 1\n")
        self.assertEqual(self.run_tool("--check"), 0)

        extra = self.root / "Lib/Stale.lean"
        extra.write_text("def stale := 0\n")
        self.assertEqual(self.run_tool("--check"), 1)
        extra.unlink()

        (self.root / "Lib/Sub/coverage.json").unlink()
        self.assertEqual(self.run_tool("--check"), 1)

    def test_unusable_inputs(self):
        self.assertEqual(self.run_tool("--check"), 1)  # no manifest yet
        self.assertEqual(self.run_tool("--update"), 0)
        self.recorded.write_text("[]\n")
        self.assertEqual(self.run_tool("--check"), 1)
        self.assertEqual(self.run_tool("--update"), 0)
        (self.root / "Lib/Link.lean").symlink_to(self.root / "Lib/A.lean")
        self.assertEqual(self.run_tool("--check"), 1)
        (self.root / "Lib/Link.lean").unlink()
        self.assertEqual(
            manifest.main(["--check", "Other", str(self.recorded), "--root", str(self.root)]), 1)
        (self.root / "Other.lean").write_text("")
        (self.root / "Other").mkdir()
        self.assertEqual(
            manifest.main(["--check", "Other", str(self.recorded), "--root", str(self.root)]), 1)


if __name__ == "__main__":
    unittest.main()
