"""Golden samples are exact copies of generated files, and every kind of drift fails."""

import importlib.util
import os
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "golden_samples", ROOT / "scripts/golden-samples.py")
golden = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(golden)


class GoldenSamplesTest(unittest.TestCase):
    def setUp(self):
        self.directory = tempfile.TemporaryDirectory()
        self.root = pathlib.Path(self.directory.name).resolve()
        self.generated, self.samples = self.root / "Lib", self.root / "Lib.samples"
        (self.generated / "Sub").mkdir(parents=True)
        (self.generated / "A.lean").write_text("def a := 1\n")
        (self.generated / "Sub/B.lean").write_text("def b := 2\n")
        (self.generated / "Sub/C.json").write_text("{}\n")
        (self.root / "outside.lean").write_text("def outside := 0\n")

    def tearDown(self):
        self.directory.cleanup()

    def run_tool(self, mode, *added):
        return golden.main([mode, "Lib", "Lib.samples", *added, "--root", str(self.root)])

    def sampled(self):
        return sorted(p.relative_to(self.samples).as_posix()
                      for p in self.samples.rglob("*") if p.is_file())

    def test_round_trip_and_drift(self):
        self.assertEqual(self.run_tool("--check"), 1)  # no samples directory
        self.assertEqual(self.run_tool("--update"), 1)  # nothing named
        self.assertFalse(self.samples.exists())  # a refused update creates nothing
        self.assertEqual(self.run_tool("--update", "A.lean", "Sub/B.lean"), 0)
        self.assertEqual(self.run_tool("--check"), 0)
        self.assertEqual(self.sampled(), ["A.lean", "Sub/B.lean"])

        (self.generated / "Sub/B.lean").write_text("def b := 20\n")
        self.assertEqual(self.run_tool("--check"), 1)
        self.assertEqual(golden.differences(self.generated, self.samples)[1], ["Sub/B.lean"])
        # naming a new sample refreshes the existing ones too, and any file kind counts
        self.assertEqual(self.run_tool("--update", "Sub/C.json"), 0)
        self.assertEqual(self.run_tool("--check"), 0)
        self.assertEqual(self.sampled(), ["A.lean", "Sub/B.lean", "Sub/C.json"])
        self.assertEqual((self.samples / "Sub/B.lean").read_text(), "def b := 20\n")

        (self.samples / "A.lean").write_text("def a := 1 -- edited by hand\n")
        self.assertEqual(self.run_tool("--check"), 1)

    def test_working_directory_does_not_matter(self):
        previous = os.getcwd()
        with tempfile.TemporaryDirectory() as elsewhere:
            os.chdir(elsewhere)
            try:
                self.assertEqual(self.run_tool("--update", "A.lean"), 0)
                self.assertEqual(self.run_tool("--check"), 0)
                self.assertEqual(os.listdir(elsewhere), [])
            finally:
                os.chdir(previous)

    def test_an_empty_sample_set_is_not_a_pass(self):
        (self.samples / "Sub").mkdir(parents=True)
        self.assertEqual(self.run_tool("--check"), 1)
        self.assertEqual(self.run_tool("--update", "A.lean"), 0)  # empty directories are fine
        self.assertEqual(self.run_tool("--check"), 0)

    def test_a_sample_needs_its_generated_file(self):
        self.assertEqual(self.run_tool("--update", "A.lean"), 0)
        (self.generated / "Sub/B.lean").write_text("def b := 3\n")
        # one bad name refuses the whole update: nothing is refreshed or added
        self.assertEqual(self.run_tool("--update", "Sub/B.lean", "Missing.lean"), 1)
        self.assertEqual(self.sampled(), ["A.lean"])
        (self.generated / "A.lean").unlink()
        self.assertEqual(self.run_tool("--check"), 1)
        self.assertEqual(self.run_tool("--update"), 1)

    def test_paths_stay_inside_the_generated_library(self):
        for name in ("../outside.lean", str(self.root / "outside.lean"), "Sub/../../outside.lean"):
            with self.subTest(name=name):
                self.assertEqual(self.run_tool("--update", name), 1)
                self.assertFalse(self.samples.exists())

    def test_symlinks_are_rejected(self):
        self.assertEqual(self.run_tool("--update", "A.lean", "Sub/B.lean"), 0)
        # a sample that links to its own generated file would always compare equal
        (self.samples / "Sub/B.lean").unlink()
        (self.samples / "Sub/B.lean").symlink_to(self.generated / "Sub/B.lean")
        self.assertEqual(self.run_tool("--check"), 1)
        (self.samples / "Sub/B.lean").unlink()
        (self.samples / "Sub/B.lean").write_text("def b := 2\n")
        self.assertEqual(self.run_tool("--check"), 0)

        # a generated file or directory reached through a link is not the generated library
        (self.generated / "Sub/B.lean").unlink()
        (self.generated / "Sub/B.lean").symlink_to(self.samples / "Sub/B.lean")
        self.assertEqual(self.run_tool("--check"), 1)
        (self.generated / "Sub/B.lean").unlink()
        (self.generated / "Sub/B.lean").write_text("def b := 2\n")
        (self.generated / "Linked").symlink_to(self.generated / "Sub")
        self.assertEqual(self.run_tool("--update", "Linked/B.lean"), 1)

    def test_directories_reached_through_links_are_rejected(self):
        self.assertEqual(self.run_tool("--update", "A.lean"), 0)
        real = self.root / "Real.samples"
        self.samples.rename(real)
        self.samples.symlink_to(real)
        self.assertEqual(self.run_tool("--check"), 1)
        self.assertEqual(self.run_tool("--update"), 1)
        self.samples.unlink()
        real.rename(self.samples)
        moved = self.root / "RealLib"
        self.generated.rename(moved)
        self.generated.symlink_to(moved)
        self.assertEqual(self.run_tool("--check"), 1)
        self.assertEqual(self.run_tool("--update"), 1)


if __name__ == "__main__":
    unittest.main()
