"""The size gate checks staged blobs as well as tracked working files."""

import importlib.util
import pathlib
import subprocess
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("sizes", ROOT / "scripts/check-file-sizes.py")
sizes = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(sizes)


class FileSizeTest(unittest.TestCase):
    def test_staged_and_working_sizes(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            subprocess.run(["git", "init", "--quiet", str(root)], check=True)
            path = root / "file with spaces"
            path.write_bytes(b"1234")
            subprocess.run(["git", "-C", str(root), "add", "--", path.name], check=True)
            self.assertEqual(sizes.oversized(root, 4), [])
            self.assertEqual(sizes.oversized(root, 3), [(path.name, 4)])
            path.write_bytes(b"1")
            self.assertEqual(sizes.oversized(root, 3), [(path.name, 4)])
            path.write_bytes(b"123456")
            self.assertEqual(sizes.oversized(root, 5), [(path.name, 6)])
            path.unlink()
            self.assertEqual(sizes.oversized(root, 3), [(path.name, 4)])
            subprocess.run(["git", "-C", str(root), "add", "-u"], check=True)
            self.assertEqual(sizes.oversized(root, 3), [])


if __name__ == "__main__":
    unittest.main()
