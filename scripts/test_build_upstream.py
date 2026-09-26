#!/usr/bin/env python3
"""Check upstream build failure propagation without fetching or compiling OCaml."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("build-upstream.sh")


class UpstreamBuildTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="upstream-build-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "repo with spaces"
        self.root.mkdir()
        subprocess.run(["git", "init", "--quiet", str(self.root)], check=True)
        scripts = self.root / "scripts"
        scripts.mkdir()
        self.script = scripts / SCRIPT.name
        shutil.copyfile(SCRIPT, self.script)
        self.up = self.root / "upstream" / "p4-spectec"
        (self.up / "p4spec" / "lib" / "parsing").mkdir(parents=True)
        self.bin = self.root / "tools"
        self.bin.mkdir()
        dune = self.bin / "dune"
        dune.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os, pathlib, sys\n"
            "pathlib.Path(os.environ['BUILD_TEST_ARGS']).write_text(json.dumps(sys.argv[1:]))\n"
            "print('dune diagnostic', file=sys.stderr)\n"
            "sys.exit(int(os.environ['BUILD_TEST_EXIT']))\n"
        )
        dune.chmod(0o755)
        self.args = self.root / "args.json"
        self.env = dict(os.environ, PATH=f"{self.bin}{os.pathsep}{os.environ['PATH']}",
                        BUILD_TEST_ARGS=str(self.args), BUILD_TEST_EXIT="0")

    def cached_executables(self):
        directory = self.up / "_build" / "default" / "p4spec" / "bin"
        directory.mkdir(parents=True)
        for name in ["main", "nano"]:
            path = directory / f"{name}.exe"
            path.write_text("#!/bin/sh\nexit 0\n")
            path.chmod(0o755)

    def run_build(self):
        return subprocess.run(["bash", str(self.script)], cwd=self.root.parent,
                              env=self.env, capture_output=True, text=True)

    def test_failed_build_rejects_cached_executables(self):
        self.cached_executables()
        self.env["BUILD_TEST_EXIT"] = "42"
        result = self.run_build()
        self.assertEqual(result.returncode, 42)
        self.assertIn("dune diagnostic", result.stderr)
        self.assertNotIn("main.exe", result.stdout)

    def test_success_requires_both_executables(self):
        result = self.run_build()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("main.exe missing", result.stderr)

    def test_missing_nano_is_rejected(self):
        self.cached_executables()
        (self.up / "_build/default/p4spec/bin/nano.exe").unlink()
        result = self.run_build()
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("nano.exe missing", result.stderr)

    def test_nonexecutable_output_is_rejected(self):
        self.cached_executables()
        for name in ["main", "nano"]:
            with self.subTest(name=name):
                path = self.up / f"_build/default/p4spec/bin/{name}.exe"
                path.chmod(0o644)
                result = self.run_build()
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(f"{name}.exe missing", result.stderr)
                path.chmod(0o755)

    def test_success_uses_explicit_root_and_targets(self):
        self.cached_executables()
        result = self.run_build()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(self.args.read_text()),
                         ["build", "--root", str(self.up.resolve()),
                          "p4spec/bin/main.exe", "p4spec/bin/nano.exe"])
        self.assertEqual(len(result.stdout.splitlines()), 2)


if __name__ == "__main__":
    unittest.main()
