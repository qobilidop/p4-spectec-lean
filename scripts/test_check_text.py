#!/usr/bin/env python3
"""Regression tests for the text gate's file enumeration and failure modes."""

import importlib.util
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).with_name("check-text.py")
SPEC = importlib.util.spec_from_file_location("check_text", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class TextGateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="text-gate-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(["git", "init", "--quiet", str(self.root)], check=True)

    def tracked(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        subprocess.run(["git", "-C", str(self.root), "add", "--", name], check=True)
        return path

    def test_valid_paths_and_empty_files(self):
        for name in ["plain.md", "a space.md", "a\nnewline.md", "unicode-λ.md"]:
            self.tracked(name, b"valid\n")
        self.tracked("empty.lean", b"")
        self.assertEqual(MODULE.check(self.root), [])

    def test_missing_tracked_file_fails(self):
        self.tracked("missing.md", b"valid\n").unlink()
        self.assertIn("cannot read", MODULE.check(self.root)[0])

    def test_staged_deletion_is_not_an_input(self):
        self.tracked("removed.md", b"valid\n").unlink()
        subprocess.run(["git", "-C", str(self.root), "add", "-u"], check=True)
        self.assertEqual(MODULE.check(self.root), [])

    def test_untracked_files_are_not_checked(self):
        (self.root / "scratch.md").write_bytes(b"not tracked ")
        self.assertEqual(MODULE.check(self.root), [])

    def test_whitespace_and_final_newline(self):
        self.tracked("bad.md", b"space \n\t\nmissing newline")
        errors = MODULE.check(self.root)
        self.assertEqual(len(errors), 3)
        self.assertTrue(any("no final newline" in error for error in errors))

    def test_python_and_yaml_are_checked(self):
        for name in ["script.py", "config.yaml", "config.yml"]:
            self.tracked(name, b"bad \n")
        self.assertEqual(len(MODULE.check(self.root)), 3)

    def test_invalid_utf8_fails(self):
        self.tracked("invalid.md", b"\xff\n")
        self.assertIn("cannot read", MODULE.check(self.root)[0])

    def test_read_failure_fails(self):
        self.tracked("unreadable.md", b"valid\n")
        with patch.object(Path, "read_bytes", side_effect=PermissionError("denied")):
            self.assertIn("cannot read", MODULE.check(self.root)[0])

    def test_lean_limits_and_script_import_exception(self):
        self.tracked("Long.lean", ("λ" * 100 + "\n" + "x" * 101 + "\n").encode())
        self.tracked("Url.lean", ("-- https://example.com/" + "x" * 120 + "\n").encode())
        self.tracked("Import.lean", b"import Lean\n")
        self.tracked("scripts/Probe.lean", b"import Lean\n")
        errors = MODULE.check(self.root)
        self.assertEqual(len(errors), 2)
        self.assertTrue(any("line over 100" in error for error in errors))
        self.assertTrue(any("bare 'import Lean'" in error for error in errors))

    def test_cli_fails_when_enumeration_fails(self):
        with tempfile.TemporaryDirectory(prefix="text-gate-nongit-") as directory:
            script = Path(directory) / "scripts" / SCRIPT.name
            script.parent.mkdir()
            shutil.copyfile(SCRIPT, script)
            result = subprocess.run([sys.executable, str(script)], capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("cannot enumerate", result.stdout)

    def test_shell_entry_point_from_another_directory(self):
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copyfile(SCRIPT, scripts / SCRIPT.name)
        shell = SCRIPT.with_suffix(".sh")
        shutil.copyfile(shell, scripts / shell.name)
        self.tracked("missing.md", b"valid\n").unlink()
        result = subprocess.run(
            ["bash", str(scripts / shell.name)], cwd=self.root.parent,
            capture_output=True, text=True,
        )
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("cannot read", result.stdout)


if __name__ == "__main__":
    unittest.main()
