#!/usr/bin/env python3
"""Offline exact-spec guard regressions; creates only disposable repositories."""

import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("spec_guard", ROOT / "scripts/check-spec-pin.py")
GUARD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GUARD)


class SpecGuardTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name).resolve()
        self.git("init", "--quiet")
        (self.root / "spec").mkdir()
        (self.root / "spec/main.watsup").write_text("fixture\n")
        (self.root / ".gitignore").write_text("ignored/\n*.extra.watsup\n")
        self.git("add", ".")
        self.git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
                 "-c", "commit.gpgsign=false", "commit", "--quiet", "-m", "Fixture")
        self.pin = self.git("rev-parse", "HEAD").decode().strip()

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.root), *args])

    def old_guard(self, path):
        # Reproduce both runners' prior HEAD/diff-only validation.
        self.assertEqual(subprocess.check_output(
            ["git", "-C", str(path), "rev-parse", "HEAD"], text=True).strip(), self.pin)
        subprocess.run(["git", "-C", str(path), "diff", "--exit-code", "HEAD"], check=True)

    def test_clean_exact_root_and_pin(self):
        self.assertEqual(GUARD.revision_guard(self.root, self.pin), self.pin)
        with self.assertRaisesRegex(ValueError, "gitlink"):
            GUARD.revision_guard(self.root, "0" * 40)
        with self.assertRaisesRegex(ValueError, "absolute"):
            GUARD.revision_guard(Path("relative"), self.pin)

    def test_subdirectory_old_false_acceptance(self):
        self.old_guard(self.root / "spec")
        with self.assertRaisesRegex(ValueError, "repository root"):
            GUARD.revision_guard(self.root / "spec", self.pin)

    def test_symlink_root_resolves_to_exact_root(self):
        with tempfile.TemporaryDirectory() as aliases:
            alias = Path(aliases).resolve() / "checkout"
            alias.symlink_to(self.root, target_is_directory=True)
            self.assertEqual(GUARD.revision_guard(alias, self.pin), self.pin)
            with self.assertRaisesRegex(ValueError, "repository root"):
                GUARD.revision_guard(alias / "spec", self.pin)

    def test_untracked_and_ignored_inputs_old_false_acceptance(self):
        for relative in ("added.watsup", "ignored/nested/added.watsup", "added.extra.watsup"):
            with self.subTest(relative=relative):
                path = self.root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("additional consumed input\n")
                self.old_guard(self.root)
                with self.assertRaisesRegex(ValueError, "untracked or ignored"):
                    GUARD.revision_guard(self.root, self.pin)
                path.unlink()

    def test_tracked_worktree_and_index_changes(self):
        path = self.root / "spec/main.watsup"
        path.write_text("changed\n")
        with self.assertRaises(subprocess.CalledProcessError):
            GUARD.revision_guard(self.root, self.pin)
        self.git("add", "spec/main.watsup")
        with self.assertRaises(subprocess.CalledProcessError):
            GUARD.revision_guard(self.root, self.pin)

    def test_untracked_directory_symlink(self):
        (self.root / "extra").symlink_to(self.root / "spec", target_is_directory=True)
        self.old_guard(self.root)
        with self.assertRaisesRegex(ValueError, "untracked or ignored"):
            GUARD.revision_guard(self.root, self.pin)


if __name__ == "__main__":
    unittest.main()
