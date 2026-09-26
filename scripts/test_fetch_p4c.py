#!/usr/bin/env python3
"""Offline contract tests for the pinned sparse p4c restore script."""

from pathlib import Path
import os
import shutil
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).resolve().parent / "fetch-p4c.sh"
URL = "https://example.invalid/p4c"
SPARSE_PATHS = ("p4include", "testdata/p4_16_samples", "backends/ubpf/tests/testdata")


class FetchP4cTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory(prefix="fetch-p4c-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "project"
        self.root.mkdir()
        self.up = self.root / "upstream/p4-spectec"
        self.up.mkdir(parents=True)
        self.dest = self.root / ".artifacts/p4c"
        self.dest.mkdir(parents=True)
        scripts = self.root / "scripts"
        scripts.mkdir()
        shutil.copy2(SCRIPT, scripts / "fetch-p4c.sh")
        self.script = scripts / "fetch-p4c.sh"
        self.env = os.environ.copy()
        self.env.update(
            GIT_CONFIG_NOSYSTEM="1",
            GIT_CONFIG_GLOBAL=os.devnull,
            GIT_TERMINAL_PROMPT="0",
            GIT_CONFIG_COUNT="1",
            GIT_CONFIG_KEY_0="protocol.https.allow",
            GIT_CONFIG_VALUE_0="never",
        )
        self.git("init", "-q", str(self.root))
        self.git("init", "-q", str(self.up))
        self.git("init", "-q", str(self.dest))
        self.write(self.dest / "p4include/core.p4", "// core\n")
        self.write(self.dest / "testdata/p4_16_samples/good.p4", "#include <core.p4>\n")
        self.write(self.dest / "backends/ubpf/tests/testdata/target.p4", "// target\n")
        self.link = self.dest / "testdata/p4_16_samples/link.p4"
        self.link.symlink_to("../../backends/ubpf/tests/testdata/target.p4")
        self.git("-C", str(self.dest), "add", "-A")
        self.commit(self.dest, "Fixture p4c")
        self.pin = self.git("-C", str(self.dest), "rev-parse", "HEAD").stdout.strip()
        self.git("-C", str(self.dest), "remote", "add", "origin", URL)
        self.git("-C", str(self.dest), "sparse-checkout", "set", *SPARSE_PATHS)
        self.write(self.up / ".gitmodules", f'[submodule "p4c"]\n\tpath = p4c\n\turl = {URL}\n')
        self.git("-C", str(self.up), "add", ".gitmodules")
        self.git(
            "-C", str(self.up), "update-index", "--add", "--cacheinfo",
            f"160000,{self.pin},p4c",
        )
        self.commit(self.up, "Fixture upstream")
        up_pin = self.git("-C", str(self.up), "rev-parse", "HEAD").stdout.strip()
        self.git(
            "-C", str(self.root), "update-index", "--add", "--cacheinfo",
            f"160000,{up_pin},upstream/p4-spectec",
        )
        self.commit(self.root, "Fixture project")

    @staticmethod
    def write(path: Path, contents: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(contents)

    def git(self, *args: str) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["git", *args], env=self.env, text=True, capture_output=True, check=True
        )

    def commit(self, repo: Path, message: str) -> None:
        self.git(
            "-C", str(repo), "-c", "user.name=Fixture", "-c",
            "user.email=fixture@example.invalid", "commit", "-qm", message,
        )

    def fetch(self) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            [str(self.script)], env=self.env, text=True, capture_output=True, check=False
        )

    def assert_refused(self, reason: str) -> None:
        result = self.fetch()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(reason, result.stderr)

    def test_exact_pin_is_idempotent_without_network(self) -> None:
        for _ in range(2):
            result = self.fetch()
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn(f"2 samples at {self.pin}", result.stdout)
        actual = self.git("-C", str(self.dest), "rev-parse", "HEAD").stdout.strip()
        self.assertEqual(actual, self.pin)
        self.assertEqual(self.git("-C", str(self.dest), "status", "--porcelain").stdout, "")

    def test_dirty_working_gitmodules_does_not_change_pinned_url(self) -> None:
        self.write(
            self.up / ".gitmodules",
            '[submodule "p4c"]\n\tpath = p4c\n\turl = https://wrong.invalid/p4c\n',
        )
        result = self.fetch()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        actual = self.git("-C", str(self.dest), "remote", "get-url", "origin").stdout.strip()
        self.assertEqual(actual, URL)

    def test_dirty_checkout_is_refused(self) -> None:
        self.write(self.dest / "untracked.txt", "dirty\n")
        self.assert_refused("artifact checkout is dirty")

    def test_wrong_pin_is_refused(self) -> None:
        self.write(self.dest / "README.md", "next commit\n")
        self.git("-C", str(self.dest), "add", "README.md")
        self.commit(self.dest, "Different p4c pin")
        self.assert_refused("artifact checkout is at a different commit")

    def test_wrong_origin_is_refused(self) -> None:
        self.git("-C", str(self.dest), "remote", "set-url", "origin", "https://wrong.invalid/p4c")
        self.assert_refused("artifact checkout has a different origin URL")

    def test_non_checkout_destination_is_refused(self) -> None:
        shutil.rmtree(self.dest)
        self.dest.mkdir()
        self.assert_refused("destination exists but is not a Git checkout")

    def test_wrong_checkout_root_is_refused(self) -> None:
        shutil.rmtree(self.dest)
        self.dest.mkdir()
        self.write(self.dest / ".git", f"gitdir: {self.up / '.git'}\n")
        self.git("-C", str(self.up), "config", "core.worktree", str(self.up))
        self.assert_refused("artifact destination is not its Git checkout root")

    def test_artifact_root_symlink_is_refused(self) -> None:
        real = self.root / ".artifacts-real"
        self.dest.parent.rename(real)
        (self.root / ".artifacts").symlink_to(real, target_is_directory=True)
        self.assert_refused("symlink artifact root")

    def test_destination_symlink_is_refused(self) -> None:
        real = self.dest.parent / "p4c-real"
        self.dest.rename(real)
        self.dest.symlink_to(real, target_is_directory=True)
        self.assert_refused("symlink artifact destination")

    def test_broken_sample_link_is_refused(self) -> None:
        self.link.unlink()
        self.link.symlink_to("../../backends/ubpf/tests/testdata/missing.p4")
        self.git("-C", str(self.dest), "add", "testdata/p4_16_samples/link.p4")
        self.commit(self.dest, "Broken sample link")
        new_pin = self.git("-C", str(self.dest), "rev-parse", "HEAD").stdout.strip()
        self.git(
            "-C", str(self.up), "update-index", "--add", "--cacheinfo",
            f"160000,{new_pin},p4c",
        )
        self.commit(self.up, "Pin broken sample")
        up_pin = self.git("-C", str(self.up), "rev-parse", "HEAD").stdout.strip()
        self.git(
            "-C", str(self.root), "update-index", "--add", "--cacheinfo",
            f"160000,{up_pin},upstream/p4-spectec",
        )
        self.commit(self.root, "Pin broken upstream")
        self.assert_refused("sample symlink has no restored target")


if __name__ == "__main__":
    unittest.main()
