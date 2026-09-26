#!/usr/bin/env python3
"""Shared exact-pin, rebuild and workspace safety boundary checks."""

import os
from pathlib import Path
import pathlib
import tempfile
import types
import unittest
from unittest import mock
import oracle_build

ROOT = oracle_build.ROOT

class Provenance(unittest.TestCase):
    def test_exact_source_contract(self):
        upstream = pathlib.Path("/fake/upstream")
        status = "".join(f" M {path}\n" for path in oracle_build.PATCHED_FILES)
        good = ["160000 pin 0 upstream/p4-spectec\n", "pin\n",
                str(upstream) + "\n", b"patch\n", b"patch\n", status]
        with mock.patch.object(oracle_build.subprocess, "check_output", side_effect=good):
            self.assertEqual(oracle_build.revision_guard(upstream), "pin")
        for name, index, changed in (
                ("pin", 0, "160000 other 0 upstream/p4-spectec\n"),
                ("root", 2, "/fake/parent\n"),
                ("semantic edit", 4, b"patch and semantic edit\n"),
                ("untracked", 5, status + "?? p4spec/lib/extra.ml\n")):
            with self.subTest(name=name):
                answers = good.copy()
                answers[index] = changed
                with mock.patch.object(oracle_build.subprocess, "check_output", side_effect=answers):
                    with self.assertRaises(SystemExit):
                        oracle_build.revision_guard(upstream)

    def test_failed_rebuild_stops_before_link(self):
        with mock.patch.object(oracle_build.subprocess, "run",
                               return_value=types.SimpleNamespace(returncode=1)) as run, \
             mock.patch.object(oracle_build.shutil, "copyfile") as copy:
            with self.assertRaisesRegex(SystemExit, "rebuild"):
                oracle_build.compile_probe(Path("/fake/upstream"),
                                           probe=Path("/probe.ml"), scratch=Path("/scratch"))
        run.assert_called_once_with(["dune", "build", "p4spec/bin/main.exe"],
                                    cwd=Path("/fake/upstream"))
        copy.assert_not_called()

class CompileWorkspaceTests(unittest.TestCase):
    def test_outside_hardlink_alias_is_never_overwritten(self):
        adapter = oracle_build
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            workspace_root = root / "workspaces"
            probe = ROOT / "P4SpecTecTest/Oracle/P4/Corpus/probe.ml"
            workspace = workspace_root / ("c" * 64)
            workspace.mkdir(parents=True)
            outside = root / "outside"
            outside.write_bytes(b"outside alias must remain untouched")
            for name in ("probe.ml", "probe", "probe.o", "probe.cmi", "probe.cmx"):
                alias = workspace / name
                os.link(outside, alias)
                with self.subTest(name=name), mock.patch.object(adapter.subprocess, "run") as process:
                    process.return_value.returncode = 0
                    with self.assertRaisesRegex(SystemExit, "single-link regular"):
                        adapter.compile_probe(Path("/upstream"), probe=probe, scratch=workspace_root, workspace_key="c" * 64)
                    self.assertEqual(process.call_count, 1)  # Rebuild only, never invoke compiler.
                    self.assertEqual(outside.read_bytes(), b"outside alias must remain untouched")
                alias.unlink()

    def test_special_entries_and_post_copy_revalidation(self):
        adapter = oracle_build
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            workspace_root = root / "workspaces"
            probe = ROOT / "P4SpecTecTest/Oracle/P4/Corpus/probe.ml"
            workspace = workspace_root / ("d" * 64)
            workspace.mkdir(parents=True)
            special = workspace / "probe.o"
            for make, remove in ((lambda: special.mkdir(), lambda: special.rmdir()),
                                 (lambda: special.symlink_to(probe),
                                  lambda: special.unlink()),
                                 (lambda: os.mkfifo(special), lambda: special.unlink())):
                make()
                with mock.patch.object(adapter.subprocess, "run") as process:
                    process.return_value.returncode = 0
                    with self.assertRaisesRegex(SystemExit, "single-link regular"):
                        adapter.compile_probe(Path("/upstream"), probe=probe, scratch=workspace_root, workspace_key="d" * 64)
                    self.assertEqual(process.call_count, 1)
                remove()
            outside = root / "outside"
            outside.write_bytes(b"unchanged")
            original_copy = adapter.shutil.copyfile
            def inject_link(source, destination):
                original_copy(source, destination)
                os.link(outside, workspace / "probe")
            with mock.patch.object(adapter.shutil, "copyfile", side_effect=inject_link), \
                 mock.patch.object(adapter.subprocess, "run") as process:
                process.return_value.returncode = 0
                with self.assertRaisesRegex(SystemExit, "single-link regular"):
                    adapter.compile_probe(Path("/upstream"), probe=probe, scratch=workspace_root, workspace_key="d" * 64)
                self.assertEqual(process.call_count, 1)
                self.assertEqual(outside.read_bytes(), b"unchanged")

    def test_default_actual_pid_and_explicit_key(self):
        adapter = oracle_build
        with tempfile.TemporaryDirectory() as scratch:
            workspace_root = Path(scratch)
            probe = ROOT / "P4SpecTecTest/Oracle/P4/Corpus/probe.ml"
            with mock.patch.object(adapter.subprocess, "run") as process:
                process.return_value.returncode = 0
                default = adapter.compile_probe(Path("/upstream"), probe=probe, scratch=workspace_root)
                keyed = adapter.compile_probe(Path("/upstream"), probe=probe, scratch=workspace_root, workspace_key="a" * 64)
            self.assertEqual(default, Path(scratch) / str(os.getpid()) / "probe")
            self.assertEqual(keyed, Path(scratch) / ("a" * 64) / "probe")
            commands = [call.args[0] for call in process.call_args_list]
            self.assertEqual(commands[0], ["dune", "build", "p4spec/bin/main.exe"])
            self.assertEqual(commands[1][-3:], [str(default.with_suffix(".ml")), "-o", str(default)])
            for key in ("../escape", "A" * 64, "0" * 63, 1, True):
                with self.subTest(key=key), self.assertRaises(SystemExit):
                    adapter.compile_probe(Path("/upstream"), probe=probe, scratch=workspace_root, workspace_key=key)
            (Path(scratch) / ("b" * 64)).symlink_to(Path(scratch) / ("a" * 64))
            with mock.patch.object(adapter.subprocess, "run") as process, self.assertRaises(SystemExit):
                process.return_value.returncode = 0
                adapter.compile_probe(Path("/upstream"), probe=probe, scratch=workspace_root, workspace_key="b" * 64)


if __name__ == "__main__":
    unittest.main()
