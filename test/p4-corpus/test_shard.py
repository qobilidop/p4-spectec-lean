#!/usr/bin/env python3
"""Offline durable shard, security, resume and compile-workspace contracts."""

import copy
import gzip
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import contract
import inventory
import run
import shard
from test_contract import ADAPTER, fixture


NAME = "p4c/testdata/p4_16_samples/synthetic.p4"


def identity():
    return {"schemaVersion": 1, "selection": [{"path": NAME, "sha256": "0" * 64}],
            "canonicalCounts": {"paths": 1352, "collectorOmitted": 18, "excluded": 67,
                                "candidates": 1267}, "limits": {"fuel": 10000000}}


def observation():
    value = fixture()
    value["name"] = NAME
    return value


def verdict():
    return {"name": NAME, "relations": {key: {"status": "matched", "leanClass": "pass",
                                             "message": ""} for key in contract.RELATIONS}}


def cli():
    return {key: {"exit": 0, "stdoutSha256": inventory.digest(b"passed\n"),
                  "stderrSha256": inventory.digest(b""), "seconds": 0.1}
            for key in contract.RELATIONS}


def record(store, reference=None, kind="semantic"):
    return {"schemaVersion": 1, "identitySha256": store.sha, "case": NAME,
            "sourceSha256": "0" * 64, "attempt": 1, "kind": kind,
            "observation": reference, "verdict": verdict() if kind == "semantic" else None,
            "cliParity": cli() if kind == "semantic" else None,
            "failure": None if kind == "semantic" else {
                "kind": "worker-timeout", "phase": "worker-start", "message": "forced"},
            "resources": {"phases": {}, "childrenMaxRssPlatformUnits": 0}}


class ShardTests(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory()
        self.parent = Path(self.scratch.name).resolve() / "runs"
        self.store = shard.Store(self.parent, identity(), ADAPTER)

    def tearDown(self):
        self.store.close()
        self.scratch.cleanup()

    def complete(self):
        self.store.marker(NAME, 1, "terminal")
        reference = self.store.save_observation(NAME, observation())
        self.store.terminal(NAME, record(self.store, reference))
        return reference

    def test_identity_and_selection_are_exact(self):
        self.complete()
        for mutate in (lambda v: v["limits"].update(fuel=1),
                       lambda v: v["selection"][0].update(sha256="1" * 64),
                       lambda v: v.update(toolchain="different")):
            changed = identity()
            mutate(changed)
            self.assertNotEqual(shard.digest(changed), self.store.sha)
        records, _ = self.store.recover()
        result = shard.summary(self.store, records)
        self.assertEqual(result["terminalAttempts"], 1)
        self.assertEqual(result["alExecutedRelations"], 2)
        self.assertEqual(result["canonicalCounts"]["candidates"], 1267)
        self.assertTrue(result["okay"])
        self.store.write("run.json", inventory.encode({"bad": True}))
        self.store.close()
        with self.assertRaises(ValueError):
            shard.Store(self.parent, identity(), ADAPTER)
        # Restore a live descriptor for tearDown.
        (self.parent / self.store.sha / "run.json").write_bytes(inventory.encode(identity()))
        self.store = shard.Store(self.parent, identity(), ADAPTER)

    def test_resume_skips_only_valid_terminal_records(self):
        self.complete()
        with mock.patch.object(run, "bounded", side_effect=AssertionError("reran completed case")):
            result = shard.run_cases(self.store, Path("/probe"), Path("/upstream"),
                                     Path("/p4c"), Path("/spec"))
        self.assertTrue(result["okay"])
        self.assertEqual(result["terminalAttempts"], 1)
        marker = self.store.case_name(NAME, "started.json")
        self.store.write(marker, inventory.encode(shard.seal({
            "schemaVersion": 1, "identitySha256": self.store.sha, "case": NAME,
            "sourceSha256": "0" * 64, "attempt": 2, "phase": "terminal"})))
        with self.assertRaises(ValueError):
            self.store.recover()

    def test_record_mutations_fail_even_with_new_digest(self):
        reference = self.complete()
        original = record(self.store, reference)
        mutations = [lambda v: v.update(case="other"), lambda v: v.update(attempt=True),
                     lambda v: v["observation"].update(path="../outside"),
                     lambda v: v["observation"].update(rawBytes=1),
                     lambda v: v["observation"].update(rawSha256="1" * 64),
                     lambda v: v["verdict"]["relations"]["Program_ok"].update(status="syntax-only", leanClass="not-evaluated"),
                     lambda v: v["cliParity"]["Program_inst"].update(exit=-9),
                     lambda v: v.update(unexpected=True),
                     lambda v: v.update(failure={"kind": "timeout"}),
                     lambda v: v["resources"].update(childrenMaxRssPlatformUnits=True)]
        for index, mutate in enumerate(mutations):
            value = copy.deepcopy(original)
            mutate(value)
            with self.subTest(index=index), self.assertRaises(ValueError):
                self.store.validate_terminal(shard.seal(value), NAME)
        corrupt = shard.seal(original)
        corrupt["attempt"] = 2
        with self.assertRaises(ValueError):
            self.store.validate_terminal(corrupt, NAME)

    def test_corrupt_final_artifacts_never_retry(self):
        self.complete()
        path = self.store.case_name(NAME, "obs.json.gz")
        for content in (b"not gzip", gzip.compress(b'{}', mtime=0),
                        gzip.compress(b'{"x":1,"x":2}', mtime=0)):
            self.store.write(path, content)
            with self.assertRaises(ValueError):
                self.store.recover()
        self.store.write(path, gzip.compress(inventory.encode(observation()), mtime=0)[:-4])
        with self.assertRaises(ValueError):
            self.store.recover()
        self.store.write(path, gzip.compress(b"x" * 101, mtime=0))
        with mock.patch.object(run, "MAX_BYTES", 100), self.assertRaises(ValueError):
            self.store.recover()

    def test_crash_points_preserve_and_retry_unfinished(self):
        self.store.marker(NAME, 1, "artifact")
        artifact = self.store.case_name(NAME, "obs.json.gz")
        temporary = ".tmp." + "a" * 32 + "." + artifact
        (self.store.path / temporary).write_bytes(b"partial")
        records, attempts = self.store.recover()
        self.assertFalse(records)
        self.assertEqual(attempts[NAME], 2)
        self.assertIn("q.tmp." + "a" * 32 + "." + artifact, self.store.names())
        self.assertIn("q.1." + self.store.case_name(NAME, "started.json"), self.store.names())
        self.store.marker(NAME, 2, "artifact")
        self.store.save_observation(NAME, observation())
        _, attempts = self.store.recover()
        self.assertEqual(attempts[NAME], 3)
        self.assertIn("q.2." + artifact, self.store.names())
        self.store.marker(NAME, 3, "terminal")
        self.store.save_observation(NAME, observation())
        _, attempts = self.store.recover()
        self.assertEqual(attempts[NAME], 4)
        self.assertEqual(shard.summary(self.store, {})["terminalAttempts"], 0)

    def test_crash_between_quarantine_moves_recovers(self):
        self.store.marker(NAME, 1, "artifact")
        self.store.save_observation(NAME, observation())
        original = os.rename
        marker = self.store.case_name(NAME, "started.json")
        artifact = self.store.case_name(NAME, "obs.json.gz")
        def crash_marker(source, destination, **keywords):
            if source == marker:
                raise RuntimeError("injected crash between quarantine moves")
            return original(source, destination, **keywords)
        with mock.patch.object(os, "rename", side_effect=crash_marker), self.assertRaises(RuntimeError):
            self.store.recover()
        self.assertIn(marker, self.store.names())
        self.assertIn("q.1." + artifact, self.store.names())
        records, attempts = self.store.recover()
        self.assertFalse(records)
        self.assertEqual(attempts[NAME], 2)
        self.assertIn("q.1." + marker, self.store.names())

    def test_injected_atomic_write_crashes(self):
        self.store.marker(NAME, 1, "artifact")
        with mock.patch.object(os, "rename", side_effect=RuntimeError("before rename")), \
             self.assertRaises(RuntimeError):
            self.store.save_observation(NAME, observation())
        _, attempts = self.store.recover()
        self.assertEqual(attempts[NAME], 2)
        self.store.marker(NAME, 2, "artifact")
        original_sync = os.fsync
        def crash_parent(fd):
            if fd == self.store.fd:
                raise RuntimeError("after artifact rename")
            return original_sync(fd)
        with mock.patch.object(os, "fsync", side_effect=crash_parent), self.assertRaises(RuntimeError):
            self.store.save_observation(NAME, observation())
        _, attempts = self.store.recover()
        self.assertEqual(attempts[NAME], 3)
        self.assertIn("q.2." + self.store.case_name(NAME, "obs.json.gz"), self.store.names())

    def test_unknown_symlink_traversal_and_hardlink_rejected(self):
        for name in ("../../outside", "/outside", "unknown.json"):
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.store.read(name, 100)
        target = self.store.path / "summary.json"
        target.symlink_to(self.store.path / "run.json")
        with self.assertRaises(ValueError):
            self.store.scan()
        target.unlink()
        os.link(self.store.path / "run.json", target)
        with self.assertRaises(ValueError):
            self.store.scan()
        target.unlink()
        unknown = self.store.path / "unrecognized"
        unknown.write_bytes(b"data")
        with self.assertRaises(ValueError):
            self.store.recover()
        unknown.unlink()
        outer = Path(self.scratch.name) / "symlink-runs"
        outer.symlink_to(self.parent)
        with self.assertRaises(OSError):
            shard.Store(outer, identity(), ADAPTER)

    def test_lock_and_file_parent_fsync(self):
        with self.assertRaises(ValueError):
            shard.Store(self.parent, identity(), ADAPTER)
        original = os.fsync
        with mock.patch.object(os, "fsync", wraps=original) as sync:
            self.store.write("summary.json", b"{}")
        self.assertEqual(sync.call_count, 2)
        self.assertEqual(sync.call_args_list[-1].args[0], self.store.fd)

    def test_harness_union_is_terminal_not_match(self):
        self.store.marker(NAME, 1, "terminal")
        self.store.terminal(NAME, record(self.store, kind="harness"))
        records, _ = self.store.recover()
        result = shard.summary(self.store, records)
        self.assertTrue(result["complete"])
        self.assertFalse(result["okay"])
        self.assertEqual(result["relationStatuses"], {})
        self.assertEqual(result["alExecutedRelations"], 0)
        self.assertEqual(result["harnessFailures"], {"worker-timeout": 1})
        value = record(self.store, kind="harness")
        value["verdict"] = verdict()
        with self.assertRaises(ValueError):
            self.store.validate_terminal(shard.seal(value), NAME)
        value["verdict"] = None
        value["failure"]["kind"] = "silently-skip"
        with self.assertRaises(ValueError):
            self.store.validate_terminal(shard.seal(value), NAME)

    def test_actual_startup_failure_is_durable(self):
        sessions = {name: {**observation()["relations"][name], "boot": observation()["boot"]}
                    for name in contract.RELATIONS}
        values = [(0, inventory.encode(sessions[name]), b"", 0.1) for name in contract.RELATIONS]
        with mock.patch.object(run, "file_digest", return_value="0" * 64), \
             mock.patch.object(run, "bounded", side_effect=values), \
             mock.patch.object(run, "cli_parity", return_value=cli()):
            result = shard.run_cases(self.store, Path("/probe"), Path("/upstream"), Path("/p4c"),
                Path("/spec"), worker_factory=mock.Mock(side_effect=run.HarnessFailure(
                    "worker-timeout", "forced initialization failure")))
        self.assertFalse(result["okay"])
        records, _ = self.store.recover()
        self.assertEqual(records[NAME]["failure"]["phase"], "worker-start")
        self.assertEqual(records[NAME]["failure"]["kind"], "worker-timeout")
        self.assertIsNotNone(records[NAME]["observation"])

    def test_malformed_resume_has_durable_run_failure(self):
        self.complete()
        self.store.write(self.store.case_name(NAME, "obs.json.gz"), b"corrupt")
        with self.assertRaises(ValueError):
            shard.run_cases(self.store, Path("/probe"), Path("/upstream"), Path("/p4c"), Path("/spec"))
        failure = self.store.json("failure.json")
        self.assertIs(failure["complete"], False)
        self.assertEqual(failure["identitySha256"], self.store.sha)

    def test_worker_final_exit_failure_is_not_success(self):
        sessions = {name: {**observation()["relations"][name], "boot": observation()["boot"]}
                    for name in contract.RELATIONS}
        values = [(0, inventory.encode(sessions[name]), b"", 0.1) for name in contract.RELATIONS]
        worker = mock.Mock(cases=0, initialization_seconds=0.1)
        worker.case.return_value = verdict()
        worker.close.side_effect = [run.HarnessFailure("worker-crash", "exit -9 after last reply"), None]
        with mock.patch.object(run, "file_digest", return_value="0" * 64), \
             mock.patch.object(run, "bounded", side_effect=values), \
             mock.patch.object(run, "cli_parity", return_value=cli()), self.assertRaises(run.HarnessFailure):
            shard.run_cases(self.store, Path("/probe"), Path("/upstream"), Path("/p4c"), Path("/spec"),
                            worker_factory=lambda _: worker)
        records, _ = self.store.recover()
        result = shard.summary(self.store, records)
        self.assertFalse(result["okay"])
        self.assertEqual(result["runFailure"]["kind"], "worker-crash")


class CompileWorkspaceTests(unittest.TestCase):
    def test_outside_hardlink_alias_is_never_overwritten(self):
        adapter = run.load("compile_hardlink_test", inventory.ROOT / "scripts/export-p4-oracle.py")
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            adapter.SCRATCH = root / "workspaces"
            adapter.PROBE = inventory.ROOT / "test/p4-corpus/probe.ml"
            workspace = adapter.SCRATCH / ("c" * 64)
            workspace.mkdir(parents=True)
            outside = root / "outside"
            outside.write_bytes(b"outside alias must remain untouched")
            for name in ("probe.ml", "probe", "probe.o", "probe.cmi", "probe.cmx"):
                alias = workspace / name
                os.link(outside, alias)
                with self.subTest(name=name), mock.patch.object(adapter.subprocess, "run") as process:
                    process.return_value.returncode = 0
                    with self.assertRaisesRegex(SystemExit, "single-link regular"):
                        adapter.compile_probe(Path("/upstream"), "c" * 64)
                    self.assertEqual(process.call_count, 1)  # Rebuild only, never invoke compiler.
                    self.assertEqual(outside.read_bytes(), b"outside alias must remain untouched")
                alias.unlink()

    def test_special_entries_and_post_copy_revalidation(self):
        adapter = run.load("compile_special_test", inventory.ROOT / "scripts/export-p4-oracle.py")
        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch)
            adapter.SCRATCH = root / "workspaces"
            adapter.PROBE = inventory.ROOT / "test/p4-corpus/probe.ml"
            workspace = adapter.SCRATCH / ("d" * 64)
            workspace.mkdir(parents=True)
            special = workspace / "probe.o"
            for make, remove in ((lambda: special.mkdir(), lambda: special.rmdir()),
                                 (lambda: special.symlink_to(adapter.PROBE),
                                  lambda: special.unlink()),
                                 (lambda: os.mkfifo(special), lambda: special.unlink())):
                make()
                with mock.patch.object(adapter.subprocess, "run") as process:
                    process.return_value.returncode = 0
                    with self.assertRaisesRegex(SystemExit, "single-link regular"):
                        adapter.compile_probe(Path("/upstream"), "d" * 64)
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
                    adapter.compile_probe(Path("/upstream"), "d" * 64)
                self.assertEqual(process.call_count, 1)
                self.assertEqual(outside.read_bytes(), b"unchanged")

    def test_default_actual_pid_and_explicit_key(self):
        adapter = run.load("compile_workspace_test", inventory.ROOT / "scripts/export-p4-oracle.py")
        with tempfile.TemporaryDirectory() as scratch:
            adapter.SCRATCH = Path(scratch)
            adapter.PROBE = inventory.ROOT / "test/p4-corpus/probe.ml"
            with mock.patch.object(adapter.subprocess, "run") as process:
                process.return_value.returncode = 0
                default = adapter.compile_probe(Path("/upstream"))
                keyed = adapter.compile_probe(Path("/upstream"), "a" * 64)
            self.assertEqual(default, Path(scratch) / str(os.getpid()) / "probe")
            self.assertEqual(keyed, Path(scratch) / ("a" * 64) / "probe")
            commands = [call.args[0] for call in process.call_args_list]
            self.assertEqual(commands[0], ["dune", "build", "p4spec/bin/main.exe"])
            self.assertEqual(commands[1][-3:], [str(default.with_suffix(".ml")), "-o", str(default)])
            for key in ("../escape", "A" * 64, "0" * 63, 1, True):
                with self.subTest(key=key), self.assertRaises(SystemExit):
                    adapter.compile_probe(Path("/upstream"), key)
            (Path(scratch) / ("b" * 64)).symlink_to(Path(scratch) / ("a" * 64))
            with mock.patch.object(adapter.subprocess, "run") as process, self.assertRaises(SystemExit):
                process.return_value.returncode = 0
                adapter.compile_probe(Path("/upstream"), "b" * 64)


if __name__ == "__main__":
    unittest.main()
