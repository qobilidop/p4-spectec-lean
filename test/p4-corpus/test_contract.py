#!/usr/bin/env python3
"""Offline v2 envelope, worker-output and abnormal-process sensitivities."""

import copy
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest import mock

import contract
import inventory
import run
import sys


ADAPTER = run.load("p4_export_test", inventory.ROOT / "scripts/export-p4-oracle.py")


def fixture():
    pos = {"file": "", "line": 0, "column": 0}
    value = {"it": ["BoolV", True], "note": {"vid": 0, "typ": ["BoolT"], "vhash": 0},
             "at": {"left": pos, "right": pos}}
    runs = {name: {"relation": name, "mode": "AL", "cache": True, "det": False,
                   "guard": False, "counterBefore": 0, "counterAfterBoot": 0,
                   "counterAfter": 0, "typeFresh": {key: 0 for key in contract.PHASES},
                   "result": {"class": "pass", "outputs": [value]}}
            for name in contract.RELATIONS}
    return {"schemaVersion": 2, "name": "synthetic", "boot": value, "relations": runs}


class ContractTests(unittest.TestCase):
    def test_valid_and_nonzero_are_distinct(self):
        value = fixture()
        contract.validate_case(value, ADAPTER)
        self.assertFalse(contract.unsupported_type_fresh(value))
        value["relations"]["Program_ok"]["typeFresh"]["after"] = 1
        contract.validate_case(value, ADAPTER)
        self.assertTrue(contract.unsupported_type_fresh(value))

    def test_malformed_envelopes_fail(self):
        def rel(value):
            return value["relations"]["Program_ok"]
        mutations = [lambda v: v.update(schemaVersion=True),
                     lambda v: v.update(name=""),
                     lambda v: v.update(unexpected=0),
                     lambda v: v["relations"].pop("Program_inst"),
                     lambda v: rel(v).update(boot={}),
                     lambda v: rel(v).update(counterAfter=1 << 62),
                     lambda v: rel(v).update(counterAfter=True),
                     lambda v: rel(v).update(guard=True),
                     lambda v: rel(v)["typeFresh"].pop("after"),
                     lambda v: rel(v)["typeFresh"].update(after=True),
                     lambda v: rel(v)["typeFresh"].update(after=1 << 62),
                     lambda v: rel(v)["result"].update({"class": "unknown"}),
                     lambda v: v.update(boot={})]
        for index, mutate in enumerate(mutations):
            value = fixture()
            mutate(value)
            with self.subTest(index=index), self.assertRaises(ValueError):
                contract.validate_case(value, ADAPTER)

    def test_duplicate_and_nonjson_constants_fail(self):
        for data in (b'{"x":1,"x":2}', b'{"x":1,"\\u0078":2}', b'{"x":NaN}', b'\xff'):
            with self.subTest(data=data), self.assertRaises((ValueError, UnicodeDecodeError)):
                contract.strict_json(data)

    def test_worker_verdict_cannot_silently_pass(self):
        item = {"status": "matched", "leanClass": "pass", "message": ""}
        value = {"name": "x", "relations": {key: copy.deepcopy(item) for key in contract.RELATIONS}}
        run.verdict(value, "x")
        for mutate in (lambda v: v.update(name="wrong"),
                       lambda v: v["relations"]["Program_ok"].update(status="skipped"),
                       lambda v: v["relations"]["Program_ok"].update(leanClass="hard-error"),
                       lambda v: v["relations"].pop("Program_inst")):
            changed = copy.deepcopy(value)
            mutate(changed)
            with self.assertRaises(ValueError):
                run.verdict(changed, "x")

    def test_cli_signal_is_not_a_failure_verdict(self):
        value = fixture()
        for name in contract.RELATIONS:
            value["relations"][name]["result"] = {"class": "unmatch"}
        with mock.patch.object(run, "bounded", return_value=(-9, b"", b"crash", 0)):
            with self.assertRaises(run.HarnessFailure) as caught:
                run.cli_parity(inventory.ROOT, inventory.ROOT, inventory.ROOT / "case.p4", value)
        self.assertEqual(caught.exception.kind, "cli-parity")

    def test_bounded_subprocess_resources(self):
        with self.assertRaises(run.HarnessFailure) as caught:
            run.bounded([sys.executable, "-c", "import time; time.sleep(2)"], timeout=0.1)
        self.assertEqual(caught.exception.kind, "timeout")
        with self.assertRaises(run.HarnessFailure) as caught:
            run.bounded([sys.executable, "-c", "print('x'*10000)"], limit=100)
        self.assertEqual(caught.exception.kind, "oversized")

    def test_worker_init_failure_is_durable(self):
        manifest = json.loads(inventory.MANIFEST.read_text())
        real_check = run.load("check_init_test", inventory.ROOT / "test/p4-oracle/check.py")
        replay = run.load("replay_init_test", inventory.ROOT / "test/p4-oracle/replay.py")
        adapter = SimpleNamespace(revision_guard=lambda _: manifest["upstreamRevision"],
                                  compile_probe=lambda _: inventory.ROOT / "unused-probe")
        check = SimpleNamespace(load_export=lambda: adapter,
                                p4c_pin_guard=lambda *_: None,
                                EXPECTED_CASES=real_check.EXPECTED_CASES)
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            with mock.patch.object(run, "load", side_effect=[check, replay]), \
                 mock.patch.object(inventory, "build", return_value=manifest), \
                 mock.patch.object(run, "file_digest", return_value="0" * 64), \
                 mock.patch.object(run.subprocess, "run"), \
                 mock.patch.object(run, "Worker", side_effect=run.HarnessFailure(
                     "worker-timeout", "forced initialization failure")):
                with self.assertRaises(run.HarnessFailure):
                    run.pilot(inventory.ROOT, inventory.ROOT, directory)
            report = json.loads((directory / "report.json").read_text())
            self.assertIs(report["complete"], False)
            self.assertEqual(report["cases"], [])
            self.assertEqual(report["failure"]["kind"], "worker-timeout")


if __name__ == "__main__":
    unittest.main()
