#!/usr/bin/env python3
"""Offline sensitivity checks for the full-P4 oracle's transport and fixtures."""

import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import types
import unittest
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]


def import_file(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


EXPORT = import_file("full_p4_export", ROOT / "scripts/export-p4-oracle.py")
CHECK = import_file("full_p4_check", ROOT / "test/p4-oracle/check.py")


def synthetic_value(text):
    return {"it": ["TextV", text], "note": {"vid": 0, "typ": [], "vhash": 0},
            "at": {"left": {"file": "/source/sample.p4", "line": 1, "column": 0},
                   "right": {"file": "/source/sample.p4", "line": 1, "column": 7}}}


def synthetic_run(relation, result, after):
    return {"relation": relation, "mode": "AL", "cache": True,
            "det": False, "guard": False, "counterBefore": 0,
            "counterAfterBoot": 0, "counterAfter": after,
            "boot": synthetic_value("program"),
            "result": result}


def synthetic_observation():
    first = synthetic_run("Program_ok", {"class": "pass", "outputs": [
        synthetic_value("FRESH__0")]}, 1)
    second = synthetic_run("Program_inst", {"class": "unmatch",
                                            "diagnostic": {"source": "interp",
                                                           "code": None,
                                                           "message": "bad program",
                                                           "region": "/source/sample.p4:1"}}, 2)
    return {"boot": first["boot"], "relations": {
        "Program_ok": {k: v for k, v in first.items() if k != "boot"},
        "Program_inst": {k: v for k, v in second.items() if k != "boot"}}}


class FixtureContract(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="p4-oracle-contract-")
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.upstream = self.base / "upstream"
        self.p4c = self.base / "p4c"
        self.fixture = self.base / "observed.json"
        self.observation = synthetic_observation()
        cases = json.loads(CHECK.FIXTURE.read_text(encoding="utf-8"))["cases"]
        sources = {"upstream": self.upstream, "p4c": self.p4c, "repo": ROOT}
        for case in cases:
            path = sources[case["source"]] / case["path"]
            if case["source"] != "repo":
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("fixture", encoding="utf-8")
        roots = [(self.upstream, "$UPSTREAM"), (self.p4c, "$P4C"),
                 (ROOT, "$REPO")]
        expected = CHECK.summarize(self.observation, roots)
        self.control = {"upstreamRevision": "pinned", "cases": [
            {"name": case["name"], "source": case["source"],
             "path": case["path"], "expected": copy.deepcopy(expected)}
            for case in cases]}
        self.fake_export = types.SimpleNamespace(
            revision_guard=lambda path: "pinned",
            compile_probe=lambda path: self.base / "fake-probe",
            observe=lambda *args: self.observation,
        )

    def run_check(self, fixture):
        self.fixture.write_text(json.dumps(fixture), encoding="utf-8")
        argv = ["check.py", "--upstream", str(self.upstream),
                "--p4c", str(self.p4c)]
        with mock.patch.object(CHECK, "FIXTURE", self.fixture), \
             mock.patch.object(CHECK, "load_export", return_value=self.fake_export), \
             mock.patch.object(CHECK, "p4c_pin_guard"), \
             mock.patch.object(CHECK, "check_cli"), \
             mock.patch.object(sys, "argv", argv):
            CHECK.main()

    def test_control(self):
        self.run_check(self.control)

    def test_corrupt_expected_fields_are_rejected(self):
        mutations = {
            "boot digest": ("bootSha256", "0" * 64),
            "output digest": ("relations", "outputSha256"),
            "output count": ("relations", "outputArity"),
            "fresh counter": ("relations", "counterAfter"),
            "failure class": ("relations", "class"),
            "failure diagnostic": ("relations", "diagnosticSha256"),
        }
        for name, (field, value) in mutations.items():
            with self.subTest(name=name):
                fixture = copy.deepcopy(self.control)
                expected = fixture["cases"][0]["expected"]
                if field == "bootSha256":
                    expected[field] = value
                elif value == "outputSha256":
                    expected["relations"]["Program_ok"]["outputsSha256"] = "0" * 64
                elif value == "outputArity":
                    expected["relations"]["Program_ok"]["outputArity"] = 0
                elif value == "counterAfter":
                    expected["relations"]["Program_ok"]["counterAfter"] = 99
                elif value == "class":
                    expected["relations"]["Program_inst"]["class"] = "abort"
                else:
                    expected["relations"]["Program_inst"]["diagnosticSha256"] = "0" * 64
                with self.assertRaisesRegex(SystemExit, "stale observation"):
                    self.run_check(fixture)

    def test_missing_duplicate_and_reordered_cases_are_rejected(self):
        for name in ("empty", "missing", "duplicate", "reordered",
                     "missing revision", "empty expected"):
            with self.subTest(name=name):
                fixture = copy.deepcopy(self.control)
                if name == "empty":
                    fixture["cases"] = []
                elif name == "missing":
                    fixture["cases"].pop()
                elif name == "duplicate":
                    fixture["cases"].append(copy.deepcopy(fixture["cases"][0]))
                elif name == "reordered":
                    fixture["cases"][0], fixture["cases"][1] = (
                        fixture["cases"][1], fixture["cases"][0])
                elif name == "missing revision":
                    del fixture["upstreamRevision"]
                else:
                    fixture["cases"][0]["expected"] = {}
                with self.assertRaises(SystemExit):
                    self.run_check(fixture)


class TransportContract(unittest.TestCase):
    def test_upstream_pin_and_patch_provenance(self):
        upstream = Path("/fake/upstream")
        status = "".join(f" M {path}\n" for path in EXPORT.PATCHED_FILES)
        good = ["160000 pin 0 upstream/p4-spectec\n", "pin\n",
                str(upstream) + "\n", b"expected patch\n", b"expected patch\n",
                status]
        with mock.patch.object(EXPORT.subprocess, "check_output",
                               side_effect=good):
            self.assertEqual(EXPORT.revision_guard(upstream), "pin")
        for name, index, replacement in (
                ("wrong pin", 0, "160000 other 0 upstream/p4-spectec\n"),
                ("dirty source", 4, b"unexpected source edit\n"),
                ("untracked source", 5, status + "?? p4spec/lib/extra.ml\n")):
            with self.subTest(name=name):
                answers = good.copy()
                answers[index] = replacement
                with mock.patch.object(EXPORT.subprocess, "check_output",
                                       side_effect=answers):
                    with self.assertRaises(SystemExit):
                        EXPORT.revision_guard(upstream)

    def test_failed_rebuild_stops_before_link(self):
        failed = types.SimpleNamespace(returncode=1)
        with mock.patch.object(EXPORT.subprocess, "run", return_value=failed) as run, \
             mock.patch.object(EXPORT.shutil, "copyfile") as copy:
            with self.assertRaisesRegex(SystemExit, "rebuild"):
                EXPORT.compile_probe(Path("/fake/upstream"))
        run.assert_called_once_with(["dune", "build", "p4spec/bin/main.exe"],
                                    cwd=Path("/fake/upstream"))
        copy.assert_not_called()

    def fake_observe(self, first, second):
        with mock.patch.object(EXPORT.subprocess, "check_output",
                               side_effect=[first, second]):
            return EXPORT.observe(Path("/fake/probe"), Path("/spec"),
                                  Path("/includes"), Path("/program.p4"))

    def test_malformed_probe_json_is_rejected(self):
        run = synthetic_run("Program_ok", {"class": "pass", "outputs": []}, 0)
        with self.assertRaises(ValueError):
            self.fake_observe("{", json.dumps(run))

    def test_different_boots_are_rejected(self):
        first = synthetic_run("Program_ok", {"class": "pass", "outputs": []}, 0)
        second = synthetic_run("Program_inst", {"class": "pass", "outputs": []}, 0)
        second["boot"]["it"][1] = "different"
        with self.assertRaises(SystemExit):
            self.fake_observe(json.dumps(first), json.dumps(second))

    def test_malformed_relation_object_is_rejected(self):
        first = synthetic_run("Program_ok", {"class": "pass", "outputs": []}, 0)
        second = synthetic_run("Program_inst", {"class": "pass", "outputs": []}, 0)
        mutations = {
            "missing outputs": lambda run: run["result"].pop("outputs"),
            "unknown class": lambda run: run["result"].update({"class": "unknown"}),
            "wrong relation": lambda run: run.update({"relation": "Program_ok"}),
            "wrong mode": lambda run: run.update({"mode": "SL"}),
            "wrong cache": lambda run: run.update({"cache": False}),
            "bad counter": lambda run: run.update({"counterAfter": "zero"}),
            "missing envelope": lambda run: run.pop("counterAfterBoot"),
            "syntax with boot": lambda run: run.update(
                {"result": {"class": "syntax", "diagnostic": {
                    "source": "p4", "code": None, "message": "bad",
                    "region": "source:1"}}}),
        }
        for name, mutate in mutations.items():
            with self.subTest(name=name):
                broken = copy.deepcopy(second)
                mutate(broken)
                with self.assertRaises(SystemExit):
                    self.fake_observe(json.dumps(first), json.dumps(broken))

    def test_path_normalization_does_not_change_payload(self):
        roots = [(Path("/checkout/p4c"), "$P4C")]
        source_region = {"at": {"left": {"file": "/checkout/p4c/a.p4",
                                          "line": 1, "column": 0},
                                "right": {"file": "/checkout/p4c/a.p4",
                                          "line": 1, "column": 1}}}
        value_a = {"it": ["TextV", "/checkout/p4c/a.p4"], **source_region}
        value_b = {"it": ["TextV", "$P4C/a.p4"], **source_region}
        self.assertNotEqual(CHECK.digest(value_a, roots), CHECK.digest(value_b, roots))

    def test_only_source_regions_are_portable(self):
        first = synthetic_value("literal")
        second = copy.deepcopy(first)
        for side in ("left", "right"):
            first["at"][side]["file"] = "/checkout-a/p4c/a.p4"
            second["at"][side]["file"] = "/checkout-b/p4c/a.p4"
        self.assertEqual(CHECK.digest(first, [(Path("/checkout-a/p4c"), "$P4C")]),
                         CHECK.digest(second, [(Path("/checkout-b/p4c"), "$P4C")]))

    def test_extern_json_region_shape_remains_semantic(self):
        roots = [(Path("/checkout/p4c"), "$P4C")]
        value_a = synthetic_value("unused")
        value_a["it"] = ["ExternV", {"at": {
            "left": {"file": "/checkout/p4c/a.p4", "line": 1, "column": 0},
            "right": {"file": "/checkout/p4c/a.p4", "line": 1, "column": 1}}}]
        value_b = copy.deepcopy(value_a)
        for side in ("left", "right"):
            value_b["it"][1]["at"][side]["file"] = "$P4C/a.p4"
        self.assertNotEqual(CHECK.digest(value_a, roots), CHECK.digest(value_b, roots))

    def test_negative_cli_crash_is_not_a_verdict(self):
        summary = {"relations": {"Program_ok": {"class": "unmatch"}}}
        crashed = types.SimpleNamespace(returncode=-9, stdout="", stderr="")
        with tempfile.TemporaryDirectory(prefix="p4-oracle-cli-") as temporary:
            upstream = Path(temporary)
            executable = upstream / "_build/default/p4spec/bin/main.exe"
            executable.parent.mkdir(parents=True)
            executable.write_text("stub", encoding="utf-8")
            with mock.patch.object(CHECK.subprocess, "run", return_value=crashed):
                with self.assertRaisesRegex(SystemExit, "CLI verdict differs"):
                    CHECK.check_cli(upstream, Path("/include"),
                                    Path("/program.p4"), summary)


if __name__ == "__main__":
    unittest.main()
