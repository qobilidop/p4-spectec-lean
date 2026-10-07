#!/usr/bin/env python3
"""Offline contracts of the corpus sweep's accounting: nothing is dropped or relabelled."""

import gzip
import json
import sys
from pathlib import Path
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sweep


def record(ok, inst, lean="pass", seconds=1.0):
    return {"name": "case", "seconds": seconds, "relations": {
        "Program_ok": {"status": ok, "leanClass": lean, "message": ""},
        "Program_inst": {"status": inst, "leanClass": lean, "message": ""}}}


FAILED = {"name": "case", "seconds": 2.0,
          "failure": {"kind": "worker-timeout", "message": "worker exceeded deadline"}}


class SweepAccountingTest(unittest.TestCase):
    def test_agreement_requires_both_relations(self):
        self.assertTrue(sweep.agrees(record("matched", "matched")))
        self.assertTrue(sweep.agrees(record("matched-public-failure", "syntax-only")))
        self.assertTrue(sweep.agrees(record("matched-abort", "matched-abort", "hard-error")))
        for status in ("output-disagreement", "counter-disagreement", "outcome-disagreement",
                       "exhausted", "unrepresentable-input", "unsupported-type-fresh"):
            with self.subTest(status=status):
                self.assertFalse(sweep.agrees(record("matched", status)))
                self.assertFalse(sweep.agrees(record(status, "matched")))
        self.assertFalse(sweep.agrees(FAILED))

    def test_every_candidate_is_accounted_for(self):
        candidates = [{"path": f"p{i}"} for i in range(4)]
        unobserved = [{"name": "p3", "kind": "oversized", "message": "bound"}]
        legs = {"interpreter": {0: record("matched", "matched"), 1: FAILED,
                                2: record("matched", "exhausted", "exhausted")},
                "generated": {0: record("matched", "matched"), 1: record("matched", "matched"),
                              2: record("matched", "matched")}}
        summary = sweep.summarize(candidates, unobserved, legs)
        self.assertEqual(summary["candidates"], 4)
        interpreter = summary["legs"]["interpreter"]
        self.assertEqual(interpreter["agreeing"], 1)
        self.assertEqual(interpreter["statuses"], {
            "failure:worker-timeout": 1, "matched,exhausted": 1, "matched,matched": 1})
        self.assertEqual(len(interpreter["other"]), 2)
        self.assertEqual(summary["legs"]["generated"]["agreeing"], 3)
        self.assertEqual(sweep.verdict(summary, require_all=False), 1)

    def test_missing_record_is_rejected(self):
        candidates = [{"path": "p0"}, {"path": "p1"}]
        with self.assertRaises(ValueError):
            sweep.summarize(candidates, [], {"generated": {0: record("matched", "matched")}})

    def test_verdict(self):
        candidates = [{"path": "p0"}, {"path": "p1"}]
        clean = {"interpreter": {0: record("matched", "matched")},
                 "generated": {0: record("matched", "matched")}}
        unobserved = [{"name": "p1", "kind": "oversized", "message": "bound"}]
        summary = sweep.summarize(candidates, unobserved, clean)
        self.assertEqual(sweep.verdict(summary, require_all=False), 0)
        self.assertEqual(sweep.verdict(summary, require_all=True), 1)
        complete = sweep.summarize(candidates[:1], [], clean)
        self.assertEqual(sweep.verdict(complete, require_all=True), 0)

    def test_only_a_reached_bound_excuses_an_unobserved_candidate(self):
        candidates = [{"path": "p0"}, {"path": "p1"}]
        clean = {"generated": {0: record("matched", "matched")}}
        for kind in ("oracle-crash", "invalid-artifact", "harness-error"):
            with self.subTest(kind=kind):
                summary = sweep.summarize(
                    candidates, [{"name": "p1", "kind": kind, "message": ""}], clean)
                self.assertEqual(sweep.verdict(summary, require_all=False), 1)
        summary = sweep.summarize(
            candidates, [{"name": "p1", "kind": "timeout", "message": ""}], clean)
        self.assertEqual(sweep.verdict(summary, require_all=False), 0)

    def test_nothing_evaluated_is_not_a_pass(self):
        candidates = [{"path": "p0"}]
        summary = sweep.summarize(
            candidates, [{"name": "p0", "kind": "oversized", "message": ""}],
            {"interpreter": {}, "generated": {}})
        self.assertEqual(sweep.verdict(summary, require_all=False), 1)


class RegressionSetTest(unittest.TestCase):
    """The regression denominator is exactly upstream's three groups of programs."""

    def tree(self, scratch, files):
        upstream = Path(scratch)
        for group in sweep.REGRESSION_GROUPS:
            (upstream / sweep.REGRESSION / group).mkdir(parents=True)
        for name, text in files.items():
            (upstream / sweep.REGRESSION / name).write_text(text)
        return upstream

    def test_candidates_by_group_then_name_with_digests(self):
        with tempfile.TemporaryDirectory() as scratch:
            upstream = self.tree(scratch, {"sim/b.p4": "b", "sim/b.stf": "packet", "neg/z.p4": "z",
                                           "neg/a.p4": "a", "pos/m.p4": "m", "neg/notes.txt": "x"})
            cases = sweep.regression_candidates(upstream)
        prefix = f"upstream/{sweep.REGRESSION}/"
        self.assertEqual([case["path"] for case in cases],
                         [prefix + name for name in ("neg/a.p4", "neg/z.p4", "pos/m.p4",
                                                     "sim/b.p4")])
        self.assertEqual(cases[0]["sha256"],
                         "ca978112ca1bbdcafac231b39a23dc4da786eff8147c4e72b9807785afee48bb")
        self.assertTrue(all(set(case) == {"path", "sha256"} for case in cases))

    def test_malformed_trees_are_rejected(self):
        with tempfile.TemporaryDirectory() as scratch:
            upstream = self.tree(scratch, {})
            with self.assertRaises(ValueError):  # no program at all
                sweep.regression_candidates(upstream)
            (upstream / "outside.p4").write_text("o")
            (upstream / sweep.REGRESSION / "neg/link.p4").symlink_to(upstream / "outside.p4")
            with self.assertRaises(ValueError):
                sweep.regression_candidates(upstream)
        with tempfile.TemporaryDirectory() as scratch:
            upstream = self.tree(scratch, {"neg/a.p4": "a"})
            (upstream / sweep.REGRESSION / "sim").rmdir()
            with self.assertRaises(ValueError):
                sweep.regression_candidates(upstream)
        # upstream collects recursively: what this enumeration would skip is an error
        for extra in ("neg/nested", "fourth", "neg/directory.p4"):
            with self.subTest(extra=extra), tempfile.TemporaryDirectory() as scratch:
                upstream = self.tree(scratch, {"neg/a.p4": "a"})
                (upstream / sweep.REGRESSION / extra).mkdir()
                with self.assertRaises(ValueError):
                    sweep.regression_candidates(upstream)
        with tempfile.TemporaryDirectory() as scratch:
            upstream = self.tree(scratch, {"neg/a.p4": "a"})
            (upstream / sweep.REGRESSION / "stray.txt").write_text("x")
            with self.assertRaises(ValueError):
                sweep.regression_candidates(upstream)

    def test_source_resolves_only_the_known_roots(self):
        upstream, p4c = Path("/u"), Path("/c")
        self.assertEqual(sweep.source({"path": "p4c/testdata/a.p4"}, upstream, p4c),
                         Path("/c/testdata/a.p4"))
        self.assertEqual(sweep.source({"path": "upstream/testdata/a.p4"}, upstream, p4c),
                         Path("/u/testdata/a.p4"))
        for path in ("elsewhere/a.p4", "upstream", "upstream/../a.p4", "/etc/passwd",
                     "upstream//etc/passwd", "upstream/./a.p4", "p4c/a/"):
            with self.subTest(path=path):
                with self.assertRaises(ValueError):
                    sweep.source({"path": path}, upstream, p4c)

    def named(self, path, ok, inst, lean="pass"):
        return {**record(ok, inst, lean), "name": path}

    def test_groups_and_expected_outcomes(self):
        prefix = f"upstream/{sweep.REGRESSION}/"
        paths = [prefix + name for name in ("neg/a.p4", "neg/b.p4", "pos/c.p4", "sim/d.p4")]
        candidates = [{"path": path} for path in paths]
        rejected = "matched-public-failure"
        good = {0: self.named(paths[0], rejected, rejected, "unmatch"),
                1: self.named(paths[1], rejected, rejected, "hard-error"),
                2: self.named(paths[2], "matched", "matched"),
                3: self.named(paths[3], "matched", "matched")}
        legs = {"interpreter": dict(good), "generated": dict(good)}
        self.assertEqual(sweep.groups(candidates, legs)["interpreter"], {
            "neg": {f"{rejected}(hard-error),{rejected}(hard-error)": 1,
                    f"{rejected}(unmatch),{rejected}(unmatch)": 1},
            "pos": {"matched(pass),matched(pass)": 1},
            "sim": {"matched(pass),matched(pass)": 1}})
        self.assertEqual(sweep.unexpected(candidates, [], legs), [])
        # a `neg` program a leg accepts, though it could still agree with upstream
        legs["generated"][0] = self.named(paths[0], "matched", "matched")
        # a rejection on one relation only, an accepted program rejected, a failure record
        legs["interpreter"][1] = self.named(paths[1], rejected, "matched")
        legs["interpreter"][2] = self.named(paths[2], rejected, rejected, "unmatch")
        legs["interpreter"][3] = {**FAILED, "name": paths[3]}
        problems = sweep.unexpected(candidates, [], legs)
        self.assertEqual(len(problems), 4)
        self.assertTrue(any(p.startswith("generated: " + paths[0]) for p in problems))
        for index in (1, 2, 3):
            self.assertTrue(any(p.startswith("interpreter: " + paths[index]) for p in problems))
        self.assertEqual(sweep.groups(candidates, legs)["interpreter"]["sim"],
                         {"failure:worker-timeout": 1})

    def test_error_tests_are_rejected_by_typing_or_parsing(self):
        prefix = "p4c/testdata/p4_16_errors/"
        paths = [prefix + name for name in ("a.p4", "b.p4", "c.p4")]
        candidates = [{"path": path} for path in paths]
        rejected = "matched-public-failure"
        legs = {"generated": {0: self.named(paths[0], rejected, rejected, "unmatch"),
                              1: self.named(paths[1], "syntax-only", "syntax-only",
                                            "not-evaluated"),
                              2: self.named(paths[2], "matched-abort", "matched-abort",
                                            "hard-error")}}
        self.assertEqual(sweep.unexpected(candidates, [], legs), [])
        self.assertEqual(sweep.groups(candidates, legs)["generated"]["p4_16_errors"], {
            f"{rejected}(unmatch),{rejected}(unmatch)": 1,
            "matched-abort(hard-error),matched-abort(hard-error)": 1,
            "syntax-only(not-evaluated),syntax-only(not-evaluated)": 1})
        # an error test a leg accepts, or one it cannot evaluate, is not a rejection
        for statuses in (("matched", rejected), (rejected, "unsupported-type-fresh"),
                         ("exhausted", rejected), (rejected, "unrepresentable-input")):
            with self.subTest(statuses=statuses):
                legs["generated"][0] = self.named(paths[0], *statuses, "unmatch")
                problems = sweep.unexpected(candidates, [], legs)
                self.assertEqual(len(problems), 1)
                self.assertTrue(problems[0].startswith("generated: " + paths[0]))

    def test_unobserved_or_missing_candidates_are_unexpected(self):
        prefix = f"upstream/{sweep.REGRESSION}/"
        paths = [prefix + "neg/a.p4", prefix + "pos/b.p4"]
        candidates = [{"path": path} for path in paths]
        rejected = "matched-public-failure"
        records = {0: self.named(paths[0], rejected, rejected, "unmatch")}
        unobserved = [{"name": paths[1], "kind": "timeout", "message": ""}]
        # a reached bound excuses a p4c candidate; here every candidate must be observed
        self.assertEqual(sweep.unexpected(candidates, unobserved, {"generated": records}),
                         [f"{paths[1]}: unobserved (timeout)"])
        self.assertEqual(sweep.groups(candidates, {"generated": records})["generated"],
                         {"neg": {f"{rejected}(unmatch),{rejected}(unmatch)": 1}})
        self.assertEqual(sweep.unexpected(candidates, [], {"generated": records}),
                         [f"generated: {paths[1]}: no record"])
        self.assertEqual(sweep.unexpected(candidates, [], {}), ["no leg"])
        with self.assertRaises(ValueError):  # a record that is not its candidate
            sweep.groups(candidates, {"generated": {1: records[0]}})

    def test_identity_depends_on_the_candidates(self):
        with tempfile.TemporaryDirectory() as scratch:
            probe = Path(scratch) / "probe"
            probe.write_text("probe")
            one = sweep.identity(Path("/u"), Path("/c"), probe, 1, 2, [{"path": "a"}])
            two = sweep.identity(Path("/u"), Path("/c"), probe, 1, 2, [{"path": "b"}])
        self.assertNotEqual(one["candidatesSha256"], two["candidatesSha256"])
        self.assertEqual({key for key in one if one[key] != two[key]}, {"candidatesSha256"})


FAKE_WORKER = r'''
import json, sys, time
print(json.dumps({"ready": 2}), flush=True)
for line in sys.stdin:
    name = json.load(open(line.strip()))["name"]
    relation = {"status": "matched", "leanClass": "pass", "message": ""}
    answer = {"name": name, "relations": {"Program_ok": relation, "Program_inst": relation}}
    if name == "crash":
        sys.exit(3)
    if name == "hang":
        time.sleep(60)
    if name == "wrong-name":
        answer["name"] = "another case"
    if name == "error":
        answer = {"error": "case exceeds worker byte bound"}
    if name == "not-an-object":
        answer = [1]
    if name == "bad-status":
        answer["relations"]["Program_ok"] = {**relation, "status": "skipped"}
    print(json.dumps(answer), flush=True)
'''


class SweepWorkerTest(unittest.TestCase):
    """Every way a worker can fail leaves a failure record, and later cases still run."""

    def test_each_failure_is_a_record(self):
        names = ["ok-1", "crash", "ok-2", "hang", "wrong-name", "error", "not-an-object",
                 "bad-status", "ok-3"]
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            script = directory / "worker.py"
            script.write_text(FAKE_WORKER)
            observations = directory / "observations"
            observations.mkdir()
            for index, name in enumerate(names):
                (observations / f"{index:04d}.json.gz").write_bytes(
                    gzip.compress(json.dumps({"name": name}).encode()))
            (observations / "0009.json.gz").write_bytes(b"not gzip")
            records = sweep.run_leg("fake", [sys.executable, str(script)], observations,
                                    timeout=2, jobs=1)
        self.assertEqual(sorted(records), list(range(10)))
        outcome = {records[index]["name"]: records[index] for index in records}
        for name in ("ok-1", "ok-2", "ok-3"):
            self.assertTrue(sweep.agrees(outcome[name]), name)
        expected = {"crash": "worker-crash", "hang": "worker-timeout",
                    "wrong-name": "invalid-artifact", "error": "worker-error",
                    "not-an-object": "invalid-artifact", "bad-status": "invalid-artifact",
                    "0009.json.gz": "harness-error"}
        for name, kind in expected.items():
            with self.subTest(name=name):
                self.assertEqual(outcome[name]["failure"]["kind"], kind)
                self.assertFalse(sweep.agrees(outcome[name]))

    def test_workers_are_recycled(self):
        with tempfile.TemporaryDirectory() as scratch:
            directory = Path(scratch)
            script = directory / "worker.py"
            script.write_text(FAKE_WORKER)
            observations = directory / "observations"
            observations.mkdir()
            for index in range(5):
                (observations / f"{index:04d}.json.gz").write_bytes(
                    gzip.compress(json.dumps({"name": f"ok-{index}"}).encode()))
            records = sweep.run_leg("fake", [sys.executable, str(script)], observations,
                                    timeout=5, jobs=2, recycle=2)
        self.assertEqual(len(records), 5)
        self.assertTrue(all(sweep.agrees(record) for record in records.values()))


if __name__ == "__main__":
    unittest.main()
