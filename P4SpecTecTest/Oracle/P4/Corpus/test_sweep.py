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
        for status in ("output-disagreement", "counter-disagreement", "outcome-disagreement",
                       "exhausted", "unrepresentable-input", "unsupported-type-fresh",
                       "unsupported-upstream-abort"):
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
