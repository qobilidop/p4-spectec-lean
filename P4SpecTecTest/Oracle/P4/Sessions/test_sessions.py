#!/usr/bin/env python3
"""Offline contracts of the session sweep: upstream's pairing and exclusion rules, and an
accounting that drops nothing."""

import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import sessions


class PairingTest(unittest.TestCase):
    """`collect_test_pairs ARCH` as upstream's `Util.Test` defines it."""

    def test_matching_rules(self):
        self.assertTrue(sessions.p4_matches_stf("a.p4", "a.stf"))
        self.assertTrue(sessions.p4_matches_stf("d/a.p4", "d/a.stf"))
        self.assertTrue(sessions.p4_matches_stf("a.p4", "a/a_1.stf"))
        self.assertFalse(sessions.p4_matches_stf("a.p4", "b.stf"))
        self.assertFalse(sessions.p4_matches_stf("d/a.p4", "a.stf"))
        self.assertFalse(sessions.p4_matches_stf("a.p4", "d/a.stf"))

    def tree(self, scratch):
        p4c = Path(scratch) / "p4c"
        upstream = Path(scratch) / "upstream"
        samples = p4c / sessions.SAMPLES
        samples.mkdir(parents=True)
        (samples / "a.p4").write_text("#include <v1model.p4>\n")
        (samples / "a.stf").write_text("packet 0 00\n")
        (samples / "b.p4").write_text("#include <ebpf_model.p4>\n")
        (samples / "b.stf").write_text("packet 0 00\n")
        (samples / "c.p4").write_text('#include "v1model.p4"\n')
        (samples / "c.stf").write_text("packet 0 00\n")
        (samples / "d.p4").write_text("#include <v1model.p4>\n")
        (samples / "include").mkdir()
        (samples / "include/e.p4").write_text("#include <v1model.p4>\n")
        (samples / "include/e.stf").write_text("packet 0 00\n")
        (upstream / "excludes/static/p4c").mkdir(parents=True)
        (upstream / "excludes/dynamic/p4c").mkdir(parents=True)
        (upstream / "excludes/dynamic/p4c/x.exclude").write_text(
            "# a comment\np4c/testdata/p4_16_samples/c.stf\n")
        (upstream / sessions.ARCHES["v1model"]["patches"]).mkdir(parents=True)
        return p4c, upstream

    def test_pairs_follow_upstream(self):
        with tempfile.TemporaryDirectory() as scratch:
            p4c, upstream = self.tree(scratch)
            pairs = sessions.p4c_pairs(p4c, upstream, "v1model")
            self.assertEqual([(p["program"], p["stf"], p["excluded"]) for p in pairs], [
                ("p4c/testdata/p4_16_samples/a.p4", "p4c/testdata/p4_16_samples/a.stf", False),
                ("p4c/testdata/p4_16_samples/c.p4", "p4c/testdata/p4_16_samples/c.stf", True)])
            self.assertTrue(all(len(p["programSha256"]) == 64 for p in pairs))
            # The eBPF selection is by its own include lines, without a patch directory.
            self.assertEqual([p["stf"] for p in sessions.p4c_pairs(p4c, upstream, "ebpf")],
                             ["p4c/testdata/p4_16_samples/b.stf"])
            (upstream / sessions.ARCHES["v1model"]["patches"] / "a.stf").write_text("packet 0 00\n")
            with self.assertRaises(ValueError):
                sessions.p4c_pairs(p4c, upstream, "v1model")
            (upstream / sessions.ARCHES["v1model"]["patches"] / "b.stf").write_text("packet 0 00\n")
            self.assertEqual(len(sessions.p4c_pairs(p4c, upstream, "ebpf")), 1)

    def test_regression_pairs_need_both_files(self):
        with tempfile.TemporaryDirectory() as scratch:
            upstream = Path(scratch)
            sim = upstream / sessions.REGRESSION
            sim.mkdir(parents=True)
            (upstream / sessions.ARCHES["v1model"]["patches"]).mkdir(parents=True)
            (sim / "b.p4").write_text("p")
            (sim / "b.stf").write_text("s")
            (sim / "a.p4").write_text("p")
            (sim / "a.stf").write_text("s")
            pairs = sessions.regression_pairs(upstream, "v1model")
            self.assertEqual([p["stf"] for p in pairs],
                             ["upstream/testdata/regression/sim/a.stf",
                              "upstream/testdata/regression/sim/b.stf"])
            # Upstream runs the directory for v1model only; every program needs its STF;
            # a patched program is unsupported.
            self.assertEqual(sessions.regression_pairs(upstream, "ebpf"), [])
            (upstream / sessions.ARCHES["v1model"]["patches"] / "a.p4").write_text("p")
            with self.assertRaises(ValueError):
                sessions.regression_pairs(upstream, "v1model")
            (upstream / sessions.ARCHES["v1model"]["patches"] / "a.p4").unlink()
            (sim / "c.p4").write_text("p")
            with self.assertRaises(ValueError):
                sessions.regression_pairs(upstream, "v1model")

    def test_source_resolves_only_the_known_roots(self):
        self.assertEqual(sessions.source("p4c/testdata/a.p4", Path("/u"), Path("/c")),
                         Path("/c/testdata/a.p4"))
        for path in ("elsewhere/a.p4", "p4c/../a.p4", "upstream//a.p4"):
            with self.subTest(path=path), self.assertRaises(ValueError):
                sessions.source(path, Path("/u"), Path("/c"))


def record(name, interpreter="matched", generated="matched"):
    return {"name": name, "seconds": 1.0, "legs": {
        "interpreter": {"status": interpreter, "message": ""},
        "generated": {"status": generated, "message": ""}}}


class AccountingTest(unittest.TestCase):
    def test_every_candidate_is_accounted_for(self):
        candidates = [{"stf": f"s{i}"} for i in range(4)]
        unobserved = [{"name": "s3", "kind": "timeout", "message": ""}]
        records = {0: record("s0"), 1: record("s1", generated="packet-disagreement"),
                   2: {"name": "s2", "seconds": 2.0,
                       "failure": {"kind": "worker-timeout", "message": ""}}}
        summary = sessions.summarize(candidates, unobserved, records)
        self.assertEqual(summary["matched"], 1)
        self.assertEqual(summary["statuses"]["generated"],
                         {"failure:worker-timeout": 1, "matched": 1, "packet-disagreement": 1})
        self.assertEqual(len(summary["other"]), 2)
        self.assertEqual(sessions.verdict(summary), 1)
        clean = sessions.summarize(candidates[:1], [], {0: record("s0")})
        self.assertEqual(sessions.verdict(clean), 0)
        with self.assertRaises(ValueError):
            sessions.summarize(candidates, [], {0: record("s0")})
        self.assertEqual(sessions.verdict(sessions.summarize([], [], {})), 1)

    def test_upstream_failure_is_not_a_match(self):
        summary = sessions.summarize([{"stf": "s0"}], [],
                                     {0: record("s0", "upstream-runtimeFail", "upstream-runtimeFail")})
        self.assertEqual(summary["matched"], 0)
        self.assertEqual(sessions.verdict(summary), 1)

    def test_malformed_answers_are_rejected(self):
        good = {"legs": {"interpreter": {"status": "matched", "message": ""},
                         "generated": {"status": "matched", "message": ""}}}
        self.assertEqual(sessions.verdict_record(good, "s"), good["legs"])
        for bad in ({"legs": {"interpreter": good["legs"]["interpreter"]}},
                    {"legs": {**good["legs"], "generated": {"status": "skipped", "message": ""}}},
                    {"error": "x"}, [1]):
            with self.subTest(bad=json.dumps(bad)), self.assertRaises(ValueError):
                sessions.verdict_record(bad, "s")


if __name__ == "__main__":
    unittest.main()
