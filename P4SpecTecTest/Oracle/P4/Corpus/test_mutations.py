#!/usr/bin/env python3
"""Offline contracts of the regression mutation suite: anchors, expectations, restoration."""

import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import campaign
import mutations


def observation(name, counter=26, classes=("pass", "pass")):
    runs = {}
    for relation, cls in zip(("Program_ok", "Program_inst"), classes):
        result = ({"class": "pass", "outputs": [{"it": ["BoolV", True]}]} if cls == "pass"
                  else {"class": cls, "diagnostic": {}})
        runs[relation] = {"counterAfterBoot": 0, "counterAfter": counter, "result": result}
    return {"schemaVersion": 2, "name": name, "boot": {}, "relations": runs}


class AnchorTest(unittest.TestCase):
    def test_replace_once_requires_a_unique_anchor(self):
        self.assertEqual(mutations.replace_once("a b a", "b", "c"), "a c a")
        for text in ("a a", "b"):
            with self.assertRaises(mutations.HarnessError):
                mutations.replace_once(text, "a", "c")
        with self.assertRaises(mutations.HarnessError):
            mutations.replace_once("a", "a", "a")

    def test_both_distinctness_checks_are_skipped(self):
        check = ("(P4Spec.«$distinct_» (τK := P4Spec.nameIR) «nameIR_f*»)\n"
                 "        let _ ← StateEval.liftEval (Eval.check tmp_%d)")
        text = "x\n" + check % 216 + "\ny\n" + check % 230 + "\n"
        mutated = mutations.skip_distinctness(text)
        self.assertEqual(mutated.count("(Eval.check true)"), 2)
        self.assertNotIn("tmp_", mutated)
        with self.assertRaises(mutations.HarnessError):
            mutations.skip_distinctness("x\n" + check % 216 + "\n")
        # another relation's distinctness check is not a record-expression check
        with self.assertRaises(mutations.HarnessError):
            mutations.skip_distinctness(text.replace("«nameIR_f*»", "«nameIR*»", 1))

    def test_code_rewrites_change_their_anchor_only(self):
        for case, (path, rewrite, leg) in mutations.CODE.items():
            with self.subTest(case=case):
                self.assertIn(leg, ("interpreter", "generated"))
                if not path.is_file():
                    continue  # the generated module exists only after generation
                original = path.read_text()
                mutated = rewrite(original)
                self.assertNotEqual(mutated, original)
                self.assertEqual(len(mutated.splitlines()), len(original.splitlines()))


class ObservationTest(unittest.TestCase):
    def test_each_observation_mutation_changes_both_relations(self):
        base = observation("sim/a.p4")
        counter = mutations.mutate_observation("observedCounter", base)
        self.assertEqual([r["counterAfter"] for r in counter["relations"].values()], [27, 27])
        output = mutations.mutate_observation("observedOutput", base)
        self.assertEqual([r["result"]["outputs"] for r in output["relations"].values()],
                         [[], []])
        rejected = mutations.mutate_observation("observedClass", base)
        self.assertEqual([r["result"]["class"] for r in rejected["relations"].values()],
                         ["unmatch", "unmatch"])
        self.assertEqual(base, observation("sim/a.p4"))  # copies, never the cache
        with self.assertRaises(mutations.HarnessError):
            mutations.mutate_observation("observedClass", observation("neg/b.p4", 0,
                                                                      ("unmatch", "unmatch")))
        with self.assertRaises(mutations.HarnessError):
            mutations.mutate_observation("generatedRecordFields", base)

    def test_fresh_expectation_is_every_allocating_program(self):
        observations = {0: observation("sim/a.p4", 26), 1: observation("pos/b.p4", 0),
                        2: observation("neg/c.p4", 6, ("unmatch", "unmatch"))}
        self.assertEqual(mutations.fresh_expectation(observations), {
            "sim/a.p4": ("counter-disagreement", "counter-disagreement"),
            "neg/c.p4": ("counter-disagreement", "counter-disagreement")})
        lopsided = observation("sim/d.p4", 26)
        lopsided["relations"]["Program_inst"]["counterAfter"] = 0
        with self.assertRaises(mutations.HarnessError):
            mutations.fresh_expectation({**observations, 3: lopsided})
        with self.assertRaises(mutations.HarnessError):
            mutations.fresh_expectation({0: observation("sim/a.p4", 26)})

    def test_concat_expectation_covers_accepted_and_allocating_programs(self):
        observations = {0: observation("sim/a.p4", 26), 1: observation("pos/b.p4", 0),
                        2: observation("neg/c.p4", 6, ("unmatch", "unmatch")),
                        3: observation("neg/d.p4", 0, ("unmatch", "unmatch"))}
        self.assertEqual(mutations.concat_expectation(observations), {
            "sim/a.p4": ("counter-disagreement", "counter-disagreement"),
            "pos/b.p4": ("outcome-disagreement", "outcome-disagreement"),
            "neg/c.p4": ("counter-disagreement", "counter-disagreement")})
        with self.assertRaises(mutations.HarnessError):
            mutations.concat_expectation({3: observations[3], 1: observations[1]})

    def test_every_case_has_an_expectation(self):
        observations = {0: observation(mutations.OBSERVED, 26),
                        1: observation(mutations.DUPLICATE, 0, ("unmatch", "unmatch")),
                        2: observation("sim/x.p4", 26)}
        for case in mutations.CASES:
            with self.subTest(case=case):
                expected = mutations.expectation(case, observations)
                self.assertTrue(expected)
                self.assertTrue(all(len(v) == 2 for v in expected.values()))


def record(name, ok="matched", inst="matched"):
    return {"name": name, "seconds": 1.0, "relations": {
        "Program_ok": {"status": ok, "leanClass": "pass", "message": ""},
        "Program_inst": {"status": inst, "leanClass": "pass", "message": ""}}}


class VerificationTest(unittest.TestCase):
    def test_changes_are_exactly_the_differing_programs(self):
        baseline = mutations.statuses({0: record("a"), 1: record("b"), 2: record("c")})
        mutated = mutations.statuses({0: record("a"), 1: record("b", inst="output-disagreement"),
                                      2: {"name": "c", "seconds": 1.0,
                                          "failure": {"kind": "worker-crash", "message": ""}}})
        self.assertEqual(mutations.changes(baseline, mutated),
                         {"b": ("matched", "output-disagreement"), "c": ("failure:worker-crash",)})
        with self.assertRaises(mutations.HarnessError):
            mutations.changes(baseline, mutations.statuses({0: record("a")}))
        mutations.verify("case", {"b": ("matched", "output-disagreement")},
                         {"b": ("matched", "output-disagreement")})
        for found in ({}, {"b": ("matched", "counter-disagreement")},
                      {"b": ("matched", "output-disagreement"), "a": ("matched", "matched")}):
            with self.assertRaises(mutations.HarnessError):
                mutations.verify("case", {"b": ("matched", "output-disagreement")}, found)


class FakeLegs:
    """Builds write a chosen worker digest; runs return chosen statuses."""

    def __init__(self, scratch, build_digests, run_results, fail_build=False):
        self.scratch = scratch
        self.build_digests = iter(build_digests)
        self.run_results = iter(run_results)
        self.fail_build = fail_build
        self.limit, self.jobs = 1, 1

    def executable(self, leg):
        return self.scratch / f"{leg}-worker"

    def build(self, leg, log):
        log.write_text("built\n")
        if self.fail_build:
            raise mutations.HarnessError("build failed")
        self.executable(leg).write_text(next(self.build_digests))

    def run(self, leg, directory):
        return next(self.run_results)


class RestorationTest(unittest.TestCase):
    def mutation(self, scratch):
        source = scratch / "source.lean"
        source.write_text("before\n")
        code = {"case": (source, lambda text: text.replace("before", "after"), "interpreter")}
        return source, code

    def test_source_and_worker_are_restored_after_a_rejection(self):
        with tempfile.TemporaryDirectory() as scratch:
            scratch = Path(scratch)
            source, code = self.mutation(scratch)
            legs = FakeLegs(scratch, ["mutant", "baseline"],
                            [{"a": ("matched", "output-disagreement")}])
            legs.executable("interpreter").write_text("baseline")
            digests = {"interpreter": campaign.file_digest(legs.executable("interpreter"))}
            leg, found = mutations.run_code_mutation(
                "case", legs, scratch, {"interpreter": {"a": ("matched", "matched")}}, digests,
                scratch, code)
            self.assertEqual((leg, found), ("interpreter", {"a": ("matched", "output-disagreement")}))
            self.assertEqual(source.read_text(), "before\n")
            self.assertEqual(legs.executable("interpreter").read_text(), "baseline")
            self.assertTrue((scratch / "case.build.log").is_file())
            self.assertTrue((scratch / "case.restore.log").is_file())

    def test_source_is_restored_when_the_build_fails(self):
        with tempfile.TemporaryDirectory() as scratch:
            scratch = Path(scratch)
            source, code = self.mutation(scratch)
            legs = FakeLegs(scratch, [], [], fail_build=True)
            legs.executable("interpreter").write_text("baseline")
            with self.assertRaises(mutations.HarnessError):
                mutations.run_code_mutation("case", legs, scratch, {}, {"interpreter": "x"},
                                            scratch, code)
            self.assertEqual(source.read_text(), "before\n")

    def test_unchanged_or_unrestored_worker_is_a_harness_failure(self):
        for build_digests in (["baseline", "baseline"], ["mutant", "other"]):
            with self.subTest(builds=build_digests), tempfile.TemporaryDirectory() as scratch:
                scratch = Path(scratch)
                source, code = self.mutation(scratch)
                legs = FakeLegs(scratch, build_digests, [{}])
                legs.executable("interpreter").write_text("baseline")
                digests = {"interpreter": campaign.file_digest(legs.executable("interpreter"))}
                with self.assertRaises(mutations.HarnessError):
                    mutations.run_code_mutation("case", legs, scratch, {"interpreter": {}},
                                                digests, scratch, code)
                self.assertEqual(source.read_text(), "before\n")


if __name__ == "__main__":
    unittest.main()
