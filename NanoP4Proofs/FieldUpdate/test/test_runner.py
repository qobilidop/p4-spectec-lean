"""Fail-closed contracts for the bounded mutation runner."""

import subprocess
from pathlib import Path
import unittest
from unittest.mock import patch

import run


class RunnerTests(unittest.TestCase):
    def test_anchor_missing_duplicate_and_no_mutation(self):
        for text, anchor, replacement in [("a", "b", "c"), ("aa", "a", "b"),
                                          ("a", "a", "a")]:
            with self.assertRaises(run.HarnessError):
                run.replace_once(text, anchor, replacement)

    def test_each_mutation_applies(self):
        baseline = run.probe("baseline", "nonce")
        for case in run.CASES[1:]:
            self.assertNotEqual(baseline, run.probe(case, "nonce"))

    def test_semantic_reports(self):
        for case, report in [("baseline", "true:true:true"),
                             ("behavior", "true:false:true"),
                             ("quotation", "false:true:true"),
                             ("representation", "true:true:false")]:
            run.validate(case, "fresh", 0, "FIELD_UPDATE:fresh:" + report + "\n", "")

    def test_unrelated_errors_stale_reports_and_baseline_failure(self):
        outcomes = [(1, "FIELD_UPDATE:fresh:true:false:true", ""),
                    (0, "FIELD_UPDATE:fresh:true:false:true", "unrelated error"),
                    (0, "FIELD_UPDATE:stale:true:false:true", ""),
                    (0, "FIELD_UPDATE:fresh:true:false:true\nextra", "")]
        for code, stdout, stderr in outcomes:
            with self.assertRaises(run.HarnessError):
                run.validate("behavior", "fresh", code, stdout, stderr)
        with self.assertRaises(run.HarnessError):
            run.validate("baseline", "fresh", 0, "FIELD_UPDATE:fresh:false:true:true", "")

    def test_runtime_and_proof_timeouts_are_failures(self):
        reports = {"baseline": "true:true:true", "behavior": "true:false:true",
                   "quotation": "false:true:true", "representation": "true:true:false"}
        for case in run.CASES:
            for phase in ("probe", "proof"):
                with self.subTest(case=case, phase=phase):
                    limits = []

                    def execute(args, **kwargs):
                        limits.append(kwargs["timeout"])
                        if phase == "probe" or "--run" not in args:
                            raise subprocess.TimeoutExpired(args, kwargs["timeout"])
                        return subprocess.CompletedProcess(args, 0,
                            "FIELD_UPDATE:fresh:" + reports[case], "")

                    limit = 60 if phase == "probe" else 300
                    with patch.object(run.uuid, "uuid4") as nonce:
                        nonce.return_value.hex = "fresh"
                        with self.assertRaisesRegex(run.HarnessError,
                                f"{case}: {phase} timed out after {limit}s"):
                            run.run_case(case, execute=execute)
                    self.assertEqual(limits, [60] if phase == "probe" else [60, 300])

    def test_phase_timeouts_can_be_overridden(self):
        limits = []

        def execute(args, **kwargs):
            limits.append(kwargs["timeout"])
            output = ("FIELD_UPDATE:fresh:true:true:true" if "--run" in args else
                      "PROOF_SUCCESS:fresh")
            return subprocess.CompletedProcess(args, 0, output, "")

        with patch.object(run.uuid, "uuid4") as nonce:
            nonce.return_value.hex = "fresh"
            result = run.run_case("baseline", execute=execute, probe_timeout=1, proof_timeout=2)
        self.assertEqual(limits, [1, 2])
        self.assertTrue(result["accepted"])

    def test_proof_rejection_is_at_intended_boundary(self):
        path = Path("/scratch/Probe.lean")
        output = f"{path}:20:3: error: refine_al: values not related:\nPROOF_SUCCESS:fresh\n"
        result = subprocess.CompletedProcess([], 1, output, "")
        run.validate_proof("behavior", "fresh", result, path, 10, 30)
        for changed in [output.replace("20:3", "2:3"),
                        output.replace("refine_al: values not related:", "unknown identifier"),
                        output.replace("fresh", "stale"),
                        output + f"{path}:20:3: warning: declaration uses sorry\n"]:
            with self.assertRaises(run.HarnessError):
                run.validate_proof("behavior", "fresh",
                    subprocess.CompletedProcess([], 1, changed, ""), path, 10, 30)
        with self.assertRaises(run.HarnessError):
            run.validate_proof("baseline", "fresh", result, path, 10, 30)

    def test_missing_mutation_is_failure(self):
        with self.assertRaises(run.HarnessError):
            run.validate("behavior", "fresh", 0, "FIELD_UPDATE:fresh:true:true:true", "")
        with self.assertRaises(run.HarnessError):
            run.validate_proof("behavior", "fresh", subprocess.CompletedProcess(
                [], 0, "PROOF_SUCCESS:fresh", ""), Path("/scratch/Probe.lean"), 10, 30)

    def test_baseline_failure_stops_mutations(self):
        with patch.object(run, "run_case", side_effect=run.HarnessError("baseline failed")) as call:
            self.assertEqual(run.main(), 1)
            call.assert_called_once_with("baseline")


if __name__ == "__main__":
    unittest.main()
