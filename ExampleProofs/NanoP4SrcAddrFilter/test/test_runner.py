"""Fail-closed contracts for the source-address filter mutation runner."""

import subprocess
from pathlib import Path
import unittest

import run


def completed(code, stdout="", stderr=""):
    return subprocess.CompletedProcess([], code, stdout, stderr)


class RunnerTests(unittest.TestCase):
    def test_anchor_missing_duplicate_and_no_mutation(self):
        for text, anchor, replacement in [("a", "b", "c"), ("aa", "a", "b"), ("a", "a", "a")]:
            with self.assertRaises(run.HarnessError):
                run.replace_once(text, anchor, replacement)

    def test_extraction_requires_unique_boundaries(self):
        with self.assertRaises(run.HarnessError):
            run.extract("xAyAz", "A", "z")
        self.assertEqual(run.extract("xAyBz", "A", "B"), "Ay")

    def test_each_mutation_changes_its_probe(self):
        baseline = run.lean_probe("baseline", "nonce")
        for case in ("branch", "extern", "output"):
            probe = run.lean_probe(case, "nonce")
            self.assertNotEqual(probe, baseline)
            self.assertEqual(probe.count("theorem Probe."), 1)
        self.assertIn("bits.toList.reverse", run.lean_probe("extern", "nonce"))
        self.assertNotIn("bits.toList.reverse", baseline)
        self.assertEqual(baseline.count("theorem Probe."), 3)
        # the copied target drives the copied extern, never the library instance
        self.assertIn("@NanoP4Spec.NanoSwitch_drive.run Probe.externs", baseline)

    def test_identity_mutation_changes_one_entry(self):
        program = (run.ROOT / "ExampleProofs/NanoP4SrcAddrFilter/Program.lean").read_text()
        mutated = run.replace_once(program, run.ENTRY, run.ENTRY.replace("W 8 1", "W 8 5"))
        self.assertEqual(sum(a != b for a, b in zip(program, mutated)), 1)
        probe = run.identity_probe("nonce", mutated)
        self.assertIn("namespace ProbeIdentity", probe)
        self.assertNotIn("ExampleProofs.NanoP4SrcAddrFilter", probe)

    def test_baseline_requires_clean_success(self):
        path = Path("/tmp/Probe.lean")
        run.validate_lean("baseline", "n", completed(0, "PROBE_DONE:n\n"), path)
        for result in (completed(1, "PROBE_DONE:n"), completed(0, "PROBE_DONE:n", "noise"),
                       completed(0, "PROBE_DONE:m"), completed(0, "warning: x\nPROBE_DONE:n")):
            with self.assertRaises(run.HarnessError):
                run.validate_lean("baseline", "n", result, path)

    def test_rejection_requires_exactly_the_evaluation_failure(self):
        path = Path("/tmp/Probe.lean")
        good = f"{path}:9:2: error: lazy_eval: evaluated to\n  x\nPROBE_DONE:n\n"
        run.validate_lean("branch", "n", completed(1, good), path)
        unrelated = f"{path}:3:0: error: unknown identifier 'foo'\nPROBE_DONE:n\n"
        extra = good + f"{path}:12:0: error: lazy_eval: evaluated to\n"
        warned = good + "warning: unused variable\n"
        for result in (completed(1, unrelated), completed(1, extra), completed(1, warned),
                       completed(0, good), completed(1, good, "stderr"),
                       completed(1, good.replace("PROBE_DONE:n", ""))):
            with self.assertRaises(run.HarnessError):
                run.validate_lean("branch", "n", result, path)

    def test_timeouts_are_failures(self):
        def timeout(*args, **kwargs):
            raise subprocess.TimeoutExpired(args, 1)
        for case in ("branch", "identity"):
            with self.assertRaises(run.HarnessError):
                run.run_case(case, execute=timeout)


if __name__ == "__main__":
    unittest.main()
