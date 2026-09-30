"""Fail-closed contracts for the cross-layer mutation runner."""

from collections import Counter
import json
import subprocess
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import mutations  # noqa: E402


def completed(code, stdout="", stderr=""):
    return subprocess.CompletedProcess([], code, stdout, stderr)


class MutationTests(unittest.TestCase):
    def test_anchors_fail_closed(self):
        for text, anchor, replacement in [("a", "b", "c"), ("aa", "a", "b"), ("a", "a", "a")]:
            with self.assertRaises(mutations.HarnessError):
                mutations.replace_once(text, anchor, replacement)
        with self.assertRaises(mutations.HarnessError):
            mutations.extract("xAyAz", "A", "z")
        with self.assertRaises(mutations.HarnessError):
            mutations.extract_declaration("def a\n\ndef a\n\n", "def a")

    def test_definition_copies_are_the_generated_text(self):
        baseline = mutations.definition("baseline")
        generated = mutations.LVALUE.read_text()
        self.assertIn(baseline.replace("Scratch.", "NanoP4Spec."), generated)
        self.assertEqual(baseline.count("Scratch."), 1)

    def test_ordering_only_reorders_alternatives(self):
        baseline = mutations.definition("baseline")
        ordering = mutations.definition("ordering")
        self.assertNotEqual(baseline, ordering)
        # the same statements, only regrouped between the alternatives' delimiters
        def statements(text):
            return Counter(line.strip().strip("()<|> ") for line in text.splitlines())
        self.assertEqual(statements(baseline), statements(ordering))
        self.assertLess(ordering.index("pure false"), ordering.index("is_nonTypeName"))

    def test_failure_kind_changes_one_guard(self):
        baseline = mutations.definition("baseline").splitlines()
        mutated = mutations.definition("failureKind").splitlines()
        changed = [(a, b) for a, b in zip(baseline, mutated) if a != b]
        self.assertEqual(len(baseline), len(mutated))
        self.assertEqual(len(changed), 1)
        self.assertIn("Eval.check", changed[0][0])
        self.assertIn("Eval.err?", changed[0][1])

    def test_quotation_mutations_change_only_their_quotation(self):
        baseline = mutations.quotations("baseline")
        constructor = mutations.quotations("constructor")
        self.assertNotIn('"DROP"', constructor)
        self.assertEqual(constructor, baseline.replace(mutations.DROP, ""))
        quotation = mutations.quotations("quotation")
        self.assertEqual(sum(a != b for a, b in zip(baseline.splitlines(),
                                                    quotation.splitlines())), 1)
        for case in ("constructor", "quotation"):
            self.assertEqual(mutations.definition(case), mutations.definition("baseline"))

    def test_probe_requires_exactly_the_expected_observation(self):
        good = "CROSS_LAYER:n:[false, true, true, true]\n"
        mutations.validate_probe("ordering", "n", completed(0, good))
        for result in (completed(1, good), completed(0, good, "noise"),
                       completed(0, good.replace(":n:", ":m:")),
                       completed(0, "CROSS_LAYER:n:[true, true, true, true]\n")):
            with self.assertRaises(mutations.HarnessError):
                mutations.validate_probe("ordering", "n", result)

    def test_proof_rejection_must_be_the_named_diagnosis(self):
        path = Path("/tmp/Proof.lean")
        source, start, end = mutations.proof_probe("ordering", "n")
        self.assertIn("«$mutation_expression_is_lvalue».refines_group", source)
        self.assertIn("(ExceptT.mk (Scratch.«$expression_is_lvalue» p0))", source)
        good = (f"{path}:{start + 5}:6: error: {mutations.REJECTION['ordering']}:case x\n"
                "PROOF_DONE:n\n")
        mutations.validate_proof("ordering", "n", completed(1, good), path, start, end)
        other = good.replace(mutations.REJECTION["ordering"],
                             mutations.REJECTION["failureKind"])
        outside = good.replace(f":{start + 5}:", f":{start - 1}:")
        for result in (completed(1, other), completed(1, outside), completed(0, good),
                       completed(1, good + "warning: x\n"), completed(1, good, "stderr"),
                       completed(1, good.replace("PROOF_DONE:n", ""))):
            with self.assertRaises(mutations.HarnessError):
                mutations.validate_proof("ordering", "n", result, path, start, end)
        with self.assertRaises(mutations.HarnessError):
            mutations.validate_proof("baseline", "n", completed(0, "PROOF_DONE:m"), path, 0, 1)

    def test_hinted_export_adds_one_valid_hint(self):
        def hints(value):
            if isinstance(value, dict):
                own = [value] if "hintid" in value else []
                return own + [h for v in value.values() for h in hints(v)]
            return [h for v in value for h in hints(v)] if isinstance(value, list) else []
        baseline = hints(json.loads(mutations.EXPORT.read_text()))
        mutated = hints(mutations.hinted_export())
        self.assertEqual(len(mutated), len(baseline) + 1)
        prints = [h for h in mutated if h["hintid"]["it"] == "print"]
        self.assertEqual([h["hintexp"]["it"] for h in prints], [["TextE", "drop"]])

    def test_print_mutation_requires_the_hint_diagnosis(self):
        ok = completed(0, "[quotes] 350 definitions match the decoded export\n"
                       "[quotes] decoded and compiled Nano print environments are empty\n")
        rejected = completed(1, "[quotes] 350 definitions match the decoded export\n",
                             "[quotes] decoded Nano print hints are nonempty; "
                             "revise the print contract\n")
        for mutant in (ok, completed(1, "", "[quotes] definitions differ\n"),
                       completed(1, "", rejected.stderr)):
            outcomes = iter([ok, mutant])
            with tempfile.TemporaryDirectory() as scratch, \
                    self.assertRaises(mutations.HarnessError):
                mutations.run_print(lambda *a, **k: next(outcomes), Path(scratch))
        outcomes = iter([ok, rejected])
        with tempfile.TemporaryDirectory() as scratch:
            mutations.run_print(lambda *a, **k: next(outcomes), Path(scratch))

    def test_timeouts_are_failures(self):
        def timeout(*args, **kwargs):
            raise subprocess.TimeoutExpired(args, 1)
        for case in ("ordering", "printProvenance"):
            with self.assertRaises(mutations.HarnessError):
                mutations.run_case(case, execute=timeout)


if __name__ == "__main__":
    unittest.main()
