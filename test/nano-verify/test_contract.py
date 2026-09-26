#!/usr/bin/env python3
"""Offline verify-oracle contract sensitivities, not upstream execution."""

import copy
import unittest
import contract


class Contract(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.bundle, cls.requests = contract.read()

    def test_current(self):
        contract.validate(self.bundle, self.requests)

    def test_pins_and_scope(self):
        for key in ("upstreamRevision", "nanoSpecRevision", "scope"):
            bad = {**self.bundle, key: "wrong"}
            with self.subTest(key=key), self.assertRaises(ValueError):
                contract.validate(bad, self.requests)

    def test_request_identity(self):
        with self.assertRaises(ValueError):
            contract.validate(self.bundle, list(reversed(self.requests)))

    def test_counter(self):
        for counter in (True, 1, 3):
            bad = copy.deepcopy(self.bundle)
            bad["cases"][0]["result"]["counterAfter"] = counter
            with self.subTest(counter=counter), self.assertRaises(ValueError):
                contract.validate(bad, self.requests)

    def test_callback_and_outputs(self):
        for key, value in (("calls", []), ("outputs", []), ("class", "skipped")):
            bad = copy.deepcopy(self.bundle)
            bad["cases"][0]["result"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                contract.validate(bad, self.requests)

    def test_reachability(self):
        for key, value in (("guard", True), ("guard", 0), ("fullP4GetterAgainstNano", "pass"),
                           ("counterAfter", True), ("counterBefore", 1),
                           ("externRelations", ["ExternFunctionCall_eval"])):
            bad = copy.deepcopy(self.bundle)
            bad["nanoReachability"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                contract.validate(bad, self.requests)

    def test_strict_json(self):
        for raw in ('{"a":1,"a":2}', '{"a":NaN}'):
            with self.assertRaises(ValueError):
                contract.strict(raw)


if __name__ == "__main__":
    unittest.main()
