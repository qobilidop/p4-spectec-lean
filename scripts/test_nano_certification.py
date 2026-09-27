#!/usr/bin/env python3
"""Completion inventory mutations must fail without granting proof evidence."""

import copy
import importlib.util
from pathlib import Path
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("nano_completion", ROOT / "scripts/nano-certification.py")
completion = importlib.util.module_from_spec(spec)
spec.loader.exec_module(completion)


def declaration(kind, name):
    return {"it": [kind, {"it": name}], "at": {"left": {"file": "test.watsup", "line": 1}}}


def fixture():
    source = [declaration("TypD", "value"), declaration("ExternTypD", "object"),
              declaration("VarD", "x"), declaration("FuncDecD", "f"),
              declaration("RelD", "R"), declaration("BuiltinDecD", "builtin"),
              declaration("ExternRelD", "extern")]
    entries = []
    for kind, name in (("function", "f"), ("relation", "R"), ("builtin", "builtin"),
                       ("externRelation", "extern")):
        entries.append({"id": name, "kind": kind, "source": "test.watsup", "group": [name],
                        "dependencies": ["f", "builtin", "extern"] if name == "R" else [],
                        "claims": [], "exclusions": []})
    entries[0]["claims"] = [{"name": "NanoP4Spec.f.refines", "kind": "refinement",
                              "direction": "referenceToGenerated", "expectedType": "True"}]
    entries[1]["claims"] = [{"name": "NanoP4Spec.R.run_sound", "kind": "runSoundness",
                              "direction": "generatedSuccessToRelation", "expectedType": "True"}]
    coverage = {"schemaVersion": 1, "library": "NanoP4Spec",
                "input": "exports/nano-p4.al.json", "definitions": entries}
    return source, coverage


class CompletionTests(unittest.TestCase):
    def setUp(self):
        self.source, self.coverage = fixture()
        self.manifest = completion.build_manifest(self.source, self.coverage,
                                                   ["corpus:typing:one", "corpus:packet:one"],
                                                   {"exportSha256": "original"})

    def reject_changed(self, change):
        modified = copy.deepcopy(self.manifest)
        change(modified)
        with self.assertRaisesRegex(completion.CertificationError, "differs from current"):
            completion.check_stored(completion.canonical(modified), self.manifest)

    def test_all_source_kinds_and_reference_only_bindings(self):
        self.assertEqual(len(self.manifest["declarations"]), 7)
        obligations = {o["id"]: o for o in self.manifest["obligations"]}
        self.assertIn("representation:TypD:value", obligations)
        self.assertIn("representation:ExternTypD:object", obligations)
        self.assertIn("variable:VarD:x", obligations)
        self.assertEqual(obligations["forward:f"]["coverageClaim"], "NanoP4Spec.f.refines")
        self.assertIsNone(obligations["reverse:f"]["coverageClaim"])
        self.assertEqual(obligations["soundness:R"]["coverageClaim"], "NanoP4Spec.R.run_sound")
        self.assertIn("contract:extern", obligations["reverse:R"]["dependencies"])

    def test_reverse_binding_keeps_independent_domain_obligations(self):
        self.coverage["definitions"][0]["claims"].append({
            "name": "NanoP4Spec.f.realizes", "kind": "refinement",
            "direction": "generatedToReference", "expectedType": "True"})
        manifest = completion.build_manifest(self.source, self.coverage, [], {})
        obligations = {o["id"]: o for o in manifest["obligations"]}
        self.assertEqual(obligations["reverse:f"]["coverageClaim"], "NanoP4Spec.f.realizes")
        self.assertEqual(obligations["forward:f"]["coverageClaim"], "NanoP4Spec.f.refines")
        self.assertIn("domain:f", obligations["reverse:f"]["dependencies"])
        self.assertIsNone(obligations["domain:f"]["coverageClaim"])
        self.assertIn("profile:initialization", obligations["reverse:f"]["dependencies"])
        self.assertTrue(completion.outstanding(manifest, "core"))

    def test_builtin_binding_requires_its_dispatch_contract(self):
        entry = self.coverage["definitions"][2]
        entry["claims"] = [{"name": "NanoP4Spec.builtin.refines", "kind": "refinement",
                            "direction": "referenceToGenerated", "expectedType": "True"}]
        manifest = completion.build_manifest(self.source, self.coverage, [], {})
        contract = next(o for o in manifest["obligations"] if o["id"] == "contract:builtin")
        self.assertIsNone(contract["coverageClaim"])
        entry["claims"].append({"name": "NanoP4Spec.builtin.dispatch", "kind": "builtinContract",
                                "direction": "twoWayDispatch", "expectedType": "True"})
        manifest = completion.build_manifest(self.source, self.coverage, [], {})
        obligations = {o["id"]: o for o in manifest["obligations"]}
        self.assertEqual(obligations["contract:builtin"]["coverageClaim"],
                         "NanoP4Spec.builtin.dispatch")
        self.assertEqual(obligations["contract:builtin"]["dependencies"], ["domain:builtin"])
        self.assertIsNone(obligations["domain:builtin"]["coverageClaim"])
        self.assertTrue(completion.outstanding(manifest, "core"))

    def test_missing_source_type(self):
        self.reject_changed(lambda m: m["declarations"].pop(0))

    def test_removed_obligation(self):
        self.reject_changed(lambda m: m["obligations"].pop(0))

    def test_removed_corpus_case(self):
        self.reject_changed(lambda m: m["obligations"].remove(next(
            o for o in m["obligations"] if o["id"] == "replay:corpus:packet:one")))

    def test_forged_theorem(self):
        self.reject_changed(lambda m: m["obligations"][0].update(coverageClaim="True.intro"))

    def test_forged_discharge_bit(self):
        self.reject_changed(lambda m: m["obligations"][0].update(checked=True))

    def test_stale_identity(self):
        self.reject_changed(lambda m: m["identity"].update(exportSha256="stale"))

    def test_weakened_expected_evidence(self):
        self.reject_changed(lambda m: m["requirements"]["reverse"].update(expectedEvidence="True"))

    def test_omitted_callable_is_not_an_exclusion(self):
        self.coverage["definitions"].pop(1)
        with self.assertRaisesRegex(completion.CertificationError, "missing/mismatched"):
            completion.build_manifest(self.source, self.coverage, [], {})

    def test_unknown_dependency(self):
        self.coverage["definitions"][0]["dependencies"] = ["missing"]
        with self.assertRaisesRegex(completion.CertificationError, "unknown coverage dependency"):
            completion.build_manifest(self.source, self.coverage, [], {})

    def test_duplicate_source_identity(self):
        with self.assertRaisesRegex(completion.CertificationError, "duplicate source"):
            completion.build_manifest(self.source + self.source[:1], self.coverage, [], {})

    def test_boolean_schema_is_not_version_one(self):
        self.coverage["schemaVersion"] = True
        with self.assertRaisesRegex(completion.CertificationError, "unsupported source or coverage"):
            completion.build_manifest(self.source, self.coverage, [], {})

    def test_every_stage_remains_incomplete(self):
        for stage in ("core", "target", "all"):
            self.assertTrue(completion.outstanding(self.manifest, stage))
        core = completion.outstanding(self.manifest, "core")
        self.assertTrue(all(o["stage"] == "core" for o in core))
        self.assertIn("replay:corpus:typing:one", [o["id"] for o in core])
        self.assertNotIn("replay:corpus:packet:one", [o["id"] for o in core])
        self.assertIn("profile:consumer", [o["id"] for o in completion.outstanding(self.manifest)])

    def test_type_dependencies_include_source_notes(self):
        self.source[3]["note"] = {"it": ["VarT", {"it": "value"}, []]}
        manifest = completion.build_manifest(self.source, self.coverage, [], {})
        domain = next(o for o in manifest["obligations"] if o["id"] == "domain:f")
        self.assertIn("representation:TypD:value", domain["dependencies"])
        self.assertIn("profile:primitiveRepresentations", domain["dependencies"])

    def test_prerequisite_failure_is_not_incompleteness_or_success(self):
        result = completion.subprocess.CompletedProcess(["lake"], 9, "", "proof failed")
        with patch.object(completion.subprocess, "run", return_value=result):
            with self.assertRaisesRegex(completion.CertificationError, "prerequisite failed.*9"):
                completion.run(ROOT, ["lake", "exe", "check-coverage"])


if __name__ == "__main__":
    unittest.main()
