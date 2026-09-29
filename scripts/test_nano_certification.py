#!/usr/bin/env python3
"""Completion inventory mutations must fail without granting proof evidence."""

import copy
import gzip
import importlib.util
import json
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
    representations = [{"id": name, "kind": kind, "source": "test.watsup", "claims": []}
                       for kind, name in (("type", "value"), ("externType", "object"))]
    coverage = {"schemaVersion": 3, "library": "NanoP4Spec",
                "input": "exports/nano-p4.al.json", "definitions": entries,
                "representations": representations, "profiles": []}
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

    def test_extern_initialization_and_identity_bindings(self):
        obligations = {o["id"]: o for o in self.manifest["obligations"]}
        self.assertIsNone(obligations["contract:extern"]["coverageClaim"])
        self.assertIsNone(obligations["profile:initialization"]["coverageClaim"])
        identity = obligations["profile:sourceIdentity"]
        self.assertIsNone(identity["coverageClaim"])
        self.assertIn("check-quotes", identity["checkedBy"])
        self.assertIn(identity, completion.outstanding(self.manifest, "core"))
        self.assertNotIn(identity, completion.outstanding(
            self.manifest, "core", verified={"profile:sourceIdentity"}))
        self.coverage["definitions"][3]["claims"] = [{
            "name": "NanoP4Spec.Externs.extern.invocations", "kind": "externContract",
            "direction": "abstractTwoWay", "expectedType": "True"}]
        self.coverage["profiles"] = [{
            "name": "NanoP4Spec.Environment.initialized", "kind": "initialization",
            "direction": "certificateEnvironment", "expectedType": "True"}]
        manifest = completion.build_manifest(self.source, self.coverage, [], {})
        obligations = {o["id"]: o for o in manifest["obligations"]}
        self.assertEqual(obligations["contract:extern"]["coverageClaim"],
                         "NanoP4Spec.Externs.extern.invocations")
        self.assertEqual(obligations["profile:initialization"]["coverageClaim"],
                         "NanoP4Spec.Environment.initialized")

    def test_domain_needs_every_component_for_callables_with_calls(self):
        claims = [("sourceEntry", "sourceInputsToTwoWay"),
                  ("producer", "sourceInputsToSourceOutput"),
                  ("callAdmission", "allCallArgumentCarriers")]
        relation = self.coverage["definitions"][1]
        for count in range(len(claims) + 1):
            relation["claims"] = [{"name": f"NanoP4Spec.R.{kind}", "kind": kind,
                                   "direction": direction, "expectedType": "True"}
                                  for kind, direction in claims[:count]]
            manifest = completion.build_manifest(self.source, self.coverage, [], {})
            domain = next(o for o in manifest["obligations"] if o["id"] == "domain:R")
            expected = "NanoP4Spec.R.sourceEntry" if count == len(claims) else None
            self.assertEqual(domain["coverageClaim"], expected)

    def test_domain_profiles_are_not_mixed(self):
        source = [("sourceEntry", "sourceInputsToTwoWay"),
                  ("producer", "sourceInputsToSourceOutput"),
                  ("callAdmission", "allCallArgumentCarriers")]
        runtime = [("sourceEntry", "runtimeInputsToTwoWay"),
                   ("producer", "runtimeInputsToRuntimeOutput"),
                   ("callAdmission", "runtimeCallArgumentCarriers")]
        relation = self.coverage["definitions"][1]

        def bound(claims):
            relation["claims"] = [{"name": f"NanoP4Spec.R.{kind}.{direction}", "kind": kind,
                                   "direction": direction, "expectedType": "True"}
                                  for kind, direction in claims]
            manifest = completion.build_manifest(self.source, self.coverage, [], {})
            return next(o for o in manifest["obligations"]
                        if o["id"] == "domain:R")["coverageClaim"]

        self.assertEqual(bound(runtime), "NanoP4Spec.R.sourceEntry.runtimeInputsToTwoWay")
        # one component from each profile is no complete evidence
        self.assertIsNone(bound(source[:2] + runtime[2:]))
        self.assertIsNone(bound(runtime[:2] + source[2:]))

    def test_target_and_replay_bindings_need_their_checks(self):
        manifest = completion.build_manifest(self.source, self.coverage,
                                             ["corpus:typing:a/b", "corpus:packet:a/b"], {})
        obligations = {o["id"]: o for o in manifest["obligations"]}
        for key in ("profile:composition", "profile:observations"):
            self.assertEqual(obligations[key]["coverageClaim"], completion.TARGET_CLAIMS[key])
            self.assertEqual(obligations[key]["checkedBy"], completion.TARGET_CHECKS)
        # The fixture's extern is not NanoSwitch's, so it has no concrete target claim.
        self.assertIsNone(obligations["target:extern"]["coverageClaim"])
        typing, packet = obligations["replay:corpus:typing:a/b"], obligations[
            "replay:corpus:packet:a/b"]
        self.assertEqual(typing["checkedBy"], completion.TYPING_REPLAY)
        self.assertEqual(packet["checkedBy"], completion.SESSION_REPLAY)
        missing = completion.outstanding(manifest, "target")
        for obligation in (obligations["profile:composition"], typing, packet):
            self.assertIn(obligation, missing)
        verified = {"profile:composition", typing["id"], packet["id"]}
        missing = completion.outstanding(manifest, "target", verified=verified)
        for obligation in (obligations["profile:composition"], typing, packet):
            self.assertNotIn(obligation, missing)
        # A verified id without its compiled claim is still missing.
        self.assertIn(obligations["target:extern"], completion.outstanding(
            manifest, "target", verified={"target:extern"}))

    def test_target_verification_requires_exact_claims(self):
        claims = set(completion.TARGET_CLAIMS.values()) | completion.TARGET_WITNESSES
        good = "".join(f"[target] claim {c}\n" for c in sorted(claims)) + \
            "[target] 4 claims checked; pinned print hints empty"
        with patch.object(completion, "run", return_value=good):
            verified = completion.target_verified(self.manifest)
        composition = next(o for o in self.manifest["obligations"]
                           if o["id"] == "profile:composition")
        self.assertIn(composition["id"], verified)
        self.assertNotIn("target:extern", verified)  # no compiled claim to verify
        for output in (good.replace("[target] claim NanoP4Target.referenceWitness\n", ""),
                       good + "\n[target] claim NanoP4Target.extra",
                       good.replace("pinned print hints empty", "")):
            with patch.object(completion, "run", return_value=output):
                with self.assertRaises(completion.CertificationError):
                    completion.target_verified(self.manifest)

    def test_replay_verification_needs_verdicts_and_both_legs(self):
        case = "corpus:typing:positive/free-pass"
        manifest = completion.build_manifest(self.source, self.coverage,
                                             [case, "corpus:typing:missing/none",
                                              "corpus:packet:positive/free-pass"], {})

        class Replay:
            agree = True

            @classmethod
            def agreeing_programs(cls, paths, expected):
                return set(paths) if cls.agree else set()

        class Sessions:
            @staticmethod
            def replay(lean):
                return ["corpus:packet:positive/free-pass"]

        helpers = {"nano_replay": Replay, "nano_session_check": Sessions}
        with patch.object(completion, "corpus_helper", lambda path, name: helpers[name]), \
                patch.object(completion, "run", return_value=""):
            verified = completion.replay_verified(manifest, None)
            self.assertEqual(verified, {f"replay:{case}",
                                        "replay:corpus:packet:positive/free-pass"})
            Replay.agree = False
            self.assertEqual(completion.replay_verified(manifest, None),
                             {"replay:corpus:packet:positive/free-pass"})

    def test_owned_n4_spans_core_and_target_but_not_release(self):
        missing = completion.outstanding(self.manifest, "target", owned="N4")
        stages = {o["stage"] for o in missing}
        self.assertTrue(stages <= {"core", "target"})
        self.assertIn("profile:printing", [o["id"] for o in missing])
        self.assertNotIn("profile:consumer", [o["id"] for o in missing])

    def test_owned_scope_excludes_later_owners_and_other_stages(self):
        owned = completion.outstanding(self.manifest, "core",
                                       verified={"profile:sourceIdentity"}, owned="N3")
        owners = {self.manifest["requirements"][o["requirement"]]["owner"] for o in owned}
        self.assertTrue(owners <= {"N0", "N1", "N2", "N3"})
        self.assertTrue(all(o["stage"] == "core" for o in owned))
        replay = [o for o in self.manifest["obligations"] if o["requirement"] == "replay"]
        self.assertTrue(replay)
        self.assertFalse(any(o in owned for o in replay))
        self.assertTrue(any(o["requirement"] == "forward" for o in owned))

    def test_typed_variable_omission_retains_type_domains(self):
        self.coverage["profiles"] = [{
            "name": "NanoP4Spec.SourceProfile.variablesIgnored", "kind": "sourceVariables",
            "direction": "typedOmissionPreservesInitialization", "expectedType": "True"}]
        manifest = completion.build_manifest(self.source, self.coverage, [], {})
        obligation = next(o for o in manifest["obligations"] if o["id"] == "variable:VarD:x")
        self.assertEqual(obligation["coverageClaim"],
                         "NanoP4Spec.SourceProfile.variablesIgnored")
        self.assertIn("profile:primitiveRepresentations", obligation["dependencies"])
        self.coverage["profiles"][0]["direction"] = "wrongDirection"
        manifest = completion.build_manifest(self.source, self.coverage, [], {})
        obligation = next(o for o in manifest["obligations"] if o["id"] == "variable:VarD:x")
        self.assertIsNone(obligation["coverageClaim"])

    def test_duplicate_profile_claim_is_rejected(self):
        evidence = {"name": "ignored", "kind": "sourceVariables",
                    "direction": "typedOmissionPreservesInitialization", "expectedType": "True"}
        self.coverage["profiles"] = [evidence, evidence]
        with self.assertRaisesRegex(completion.CertificationError, "duplicate required claim"):
            completion.build_manifest(self.source, self.coverage, [], {})

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

    def test_source_codec_binding_keeps_call_domain_separate(self):
        self.coverage["representations"][0]["claims"] = [{
            "name": "NanoP4Spec.value.codec", "kind": "representation",
            "direction": "sourceCodec", "expectedType": "True"}]
        manifest = completion.build_manifest(self.source, self.coverage, [], {})
        obligations = {o["id"]: o for o in manifest["obligations"]}
        self.assertEqual(obligations["representation:TypD:value"]["coverageClaim"],
                         "NanoP4Spec.value.codec")
        self.assertIsNone(obligations["domain:f"]["coverageClaim"])
        self.assertIsNone(obligations["profile:initialization"]["coverageClaim"])

    def test_type_inventory_mismatches_rejected(self):
        for change in (lambda entries: entries.pop(),
                       lambda entries: entries.append(copy.deepcopy(entries[0])),
                       lambda entries: entries[0].update(kind="externType"),
                       lambda entries: entries[0].update(source="other.watsup")):
            coverage = copy.deepcopy(self.coverage)
            change(coverage["representations"])
            with self.assertRaises(completion.CertificationError):
                completion.build_manifest(self.source, coverage, [], {})

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


def n2_fixture():
    """Bindings are synthetic; only the CLI's separate Lean checker can validate them."""
    with gzip.open(ROOT / "exports/nano-p4.al.json.gz", "rt", encoding="utf-8") as exported:
        source = json.load(exported)
    coverage = completion.read_json(ROOT / completion.COVERAGE)
    def claim(kind, direction):
        return {"name": f"Fixture.{kind}.{direction}", "kind": kind,
                "direction": direction, "expectedType": "True"}
    for entry in coverage["representations"]:
        entry["claims"] = [claim("representation", "sourceCodec")]
    for entry in coverage["definitions"]:
        entry["claims"] = [claim(kind, direction) for kind, direction in (
            ("refinement", "referenceToGenerated"), ("refinement", "generatedToReference"),
            ("runSoundness", "generatedSuccessToRelation"),
            ("sourceEntry", "sourceInputsToTwoWay"), ("sourceDomain", "sourceInputsAndOutput"),
            ("producer", "sourceInputsToSourceOutput"),
            ("callAdmission", "allCallArgumentCarriers"), ("builtinContract", "twoWayDispatch"))]
    coverage["profiles"] = [claim(kind, direction) for kind, direction in completion.N2_PROFILES]
    return source, coverage


class N2Tests(unittest.TestCase):
    def setUp(self):
        self.source, self.coverage = n2_fixture()

    def entry(self, name):
        return next(entry for entry in self.coverage["definitions"] if entry["id"] == name)

    def remove(self, name, kind, direction):
        entry = self.entry(name)
        entry["claims"] = [claim for claim in entry["claims"]
                           if (claim["kind"], claim["direction"]) != (kind, direction)]

    def test_exact_bound_scope_does_not_close_broader_stages(self):
        self.assertEqual(completion.n2_missing(self.source, self.coverage), [])
        self.assertEqual(len(completion.N2_CLOSURE), 30)
        manifest = completion.build_manifest(self.source, self.coverage, [], {})
        self.assertTrue(completion.outstanding(manifest, "core"))
        self.assertTrue(completion.outstanding(manifest, "target"))
        self.assertTrue(completion.outstanding(manifest, "all"))

    def test_every_actual_type_identity_requires_a_codec(self):
        expected = {d["it"][1]["it"] for d in self.source
                    if d["it"][0] in ("TypD", "ExternTypD")}
        self.assertEqual(expected, {entry["id"] for entry in self.coverage["representations"]})
        for entry in self.coverage["representations"]:
            saved = entry["claims"]
            entry["claims"] = []
            self.assertIn(f"{entry['kind'] == 'type' and 'TypD' or 'ExternTypD'}:{entry['id']}: "
                          "representation/sourceCodec",
                          completion.n2_missing(self.source, self.coverage))
            entry["claims"] = saved

    def test_same_count_different_type_identity_fails(self):
        self.coverage["representations"][0]["id"] = "unrelatedType"
        with self.assertRaises(completion.CertificationError):
            completion.n2_missing(self.source, self.coverage)

    def test_dropped_variable_is_not_an_omission_proof(self):
        self.source.pop(next(i for i, d in enumerate(self.source) if d["it"][0] == "VarD"))
        self.assertTrue(any("VarD inventory" in message
                            for message in completion.n2_missing(self.source, self.coverage)))

    def test_every_initialization_and_primitive_profile_is_required(self):
        for profile in list(self.coverage["profiles"]):
            self.coverage["profiles"].remove(profile)
            self.assertIn(f"profile: {profile['kind']}/{profile['direction']}",
                          completion.n2_missing(self.source, self.coverage))
            self.coverage["profiles"].append(profile)

    def test_every_actual_builtin_needs_domain_and_dispatch(self):
        names = [d["it"][1]["it"] for d in self.source if d["it"][0] == "BuiltinDecD"]
        self.assertEqual(len(names), 26)
        for name in names:
            for kind, direction in (("sourceDomain", "sourceInputsAndOutput"),
                                    ("builtinContract", "twoWayDispatch"),
                                    ("refinement", "referenceToGenerated"),
                                    ("refinement", "generatedToReference")):
                saved = list(self.entry(name)["claims"])
                self.remove(name, kind, direction)
                self.assertIn(f"{name}: {kind}/{direction}",
                              completion.n2_missing(self.source, self.coverage))
                self.entry(name)["claims"] = saved

    def test_reports_all_missing_components(self):
        for name, kind, direction in (
                ("exists_", "refinement", "generatedToReference"),
                ("Var_init", "producer", "sourceInputsToSourceOutput"),
                ("Var_init", "sourceEntry", "sourceInputsToTwoWay"),
                ("in_set", "sourceDomain", "sourceInputsAndOutput"),
                ("Type_eq", "runSoundness", "generatedSuccessToRelation")):
            self.remove(name, kind, direction)
        missing = completion.n2_missing(self.source, self.coverage)
        self.assertEqual(len(missing), 5)

    def test_output_preservation_does_not_discharge_intermediate_calls(self):
        for name in ("update_fieldValue", "add_var_e", "Var_init"):
            self.remove(name, "callAdmission", "allCallArgumentCarriers")
            self.entry(name)["claims"].append({"name": "Partial.projection", "expectedType": "True",
                "kind": "callAdmission", "direction": "sourceContextProjections"})
        missing = completion.n2_missing(self.source, self.coverage)
        self.assertEqual(len(missing), 3)
        self.assertTrue(all("fullSourceCallInputs" in message for message in missing))

    def test_precise_full_call_contracts_are_accepted(self):
        for name, direction in (("update_fieldValue", "sourceRecursiveSuffixes"),
                                ("add_var_e", "sourceContextCalls"),
                                ("Var_init", "sourceCallPrefixes")):
            for claim in self.entry(name)["claims"]:
                if claim["kind"] == "callAdmission":
                    claim["direction"] = direction
        self.assertEqual(completion.n2_missing(self.source, self.coverage), [])

    def test_output_free_relation_still_needs_checked_unit_producer(self):
        self.remove("Type_eq", "producer", "sourceInputsToSourceOutput")
        self.assertIn("Type_eq: producer/sourceInputsToSourceOutput",
                      completion.n2_missing(self.source, self.coverage))

    def test_removed_dependency_cannot_shrink_scope(self):
        self.entry("Var_init")["dependencies"] = []
        missing = completion.n2_missing(self.source, self.coverage)
        self.assertTrue(any("required N2 dependency closure" in message for message in missing))

    def test_new_dependency_does_not_silently_expand_checked_scope(self):
        self.entry("exists_")["dependencies"].append("Program_load")
        missing = completion.n2_missing(self.source, self.coverage)
        self.assertTrue(any("new N2 dependency" in message for message in missing))

    def test_known_kind_wrong_direction_is_missing(self):
        for claim in self.entry("find_map")["claims"]:
            if claim["kind"] == "sourceDomain":
                claim["direction"] = "representedInputsOnly"
        self.assertIn("find_map: sourceDomain/sourceInputsAndOutput",
                      completion.n2_missing(self.source, self.coverage))

    def test_n2_cli_rejects_changed_quoted_inputs_before_binding_check(self):
        fake_corpus = type("Corpus", (), {"check": staticmethod(lambda **_: [])})
        with patch.object(completion, "corpus_module", return_value=fake_corpus), \
                patch.object(completion, "source_identity", return_value={}), \
                patch.object(completion, "read_json", side_effect=[self.source, self.coverage]), \
                patch.object(completion, "check_stored"), \
                patch.object(Path, "read_text", return_value=""), \
                patch.object(completion, "run", side_effect=["", "", completion.CertificationError(
                    "quotation input type changed")]) as checked, \
                patch.object(completion, "n2_missing") as inspected:
            self.assertEqual(completion.main(["--require-n2"]), 1)
            self.assertEqual(checked.call_args_list[-1].args,
                             (completion.ROOT, ["lake", "exe", "check-quotes"]))
            inspected.assert_not_called()

    def test_n2_cli_never_skips_failed_compiled_checks(self):
        manifest = completion.build_manifest(self.source, self.coverage, [], {})
        fake_corpus = type("Corpus", (), {"check": staticmethod(lambda **_: [])})
        with patch.object(completion, "corpus_module", return_value=fake_corpus), \
                patch.object(completion, "source_identity", return_value={}), \
                patch.object(completion, "read_json", side_effect=[self.source, self.coverage]), \
                patch.object(completion, "check_stored"), \
                patch.object(Path, "read_text", return_value=completion.canonical(manifest)), \
                patch.object(completion, "run", side_effect=completion.CertificationError(
                    "compiled check failed")) as checked, \
                patch.object(completion, "n2_missing") as inspected:
            self.assertEqual(completion.main(["--require-n2"]), 1)
            checked.assert_called_once_with(completion.ROOT, [
                "lake", "exe", "p4spectec-gen", "exports/nano-p4.al.json", "--lib", "NanoP4Spec",
                "--runtime-extern", "value", "--check"])
            inspected.assert_not_called()


if __name__ == "__main__":
    unittest.main()
