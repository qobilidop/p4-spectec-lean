#!/usr/bin/env python3
"""Inventory Nano completion obligations; JSON is never a validation verdict.

The source census includes declarations omitted by callable coverage. Compiled
proof evidence is delegated to the existing Lean coverage checker. New contract
kinds stay unresolved until their semantic statement and checker are implemented.
"""

import argparse
import hashlib
import importlib.util
import json
import re
from pathlib import Path
import subprocess
import sys

from oracle_paths import source_path


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = Path("NanoP4Spec/completion.json")
EXPORT = Path("exports/nano-p4.al.json")
COVERAGE = Path("NanoP4Spec/coverage.json")
CORPUS = Path("test/nano-certification/corpus.json")
CALLABLE_KINDS = {
    "FuncDecD": "function", "RelD": "relation", "TableDecD": "table",
    "BuiltinDecD": "builtin", "ExternDecD": "externFunction",
    "ExternRelD": "externRelation",
}
SOURCE_KINDS = set(CALLABLE_KINDS) | {"TypD", "ExternTypD", "VarD"}

# The retained original certificate frontier plus the three N2 integration roots.
# This scope is intentionally smaller than N3's complete callable denominator.
N2_ROOTS = frozenset({
    "exists_", "forall_", "flatten_statementList", "flatten_typeFieldList",
    "flatten_externMethodPrototypeList", "flatten_selectCaseList",
    "flatten_parserLocalDeclarationList", "flatten_tableEntryList",
    "flatten_controlLocalDeclarationList", "flatten_program", "params_of_callableTypeDef",
    "exit_t", "split_dataplane_parameters", "find_action'", "find_action",
    "directionless_trailing'", "exit_e", "update_fieldValue", "Type_eq", "ParameterType_eq",
    "Type_ok", "Var_init",
})
N2_CLOSURE = N2_ROOTS | {
    "typeIR_of_typeDefIR", "find_typeDef_t", "find_map", "default", "add_var_e",
    "dom_map", "in_set", "add_map",
}
N2_CALL_DIRECTIONS = frozenset({
    "allCallArgumentCarriers", "sourceRecursiveSuffixes", "sourceContextCalls",
    "sourceCallPrefixes",
})
N2_PROFILES = (
    ("sourceVariables", "typedOmissionPreservesInitialization"),
    ("primitiveRepresentation", "legalSourceCodecs"),
    ("tableInitialization", "checkedInitialization"),
    ("tableInitialization", "completeSourceLookups"),
    ("tableInitialization", "noLocalOverrides"),
)

# These requirements are intentionally independent of emitter eligibility.
# Text specifies the obligation, not a theorem that this tool may assume.
REQUIREMENTS = {
    "forward": ("N3", "Every terminating reference outcome has a related generated outcome; "
                "preserve failure kinds under the explicit input/environment contract."),
    "reverse": ("N3", "Every terminating generated outcome has a finite related reference "
                "execution; preserve failure kinds without a fixed source-depth bound."),
    "domain": ("N2", "Source-defined admitted inputs cover every legal constructor and "
               "parameter instance; establish every callee precondition on intermediate values."),
    "representation": ("N2", "Prove source coverage, admitted generated-input validity and "
                       "decoder sufficiency, including nested values and observation invariants."),
    "variable": ("N2", "Account for the source variable declaration and its type in the source "
                  "domain and initialized environment; omission from quotations is explicit."),
    "builtin": ("N2", "Operation-specific two-way contract between actual reference dispatch "
                 "and generated wrapper, including rejection, errors and type parameters."),
    "extern": ("N1", "State the abstract extern correspondence and input/output invariant "
                "used by core certificates, without assuming a concrete implementation."),
    "soundness": ("N3", "Successful executable relation evaluation implies the logical relation."),
    "initialization": ("N3", "Actual Nano initialization succeeds on admitted inputs and "
                        "establishes HoldsSpec, guard, callback and environment assumptions."),
    "sourceIdentity": ("N0", "Verify pinned source/export identity, fresh generated artifacts "
                        "and quotations, accounting explicitly for erased fields and VarD."),
    "target": ("N4", "Concrete pinned NanoSwitch port discharges abstract extern contracts "
                "through actual callbacks, including subsequent uses of returned values."),
    "composition": ("N4", "Two-way composition from semantic loading and initialization "
                     "through packet execution with the concrete target."),
    "observations": ("N4", "Preserve ordered packet bytes/ports, forward/drop, failures, "
                      "persistent contexts and relevant fresh counters across packets."),
    "printing": ("N1", "Preserve print_ byte results under the pinned hint environment and "
                  "source provenance; canonical value equality alone is insufficient."),
    "consumer": ("N5", "Checked whole-program packet property and rejection/drop family "
                  "from exported source, actual initialization and concrete target contracts."),
    "replay": ("N4", "Both Lean paths match the pinned upstream terminal outcome and required "
                "observations; missing data, timeout, unsupported and harness failures block."),
    "sensitivity": ("N6", "Discriminating mutations reject changed source, behavior, "
                      "representation and observations at their intended checking boundaries."),
    "review": ("N6", "Independent review of release revision, source-domain adequacy, "
                 "contract statements and remaining trust assumptions."),
    "release": ("N6", "Recorded successful full local gate and exact-revision remote CI; "
                  "these publication observations are separate from kernel proof evidence."),
}


class CertificationError(Exception):
    """A missing, stale or invalid completion input, never semantic rejection."""


def canonical(value):
    return json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n"


def read_json(path):
    try:
        return json.loads(path.read_text())
    except (OSError, ValueError) as error:
        raise CertificationError(f"cannot read certification input {path}: {error}") from error


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(root, args):
    result = subprocess.run(args, cwd=root, text=True, capture_output=True)
    if result.returncode:
        raise CertificationError(
            f"certification prerequisite failed ({result.returncode}): {' '.join(args)}\n"
            f"{result.stdout}{result.stderr}")
    return result.stdout.strip()


def corpus_module(root):
    path = root / "P4SpecTecTest/Oracle/Nano/Certification/corpus.py"
    spec = importlib.util.spec_from_file_location("nano_completion_corpus", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def source_identity(root):
    expected = (root / "exports/nano-p4.al.json.sha256").read_text().split()[0]
    actual = digest(root / EXPORT)
    if actual != expected:
        raise CertificationError("Nano export digest differs from snapshot digest")
    pins = {}
    for path in ("upstream/p4-spectec", "upstream/nano-p4-spec"):
        record = run(root, ["git", "ls-files", "--stage", "--", path]).split()
        if len(record) != 4 or record[0] != "160000" or record[2] != "0":
            raise CertificationError(f"missing or conflicted source pin: {path}")
        if run(root, ["git", "-C", str(root / path), "rev-parse", "HEAD"]) != record[1]:
            raise CertificationError(f"source checkout differs from pin: {path}")
        pins[path] = record[1]
    return {"pins": pins, "export": str(EXPORT), "exportSha256": actual,
            "coverage": str(COVERAGE), "coverageSha256": digest(root / COVERAGE),
            "corpus": str(CORPUS), "corpusSha256": digest(source_path(root, str(CORPUS)))}


def named_type_references(definition, type_keys):
    """Conservatively retain source VarT references, including expression notes.

    This is dependency accounting, not an AL decoder or a proof of typing.
    Only declared names become edges; type parameters remain domain obligations.
    """
    pending, found = [definition], set()
    while pending:
        value = pending.pop()
        if isinstance(value, dict):
            pending.extend(value.values())
        elif isinstance(value, list):
            if (len(value) >= 2 and value[0] == "VarT" and isinstance(value[1], dict)
                    and value[1].get("it") in type_keys):
                found.add(type_keys[value[1]["it"]])
            pending.extend(value)
    return sorted(found)


# Checks the completion CLI itself runs before counting obligations; never a compiled claim.
IDENTITY_CHECKS = ["source pins and export digest", "generated library freshness",
                   "check-quotes", "check-coverage"]
# Handwritten concrete-target theorems; check-target verifies their exact types and axioms.
TARGET_CLAIMS = {
    "target:ExternMethodCall_eval": "NanoP4Target.externsContractHolds",
    "profile:composition": "NanoP4Target.initializedSessionCorrespondence",
    "profile:observations": "NanoP4Target.sessionObservations",
}
# Checked alongside the bound claims: the reference configuration they assume is inhabited.
TARGET_WITNESSES = {"NanoP4Target.referenceWitness"}
TARGET_CHECKS = ["check-target: exact NanoP4Target theorem types and allowed axioms"]
PRINTING_CHECKS = ["check-coverage: print_ dispatch under the empty hint table",
                   "check-target: the pinned export declares no print hints"]
# The whole-program consumer certificate; check-consumer verifies the quotation against the
# decoded export, the proven STF outcome against the pinned upstream recording, and these
# claims' exact types and axioms.
CONSUMER_EVIDENCE = "ExampleProofs.NanoP4SrcAddrFilter.referenceFilter"
CONSUMER_CLAIMS = {f"ExampleProofs.NanoP4SrcAddrFilter.{name}" for name in (
    "initialized", "filterGenerated", "shortGenerated", "stfSession", "stfTransmits",
    "referenceFilter", "programRel")}
CONSUMER_CHECKS = ["check-consumer: export identity, upstream STF observation, "
                   "exact claim types and allowed axioms"]
SESSION_BUNDLE = Path(".artifacts/nano-sessions/sessions-observed.json")
# The mutation suites and the summary each must print: every baseline passes first and every
# mutation is rejected at its named check (each runner fails closed otherwise).
SENSITIVITY_SUITES = (
    ("ExampleProofs/NanoP4FieldUpdate/test/run.py", None),
    ("ExampleProofs/NanoP4SrcAddrFilter/test/run.py", "[src-addr-filter] 6 mutations rejected"),
    ("P4SpecTecTest/Oracle/Nano/Certification/mutations.py", "[cross-layer] 5 mutations rejected"),
)
FIELD_UPDATE_CASES = {"baseline": "all", "behavior": "update_fieldValue.refines_group",
                      "quotation": "compareSpecs", "representation": "Scalar.sourceRel"}
SENSITIVITY_CHECKS = ["field-update, source-address filter and cross-layer mutation suites: "
                      "each baseline passes and each mutation is rejected at its named check"]
# Review and release are publication records about one tree, not proofs: the record names the
# digest of every tracked file outside `.agents/`, so recording them changes no digest.
RELEASE_RECORD = Path(".agents/notes/nano-release.json")
REVIEW_CHECKS = ["recorded independent review of this tree digest"]
RELEASE_CHECKS = ["recorded successful full gate and exact-revision CI for this tree digest"]
PUBLICATION = ("review", "release")
TYPING_REPLAY = ["nano-p4-run and nano-p4-interp match the upstream verdict and outputs"]
SESSION_REPLAY = ["check-nano-sessions matches every upstream session step on both paths"]

MONOMORPHIC_DOMAIN = (("sourceEntry", "sourceInputsToTwoWay"),
                      ("producer", "sourceInputsToSourceOutput"))
# The runtime profile's grammar contains the source grammar and adds only the configured
# runtime-only raw extern (decisions, "Nano value domains and codecs"); complete
# runtime evidence therefore covers the source domain as well as actual runtime values.
RUNTIME_DOMAIN = (("sourceEntry", "runtimeInputsToTwoWay"),
                  ("producer", "runtimeInputsToRuntimeOutput"))
RUNTIME_CALL_DIRECTIONS = frozenset({"runtimeCallArgumentCarriers"})


def domain_evidence(tag, definition, entry, claim):
    """Bind a callable's source domain only when its complete domain evidence exists.

    A polymorphic or leaf callable has one combined source-domain contract. A monomorphic
    bodied callable needs source entry and producer claims, and call admission when it has
    call sites (the bounded N2 criteria, applied to every callable), all in the source profile
    or all in the runtime profile. The returned name is the entry claim; every required claim
    is still checked as compiled by check-coverage.
    """
    combined = claim(entry, "sourceDomain", "sourceInputsAndOutput")
    # An extern relation's inputs are covered by its runtime entry; its results are those of
    # the abstract extern contract that entry assumes, discharged by the target.
    if tag == "ExternRelD":
        return claim(entry, "sourceEntry", "runtimeInputsToTwoWay")
    polymorphic = (tag == "FuncDecD" and len(definition["it"]) > 2
                   and bool(definition["it"][2]))
    if tag not in ("FuncDecD", "RelD", "TableDecD") or polymorphic:
        return combined
    if not entry["dependencies"] and combined:
        return combined
    for profile, calls in ((MONOMORPHIC_DOMAIN, N2_CALL_DIRECTIONS),
                           (RUNTIME_DOMAIN, RUNTIME_CALL_DIRECTIONS)):
        names = [claim(entry, kind, direction) for kind, direction in profile]
        if entry["dependencies"]:
            admitted = [c["name"] for c in entry["claims"] if c["kind"] == "callAdmission"
                        and c["direction"] in calls]
            names.append(admitted[0] if admitted else None)
        if all(names):
            return names[0]
    return None


def build_manifest(source, coverage, corpus_ids, identity):
    """Join the full source inventory to existing callable proof evidence.

    No independent callable-dependency or proof-eligibility algorithm is used.
    Forward, reverse, builtin dispatch, source codec and run-soundness contracts have adapters.
    All other obligations remain explicit, with no user-editable discharge bit.
    """
    if (not isinstance(source, list) or type(coverage.get("schemaVersion")) is not int
            or coverage["schemaVersion"] != 3):
        raise CertificationError("unsupported source or coverage schema")
    if coverage.get("library") != "NanoP4Spec" or coverage.get("input") != str(EXPORT):
        raise CertificationError("coverage library/input does not match Nano profile")
    entries = coverage.get("definitions", [])
    by_id = {entry["id"]: entry for entry in entries}
    if len(by_id) != len(entries):
        raise CertificationError("duplicate callable coverage identity")
    representation_entries = coverage.get("representations", [])
    representations_by_id = {entry["id"]: entry for entry in representation_entries}
    if len(representations_by_id) != len(representation_entries):
        raise CertificationError("duplicate type coverage identity")
    declarations, obligations, seen, callables = [], [], set(), set()
    represented_types = set()
    type_keys = {d["it"][1]["it"]: f"{d['it'][0]}:{d['it'][1]['it']}" for d in source
                 if isinstance(d, dict) and isinstance(d.get("it"), list)
                 and d["it"][0] in ("TypD", "ExternTypD")}

    def add(key, requirement, subject, stage="core", dependencies=(), evidence=None,
            checked_by=None):
        obligation = {"id": key, "requirement": requirement, "subject": subject,
                      "stage": stage, "dependencies": list(dependencies),
                      "coverageClaim": evidence}
        if checked_by is not None:
            obligation["checkedBy"] = checked_by
        obligations.append(obligation)

    def claim(entry, kind, direction):
        found = [c for c in entry["claims"] if c["kind"] == kind and c["direction"] == direction]
        if len(found) > 1:
            raise CertificationError(f"duplicate required claim: {entry['id']} {kind}")
        return found[0]["name"] if found else None

    def profile_claim(kind, direction):
        return claim({"id": "source profile", "claims": coverage.get("profiles", [])},
                     kind, direction)

    for ordinal, definition in enumerate(source):
        try:
            tag, name = definition["it"][0], definition["it"][1]["it"]
            location = definition["at"]["left"]
        except (KeyError, IndexError, TypeError) as error:
            raise CertificationError(f"malformed source declaration at index {ordinal}") from error
        if tag not in SOURCE_KINDS or not isinstance(name, str):
            raise CertificationError(f"unsupported source declaration at index {ordinal}: {tag}")
        key = f"{tag}:{name}"
        if key in seen:
            raise CertificationError(f"duplicate source declaration: {key}")
        seen.add(key)
        declarations.append({"id": key, "ordinal": ordinal, "name": name, "kind": tag,
                             "source": location["file"], "line": location["line"]})
        representations = ["profile:primitiveRepresentations"] + [f"representation:{ref}"
                           for ref in named_type_references(definition, type_keys) if ref != key]
        if tag in ("TypD", "ExternTypD"):
            represented_types.add(name)
            entry = representations_by_id.get(name)
            expected_kind = "type" if tag == "TypD" else "externType"
            if entry is None or entry["kind"] != expected_kind:
                raise CertificationError(f"source type missing/mismatched in coverage: {key}")
            if entry["source"] != location["file"]:
                raise CertificationError(f"type source differs from coverage: {key}")
            add(f"representation:{key}", "representation", key, dependencies=representations,
                evidence=claim(entry, "representation", "sourceCodec"))
        elif tag == "VarD":
            add(f"variable:{key}", "variable", key, dependencies=representations,
                evidence=profile_claim("sourceVariables", "typedOmissionPreservesInitialization"))
        else:
            callables.add(name)
            entry = by_id.get(name)
            if entry is None or entry["kind"] != CALLABLE_KINDS[tag]:
                raise CertificationError(f"source callable missing/mismatched in coverage: {key}")
            if entry["source"] != location["file"]:
                raise CertificationError(f"callable source differs from coverage: {key}")
            domain = f"domain:{name}"
            add(domain, "domain", key, dependencies=representations,
                evidence=domain_evidence(tag, definition, entry, claim))
            if entry["kind"] == "builtin":
                add(f"contract:{name}", "builtin", key, dependencies=[domain],
                    evidence=claim(entry, "builtinContract", "twoWayDispatch"))
            elif entry["kind"].startswith("extern"):
                add(f"contract:{name}", "extern", key, dependencies=[domain],
                    evidence=claim(entry, "externContract", "abstractTwoWay"))
                add(f"target:{name}", "target", key, "target", [f"contract:{name}"],
                    evidence=TARGET_CLAIMS.get(f"target:{name}"), checked_by=TARGET_CHECKS)
            else:
                for direction, requirement in (("referenceToGenerated", "forward"),
                                               ("generatedToReference", "reverse")):
                    deps = [domain, "profile:initialization", "profile:sourceIdentity"]
                    for callee in dict.fromkeys(entry["dependencies"] + entry["group"]):
                        if callee == name:
                            continue
                        target = by_id.get(callee)
                        if target is None:
                            raise CertificationError(f"unknown coverage dependency: {callee}")
                        prefix = "contract" if target["kind"] in (
                            "builtin", "externFunction", "externRelation") else requirement
                        deps.append(f"{prefix}:{callee}")
                    # Each direction has its own generated statement, checked by check-coverage.
                    evidence = claim(entry, "refinement", direction)
                    add(f"{requirement}:{name}", requirement, key, dependencies=deps,
                        evidence=evidence)
                if tag == "RelD":
                    add(f"soundness:{name}", "soundness", key,
                        evidence=claim(entry, "runSoundness", "generatedSuccessToRelation"))
    if represented_types != set(representations_by_id):
        raise CertificationError("coverage contains a type absent from the source")
    if callables != set(by_id):
        raise CertificationError("coverage contains a callable absent from the source")
    add("profile:primitiveRepresentations", "representation", "primitive and container codecs",
        evidence=profile_claim("primitiveRepresentation", "legalSourceCodecs"))
    add("profile:sourceIdentity", "sourceIdentity", "NanoP4Spec", checked_by=IDENTITY_CHECKS)
    add("profile:initialization", "initialization", "NanoP4Spec",
        evidence=profile_claim("initialization", "certificateEnvironment"), dependencies=
        ["profile:sourceIdentity"] + [o["id"] for o in obligations if o["requirement"] == "variable"])
    target_contracts = [o["id"] for o in obligations if o["requirement"] == "target"]
    add("profile:observations", "observations", "NanoSwitch", "target",
        target_contracts + ["profile:primitiveRepresentations"],
        evidence=TARGET_CLAIMS["profile:observations"], checked_by=TARGET_CHECKS)
    add("profile:printing", "printing", "NanoSwitch", "target",
        ["contract:print_"] if "print_" in by_id else ["profile:primitiveRepresentations"],
        evidence=(claim(by_id["print_"], "builtinContract", "twoWayDispatch")
                  if "print_" in by_id else None), checked_by=PRINTING_CHECKS)
    core_proofs = [o["id"] for o in obligations if o["requirement"] in ("forward", "reverse")]
    add("profile:composition", "composition", "NanoSwitch", "target",
        core_proofs + target_contracts + ["profile:initialization", "profile:observations"],
        evidence=TARGET_CLAIMS["profile:composition"], checked_by=TARGET_CHECKS)
    add("profile:consumer", "consumer", "Nano-P4 milestone", "release",
        ["profile:composition", "profile:sourceIdentity"],
        evidence=CONSUMER_EVIDENCE, checked_by=CONSUMER_CHECKS)
    if len(corpus_ids) != len(set(corpus_ids)):
        raise CertificationError("duplicate corpus obligation identity")
    for case in corpus_ids:
        if not case.startswith(("corpus:typing:", "corpus:packet:")):
            raise CertificationError(f"unknown corpus obligation kind: {case}")
        typing = case.startswith("corpus:typing:")
        add(f"replay:{case}", "replay", case, "core" if typing else "target",
            ["profile:sourceIdentity"], checked_by=TYPING_REPLAY if typing else SESSION_REPLAY)
    add("profile:sensitivity", "sensitivity", "Nano-P4 milestone", "release",
        ["profile:sourceIdentity", "profile:consumer"], checked_by=SENSITIVITY_CHECKS)
    add("profile:review", "review", "Nano-P4 milestone", "release",
        [o["id"] for o in obligations], checked_by=REVIEW_CHECKS)
    add("profile:release", "release", "Nano-P4 milestone", "release", ["profile:review"],
        checked_by=RELEASE_CHECKS)
    ids = {obligation["id"] for obligation in obligations}
    if len(ids) != len(obligations):
        raise CertificationError("duplicate completion obligation identity")
    for obligation in obligations:
        if not set(obligation["dependencies"]) <= ids:
            raise CertificationError(f"unknown obligation dependency: {obligation['id']}")
    return {"schemaVersion": 1, "generator": "scripts/nano-certification.py",
            "profile": "docs/design.md#9-nano-p4-scope-and-acceptance", "identity": identity,
            "requirements": {key: {"owner": owner, "expectedEvidence": shape}
                             for key, (owner, shape) in REQUIREMENTS.items()},
            "declarations": declarations, "obligations": obligations}


def check_stored(text, regenerated):
    if text != canonical(regenerated):
        raise CertificationError("completion manifest differs from current inputs/requirements")


MILESTONES = ("N0", "N1", "N2", "N3", "N4", "N5", "N6")


def outstanding(manifest, stage="all", verified=frozenset(), owned=None):
    """Report missing evidence after callers have validated compiled bindings.

    Presence of a binding is not evidence until the Lean checker succeeds. An obligation
    with `checkedBy` counts only when the caller ran those checks and they verified that
    obligation (`verified`), whether or not it also names a compiled claim.
    `owned` restricts the result to requirements owned by milestones up to it.
    This function alone must never be exposed as a certification verdict.
    """
    stages = {"core"} if stage == "core" else {"core", "target"} if stage == "target" else {
        "core", "target", "release"}
    owners = None if owned is None else set(MILESTONES[:MILESTONES.index(owned) + 1])
    requirements = manifest["requirements"]

    def done(o):
        if o.get("checkedBy"):
            return o["id"] in verified and (o["coverageClaim"] is not None or o["requirement"] in (
                "sourceIdentity", "replay", "sensitivity") + PUBLICATION)
        return o["coverageClaim"] is not None

    return [o for o in manifest["obligations"]
            if o["stage"] in stages and not done(o)
            and (owners is None or requirements[o["requirement"]]["owner"] in owners)]


def _required_claim(entry, kind, directions):
    """Check binding presence only; the caller must first run the compiled Lean checker."""
    found = [claim for claim in entry.get("claims", [])
             if claim.get("kind") == kind and claim.get("direction") in directions]
    if len(found) > 1:
        raise CertificationError(f"duplicate N2 claim: {entry.get('id', 'profile')} {kind}")
    return bool(found)



def n2_missing(source, coverage):
    """List every missing N2 binding after independent compiled checking.

    This does not turn JSON into proof evidence. The CLI first verifies exact source
    identity, manifest freshness, compiled claim types/axioms and quotations. The scope
    comes from the entire pinned source type/variable/builtin inventories and the complete
    checked dependency closure of the explicitly retained N2 roots, never emitter success.
    """
    # Reject inventory additions/removals and mismatched source identities independently
    # of whether their remaining claim counts happen to equal the old denominator.
    build_manifest(source, coverage, [], {})
    entries = {entry["id"]: entry for entry in coverage["definitions"]}
    representations = {entry["id"]: entry for entry in coverage["representations"]}
    declarations = {(d["it"][0], d["it"][1]["it"]): d for d in source}
    missing = []

    def require(entry, kind, direction, subject):
        if not _required_claim(entry, kind, {direction}):
            missing.append(f"{subject}: {kind}/{direction}")

    for (kind, name), definition in declarations.items():
        if kind in ("TypD", "ExternTypD"):
            require(representations[name], "representation", "sourceCodec", f"{kind}:{name}")
        elif kind == "BuiltinDecD":
            require(entries[name], "builtinContract", "twoWayDispatch", name)
            require(entries[name], "sourceDomain", "sourceInputsAndOutput", name)
            require(entries[name], "refinement", "referenceToGenerated", name)
            require(entries[name], "refinement", "generatedToReference", name)
    # These pin-local tripwires supplement, never replace, identity-by-identity matching.
    for kind, expected in (("VarD", 8), ("BuiltinDecD", 26)):
        actual = sum(tag == kind for tag, _ in declarations)
        if actual != expected:
            missing.append(f"source {kind} inventory: expected {expected}, found {actual}")
    profiles = {"id": "source profile", "claims": coverage.get("profiles", [])}
    for kind, direction in N2_PROFILES:
        require(profiles, kind, direction, "profile")

    pending, reached = list(sorted(N2_ROOTS)), set()
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        reached.add(name)
        entry = entries.get(name)
        if entry is None:
            missing.append(f"{name}: missing N2 root or dependency")
            continue
        pending.extend(entry["dependencies"] + entry["group"])
    for name in sorted(N2_CLOSURE - reached):
        missing.append(f"{name}: removed from the required N2 dependency closure")
    for name in sorted(reached - N2_CLOSURE):
        missing.append(f"{name}: new N2 dependency requires explicit scope review")

    for name in sorted(reached):
        entry = entries.get(name)
        if entry is None or entry["kind"] == "builtin":
            continue
        kind = next((tag for tag, _name in declarations if _name == name
                     and tag in CALLABLE_KINDS), None)
        if kind not in ("FuncDecD", "RelD", "TableDecD"):
            missing.append(f"{name}: unsupported N2 external dependency")
            continue
        definition = declarations[kind, name]
        require(entry, "refinement", "referenceToGenerated", name)
        require(entry, "refinement", "generatedToReference", name)
        polymorphic = kind == "FuncDecD" and bool(definition["it"][2])
        if polymorphic:
            require(entry, "sourceDomain", "sourceInputsAndOutput", name)
        else:
            require(entry, "sourceEntry", "sourceInputsToTwoWay", name)
            # Output-free relations still have a checked Unit/source-empty-tuple producer.
            require(entry, "producer", "sourceInputsToSourceOutput", name)
        if kind == "RelD":
            require(entry, "runSoundness", "generatedSuccessToRelation", name)
        if entry["dependencies"] and not _required_claim(
                entry, "callAdmission", N2_CALL_DIRECTIONS):
            missing.append(f"{name}: callAdmission/fullSourceCallInputs")
    return sorted(missing)


def target_verified(manifest):
    """Run check-target; the target-stage obligations whose compiled claims it verified."""
    output = run(ROOT, ["lake", "exe", "check-target"])
    claims = {line.removeprefix("[target] claim ").strip() for line in output.splitlines()
              if line.startswith("[target] claim ")}
    if (claims != set(TARGET_CLAIMS.values()) | TARGET_WITNESSES
            or "pinned print hints empty" not in output):
        raise CertificationError("check-target did not verify exactly the bound target claims")
    return {o["id"] for o in manifest["obligations"]
            if o.get("checkedBy") in (TARGET_CHECKS, PRINTING_CHECKS)
            and o["coverageClaim"] is not None}


def consumer_verified(manifest):
    """Run check-consumer on the pinned session recording; the consumer obligations it
    verified."""
    fixture = corpus_helper(ROOT / "P4SpecTecTest/Oracle/NanoSwitch/Sessions/fixture.py",
                            "nano_session_fixture")
    _, data = fixture.read()
    bundle = ROOT / SESSION_BUNDLE
    bundle.parent.mkdir(parents=True, exist_ok=True)
    corpus_helper(ROOT / "scripts/spec-snapshot.py", "spec_snapshot").atomic_write(bundle, data)
    run(ROOT, ["lake", "build", "check-consumer"])
    output = run(ROOT, ["lake", "exe", "check-consumer", str(SESSION_BUNDLE)])
    claims = {line.removeprefix("[consumer] claim ").strip() for line in output.splitlines()
              if line.startswith("[consumer] claim ")}
    if (claims != CONSUMER_CLAIMS or "[consumer] identity:" not in output
            or "[consumer] observation:" not in output):
        raise CertificationError("check-consumer did not verify exactly the consumer claims, "
                                 "the export identity and the upstream observation")
    return {o["id"] for o in manifest["obligations"]
            if o.get("checkedBy") == CONSUMER_CHECKS and o["coverageClaim"] is not None}


def excuse_unpublished(missing):
    """Split out the review and release records; every other obligation stays missing."""
    return ([o for o in missing if o["requirement"] not in PUBLICATION],
            [o for o in missing if o["requirement"] in PUBLICATION])


def sensitivity_verified(manifest):
    """Run every mutation suite; the sensitivity obligation when all of them pass."""
    run(ROOT, ["lake", "build", "ExampleProofs", "check-consumer", "nano-program-quote",
               "check-quotes"])
    for path, summary in SENSITIVITY_SUITES:
        output = run(ROOT, ["lake", "env", "python3", path])
        if summary is None:
            try:
                results = json.loads(output.splitlines()[-1])["results"]
            except (IndexError, ValueError, KeyError, TypeError) as error:
                raise CertificationError(f"{path}: unreadable result") from error
            observed = {r.get("case"): (r.get("boundary"), r.get("accepted")) for r in results}
            expected = {case: (boundary, case == "baseline")
                        for case, boundary in FIELD_UPDATE_CASES.items()}
            if len(results) != len(expected) or observed != expected:
                raise CertificationError(f"{path}: unexpected mutation outcomes {observed}")
        elif output.splitlines()[-1:] != [summary]:
            raise CertificationError(f"{path}: expected {summary!r}")
    return {o["id"] for o in manifest["obligations"]
            if o.get("checkedBy") == SENSITIVITY_CHECKS}


def _digest(entries):
    """SHA-256 over sorted (mode, path, content) entries outside `.agents/`."""
    digest = hashlib.sha256()
    for mode, path, content in sorted(entries, key=lambda e: e[1]):
        if not path.startswith(".agents/"):
            digest.update(f"{mode} {path} {hashlib.sha256(content).hexdigest()}\n".encode())
    return digest.hexdigest()


def tree_digest(root):
    """The digest of the checkout: every tracked path outside `.agents/`, with file bytes from
    the working tree, link targets, and submodule commits from the index."""
    listing = subprocess.run(["git", "ls-files", "-s", "-z"], cwd=root, capture_output=True,
                             check=True).stdout.decode()
    entries = []
    for entry in filter(None, listing.split("\0")):
        meta, path = entry.split("\t", 1)
        mode, blob, _ = meta.split()
        target = root / path
        content = (blob.encode() if mode == "160000" else
                   str(target.readlink()).encode() if mode == "120000" else target.read_bytes())
        entries.append((mode, path, content))
    return _digest(entries)


def revision_digest(root, revision):
    """The same digest computed from a commit's own objects, independent of the checkout.

    The revision must be a full commit id naming a commit: a symbolic ref such as `HEAD`, or a
    tree id, would follow the checkout instead of naming what was reviewed."""
    if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
        raise CertificationError(f"recorded revision must be a full commit id: {revision!r}")
    resolved = subprocess.run(["git", "rev-parse", "--verify", "--quiet", "--end-of-options",
                               f"{revision}^{{commit}}"], cwd=root, capture_output=True,
                              text=True)
    if resolved.returncode or resolved.stdout.strip() != revision:
        raise CertificationError(f"recorded revision is not a commit: {revision!r}")
    listing = subprocess.run(["git", "ls-tree", "-r", "-z", revision], cwd=root,
                             capture_output=True)
    if listing.returncode:
        raise CertificationError(f"unknown recorded revision {revision!r}")
    rows = []
    for entry in filter(None, listing.stdout.decode().split("\0")):
        meta, path = entry.split("\t", 1)
        mode, _, obj = meta.split()
        rows.append((mode, path, obj))
    blobs = [obj for mode, _, obj in rows if mode != "160000"]
    output = subprocess.run(["git", "cat-file", "--batch"], cwd=root, capture_output=True,
                            input="".join(f"{obj}\n" for obj in blobs).encode(), check=True).stdout
    contents, offset = {}, 0
    for obj in blobs:
        header_end = output.index(b"\n", offset)
        size = int(output[offset:header_end].split()[2])
        contents[obj] = output[header_end + 1:header_end + 1 + size]
        offset = header_end + 1 + size + 1
    return _digest([(mode, path, obj.encode() if mode == "160000" else contents[obj])
                    for mode, path, obj in rows])


def publication_verified(manifest, root=ROOT):
    """The review and release obligations whose records describe exactly this tree.

    Absent or stale records verify nothing; a record for this tree must be complete."""
    path = root / RELEASE_RECORD
    if not path.is_file():
        return set(), "no review or release record"
    record = read_json(path)
    if record.get("tree") != tree_digest(root):
        return set(), f"{RELEASE_RECORD} describes another tree"
    review, release = record.get("review"), record.get("release")
    fields = ("revision", "reviewer", "verdict", "record")
    if not isinstance(review, dict) or any(not review.get(k) for k in fields) or (
            review["verdict"] != "no unresolved findings") or not (root / review["record"]).is_file():
        raise CertificationError(f"{RELEASE_RECORD}: incomplete review for this tree")
    revision = review["revision"]
    if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
        raise CertificationError(f"{RELEASE_RECORD}: revision must be a full commit id: "
                                 f"{revision!r}")
    kinds = {"review"}
    if release is not None:
        gate, ci = release.get("gate", {}), release.get("ci", {})
        if (release.get("revision") != revision or gate.get("exit") != 0
                or not gate.get("command") or ci.get("conclusion") != "success"
                or not ci.get("run") or ci.get("headSha") != revision):
            raise CertificationError(f"{RELEASE_RECORD}: incomplete release for this tree")
        kinds.add("release")
    # The reviewed and released revision must itself have this content, so a record cannot be
    # carried forward to a tree nobody reviewed or tested by editing its digest. Only a missing
    # object is excused: a clone without the commit (CI checks out shallowly) cannot check the
    # record, so it counts nothing. An object that exists but is not a commit is an error.
    missing = subprocess.run(["git", "cat-file", "-e", revision], cwd=root,
                             capture_output=True).returncode != 0
    if missing:
        return set(), f"{RELEASE_RECORD} names commit {revision}, absent from this clone"
    if revision_digest(root, revision) != record["tree"]:
        raise CertificationError(f"{RELEASE_RECORD}: revision {revision} is not this tree")
    verified = {o["id"] for o in manifest["obligations"] if o["requirement"] in kinds}
    return verified, " and ".join(sorted(kinds)) + " recorded for this tree"


def replay_verified(manifest, corpus):
    """Run both typing replay legs and the session replay; every agreeing replay obligation."""
    replay = corpus_helper(ROOT / "P4SpecTecTest/Oracle/Nano/Replay/replay.py", "nano_replay")
    typing = {}
    for o in manifest["obligations"]:
        case = o["subject"]
        if o["requirement"] == "replay" and case.startswith("corpus:typing:"):
            path = f"exports/programs/nano-p4/{case.removeprefix('corpus:typing:')}.json"
            verdict = ROOT / path.removesuffix(".json")
            verdict = verdict.with_name(verdict.name + ".verdict")
            if verdict.is_file():
                typing[path] = (o["id"], verdict.read_text().strip())
    agreeing = replay.agreeing_programs(list(typing), {p: v for p, (_, v) in typing.items()})
    verified = {typing[path][0] for path in agreeing}
    sessions = corpus_helper(ROOT / "P4SpecTecTest/Oracle/NanoSwitch/Sessions/check.py",
                             "nano_session_check")
    run(ROOT, ["lake", "build", "check-nano-sessions"])
    try:
        matched = sessions.replay(ROOT / ".lake/build/bin/check-nano-sessions")
    except (SystemExit, subprocess.TimeoutExpired) as error:
        raise CertificationError(f"session replay failed: {error}") from error
    verified |= {f"replay:{case}" for case in matched}
    return verified


def corpus_helper(path, name):
    """Load a colocated oracle driver as a module, with its own directory importable."""
    sys.path.insert(0, str(path.parent))
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true", help="regenerate metadata, not proof evidence")
    parser.add_argument("--require-complete", choices=("core", "target", "all"))
    parser.add_argument("--require-owned", choices=MILESTONES,
                        help="require every obligation owned by milestones up to this one; "
                        "later-owned obligations stay reported")
    parser.add_argument("--allow-unpublished", action="store_true",
                        help="let review and release records be absent or describe another "
                        "tree; every proof, replay and sensitivity obligation stays required")
    parser.add_argument("--require-n2", action="store_true",
                        help="require the bounded N2 profile; broader stages stay independent")
    args = parser.parse_args(argv)
    if args.allow_unpublished and not (args.require_complete or args.require_owned):
        parser.error("--allow-unpublished qualifies a completion requirement")
    if args.update and (args.require_complete or args.require_n2 or args.require_owned):
        parser.error("--update cannot be combined with a completion requirement")
    if args.require_complete and args.require_owned:
        parser.error("--require-owned selects its own stages; omit --require-complete")
    try:
        corpus = corpus_module(ROOT)
        corpus_ids = corpus.check(root=ROOT, path=source_path(ROOT, str(CORPUS)))
        source, coverage = read_json(ROOT / EXPORT), read_json(ROOT / COVERAGE)
        manifest = build_manifest(source, coverage, corpus_ids, source_identity(ROOT))
        if args.update:
            (ROOT / MANIFEST).write_text(canonical(manifest))
            print(f"[completion] wrote {MANIFEST}; metadata only, no validation verdict")
            return 0
        check_stored((ROOT / MANIFEST).read_text(), manifest)
        run(ROOT, ["lake", "exe", "p4spectec-gen", str(EXPORT), "--lib", "NanoP4Spec",
                   "--runtime-extern", "value", "--check"])
        run(ROOT, ["lake", "exe", "check-coverage"])
        run(ROOT, ["lake", "exe", "check-quotes"])
        verified = {o["id"] for o in manifest["obligations"]
                    if o.get("checkedBy") == IDENTITY_CHECKS}
        verified |= target_verified(manifest)
        verified |= replay_verified(manifest, corpus)
        # The consumer is release-stage evidence; narrower scopes need not build the example.
        if (MILESTONES.index(args.require_owned) >= MILESTONES.index("N5") if args.require_owned
                else args.require_complete in (None, "all")):
            verified |= consumer_verified(manifest)
        # The mutation suites are slow; only a requirement that includes N6 runs them.
        if (MILESTONES.index(args.require_owned) >= MILESTONES.index("N6") if args.require_owned
                else args.require_complete == "all"):
            verified |= sensitivity_verified(manifest)
            published, state = publication_verified(manifest)
            verified |= published
            print(f"[completion] publication: {state}")
        # Owned scope spans every stage; the owner filter excludes later milestones' work.
        stage = "all" if args.require_owned else args.require_complete or "all"
        missing = outstanding(manifest, stage, verified=verified, owned=args.require_owned)
        if args.allow_unpublished:
            missing, pending = excuse_unpublished(missing)
            if pending:
                print(f"[completion] {len(pending)} publication records pending, allowed")
        bound = sum(o["coverageClaim"] is not None for o in manifest["obligations"])
        print(f"[completion] {len(manifest['declarations'])} source declarations; "
              f"{len(manifest['obligations'])} obligations; {bound} compiled claim bindings; "
              f"{len(missing)} unresolved")
        if args.require_n2:
            n2 = n2_missing(source, coverage)
            for obligation in n2:
                print(f"[completion] missing N2 {obligation}")
            if n2:
                raise CertificationError(f"Nano N2 certification is incomplete ({len(n2)} bindings)")
            print("[completion] bounded N2 source-domain and selected-closure checks passed; "
                  "broader core, target and release obligations remain independent")
        if (args.require_complete or args.require_owned) and missing:
            for kind in REQUIREMENTS:
                count = sum(o["requirement"] == kind for o in missing)
                if count:
                    print(f"[completion] missing {kind}: {count}")
            scope = args.require_complete or f"{args.require_owned}-owned"
            raise CertificationError(f"Nano {scope} certification is incomplete")
        return 0
    except (CertificationError, OSError, ValueError, KeyError) as error:
        print(f"[completion] {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
