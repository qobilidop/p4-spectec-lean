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


def build_manifest(source, coverage, corpus_ids, identity):
    """Join the full source inventory to existing callable proof evidence.

    No independent callable-dependency or proof-eligibility algorithm is used.
    Forward, reverse, builtin dispatch and run-soundness contracts have evidence adapters.
    All other obligations remain explicit, with no user-editable discharge bit.
    """
    if (not isinstance(source, list) or type(coverage.get("schemaVersion")) is not int
            or coverage["schemaVersion"] != 1):
        raise CertificationError("unsupported source or coverage schema")
    if coverage.get("library") != "NanoP4Spec" or coverage.get("input") != str(EXPORT):
        raise CertificationError("coverage library/input does not match Nano profile")
    entries = coverage.get("definitions", [])
    by_id = {entry["id"]: entry for entry in entries}
    if len(by_id) != len(entries):
        raise CertificationError("duplicate callable coverage identity")
    declarations, obligations, seen, callables = [], [], set(), set()
    type_keys = {d["it"][1]["it"]: f"{d['it'][0]}:{d['it'][1]['it']}" for d in source
                 if isinstance(d, dict) and isinstance(d.get("it"), list)
                 and d["it"][0] in ("TypD", "ExternTypD")}

    def add(key, requirement, subject, stage="core", dependencies=(), evidence=None):
        obligations.append({"id": key, "requirement": requirement, "subject": subject,
                            "stage": stage, "dependencies": list(dependencies),
                            "coverageClaim": evidence})

    def claim(entry, kind, direction):
        found = [c for c in entry["claims"] if c["kind"] == kind and c["direction"] == direction]
        if len(found) > 1:
            raise CertificationError(f"duplicate required claim: {entry['id']} {kind}")
        return found[0]["name"] if found else None

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
            add(f"representation:{key}", "representation", key, dependencies=representations)
        elif tag == "VarD":
            add(f"variable:{key}", "variable", key, dependencies=representations)
        else:
            callables.add(name)
            entry = by_id.get(name)
            if entry is None or entry["kind"] != CALLABLE_KINDS[tag]:
                raise CertificationError(f"source callable missing/mismatched in coverage: {key}")
            if entry["source"] != location["file"]:
                raise CertificationError(f"callable source differs from coverage: {key}")
            domain = f"domain:{name}"
            add(domain, "domain", key, dependencies=representations)
            if entry["kind"] == "builtin":
                add(f"contract:{name}", "builtin", key, dependencies=[domain],
                    evidence=claim(entry, "builtinContract", "twoWayDispatch"))
            elif entry["kind"].startswith("extern"):
                add(f"contract:{name}", "extern", key, dependencies=[domain])
                add(f"target:{name}", "target", key, "target", [f"contract:{name}"])
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
    if callables != set(by_id):
        raise CertificationError("coverage contains a callable absent from the source")
    add("profile:primitiveRepresentations", "representation", "primitive and container codecs")
    add("profile:sourceIdentity", "sourceIdentity", "NanoP4Spec")
    add("profile:initialization", "initialization", "NanoP4Spec", dependencies=
        ["profile:sourceIdentity"] + [o["id"] for o in obligations if o["requirement"] == "variable"])
    target_contracts = [o["id"] for o in obligations if o["requirement"] == "target"]
    add("profile:observations", "observations", "NanoSwitch", "target",
        target_contracts + ["profile:primitiveRepresentations"])
    add("profile:printing", "printing", "NanoSwitch", "target",
        ["contract:print_"] if "print_" in by_id else ["profile:primitiveRepresentations"])
    core_proofs = [o["id"] for o in obligations if o["requirement"] in ("forward", "reverse")]
    add("profile:composition", "composition", "NanoSwitch", "target",
        core_proofs + target_contracts + ["profile:initialization", "profile:observations"])
    add("profile:consumer", "consumer", "Nano-P4 milestone", "release",
        ["profile:composition", "profile:sourceIdentity"])
    if len(corpus_ids) != len(set(corpus_ids)):
        raise CertificationError("duplicate corpus obligation identity")
    for case in corpus_ids:
        if not case.startswith(("corpus:typing:", "corpus:packet:")):
            raise CertificationError(f"unknown corpus obligation kind: {case}")
        stage = "core" if case.startswith("corpus:typing:") else "target"
        add(f"replay:{case}", "replay", case, stage, ["profile:sourceIdentity"])
    add("profile:sensitivity", "sensitivity", "Nano-P4 milestone", "release",
        ["profile:sourceIdentity", "profile:consumer"])
    add("profile:review", "review", "Nano-P4 milestone", "release",
        [o["id"] for o in obligations])
    add("profile:release", "release", "Nano-P4 milestone", "release", ["profile:review"])
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


def outstanding(manifest, stage="all"):
    """Report missing evidence after callers have validated compiled bindings.

    Presence of a binding is not evidence until the Lean checker succeeds.
    This function alone must never be exposed as a certification verdict.
    """
    stages = {"core"} if stage == "core" else {"core", "target"} if stage == "target" else {
        "core", "target", "release"}
    return [o for o in manifest["obligations"]
            if o["stage"] in stages and o["coverageClaim"] is None]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--update", action="store_true", help="regenerate metadata, not proof evidence")
    parser.add_argument("--require-complete", choices=("core", "target", "all"))
    args = parser.parse_args(argv)
    if args.update and args.require_complete:
        parser.error("--update cannot be combined with --require-complete")
    try:
        corpus = corpus_module(ROOT)
        corpus_ids = corpus.check(root=ROOT, path=source_path(ROOT, str(CORPUS)))
        manifest = build_manifest(read_json(ROOT / EXPORT), read_json(ROOT / COVERAGE),
                                  corpus_ids, source_identity(ROOT))
        if args.update:
            (ROOT / MANIFEST).write_text(canonical(manifest))
            print(f"[completion] wrote {MANIFEST}; metadata only, no validation verdict")
            return 0
        check_stored((ROOT / MANIFEST).read_text(), manifest)
        run(ROOT, ["lake", "exe", "check-coverage"])
        run(ROOT, ["lake", "exe", "check-quotes"])
        missing = outstanding(manifest, args.require_complete or "all")
        bound = sum(o["coverageClaim"] is not None for o in manifest["obligations"])
        print(f"[completion] {len(manifest['declarations'])} source declarations; "
              f"{len(manifest['obligations'])} obligations; {bound} compiled claim bindings; "
              f"{len(missing)} unresolved")
        if args.require_complete and missing:
            for kind in REQUIREMENTS:
                count = sum(o["requirement"] == kind for o in missing)
                if count:
                    print(f"[completion] missing {kind}: {count}")
            raise CertificationError(f"Nano {args.require_complete} certification is incomplete")
        return 0
    except (CertificationError, OSError, ValueError, KeyError) as error:
        print(f"[completion] {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
