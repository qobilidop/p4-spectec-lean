#!/usr/bin/env python3
"""Capture every pinned Nano STF session from the upstream AL simulator (upstream shell).

    capture.py --upstream ABS --spec ABS [--check | --update]

The probe runs upstream's own `run_stf_test` with an observing pipe; it never changes target
outputs. Sessions follow the pinned corpus inventory, so none can be omitted silently.
"""

import argparse
import hashlib
import importlib.util
import json
import pathlib
import subprocess
import sys

import fixture

ROOT = fixture.ROOT
sys.path.insert(0, str(ROOT / "scripts"))
import oracle_build  # noqa: E402


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=pathlib.Path, required=True)
    parser.add_argument("--spec", type=pathlib.Path, required=True)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--update", action="store_true")
    args = parser.parse_args()
    if args.check and args.update:
        parser.error("--check and --update are mutually exclusive")
    if not args.upstream.is_absolute() or not args.spec.is_absolute():
        parser.error("checkout paths must be absolute")
    revision = oracle_build.revision_guard(args.upstream)
    spec_pin = subprocess.check_output(
        ["git", "-C", str(ROOT), "rev-parse", "HEAD:upstream/nano-p4-spec"], text=True).strip()
    load("nano_session_spec_guard", ROOT / "scripts/check-spec-pin.py").revision_guard(
        args.spec, spec_pin)
    corpus = load("nano_session_corpus", ROOT / "P4SpecTecTest/Oracle/Nano/Certification/corpus.py")
    manifest = corpus.load(corpus.MANIFEST)
    normalize = load("nano_session_normalize", ROOT / "P4SpecTecTest/Oracle/P4/Replay/check.py")
    probe = pathlib.Path(__file__).with_name("probe.ml")
    executable = oracle_build.compile_probe(
        args.upstream, probe=probe, scratch=ROOT / ".artifacts/nano-session-oracle")
    values, index = [], {}

    def intern(value):
        value = fixture.strip_identities(normalize.normalize_locations(
            value, [(args.upstream, "$UPSTREAM"), (args.spec, "$NANO_SPEC")]))
        key = json.dumps(value, sort_keys=True, separators=(",", ":"))
        if key not in index:
            index[key] = len(values)
            values.append(value)
        return index[key]

    sessions = []
    for case in manifest["cases"]:
        if case["kind"] != "packet":
            continue
        stf_rel = case["source"]["path"]
        program_rel = stf_rel.removesuffix(".stf") + ".p4"
        stf, program = args.upstream / stf_rel, args.upstream / program_rel
        name = program_rel.removeprefix("nano-p4/testdata/").removesuffix(".p4")
        raw = subprocess.check_output(
            [str(executable), str(args.spec), str(args.upstream / "nano-p4/include"),
             str(program), str(stf)], text=True, timeout=300)
        lines = [line.removeprefix("OBSERVATION ") for line in raw.splitlines()
                 if line.startswith("OBSERVATION ")]
        if len(lines) != 1:
            raise SystemExit(f"missing or repeated observation for {name}")
        observed = fixture.strict_json(lines[0])
        init = observed["init"]
        if init.get("class") == "pass":
            init = {"class": "pass", "ctx": intern(init["ctx"]), "arch": intern(init["arch"])}
        decisions = iter(observed["decisions"])
        drives = []
        for drive in observed["drives"]:
            if drive["class"] == "pass":
                drives.append({"rx": drive["rx"], "class": "pass", "ctx": intern(drive["ctx"]),
                               "arch": intern(drive["arch"]),
                               "decision": intern(next(decisions)), "txs": drive["txs"]})
            else:
                drives.append({"rx": drive["rx"], "class": drive["class"]})
        if next(decisions, None) is not None:
            raise SystemExit(f"unmatched forwarding decision for {name}")
        sessions.append({
            "id": case["id"], "program": program_rel,
            "programSha256": hashlib.sha256(program.read_bytes()).hexdigest(),
            "stf": stf_rel, "stfSha256": hashlib.sha256(stf.read_bytes()).hexdigest(),
            "export": f"exports/programs/nano-p4/{name}.json",
            "stfResult": observed["stfResult"], "init": init, "drives": drives})
        print(f"[nano-session] {name}: {observed['stfResult']}, {len(drives)} packet(s)")
    bundle = {"schemaVersion": 1, "upstreamRevision": revision, "nanoSpecRevision": spec_pin,
              "mode": "AL", "cache": False, "det": False, "guard": False,
              "values": values, "sessions": sessions}
    fixture.validate(bundle)
    if args.check:
        expected, _ = fixture.read()
        if bundle != expected:
            raise SystemExit("session observations differ")
        print(f"[nano-session] {len(sessions)} exact-pin sessions match")
    elif args.update:
        fixture.write(bundle)
        print(f"[nano-session] wrote {len(sessions)} sessions, {len(values)} distinct values")
    else:
        print(json.dumps(bundle)[:2000])


if __name__ == "__main__":
    main()
