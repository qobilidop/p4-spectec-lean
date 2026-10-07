#!/usr/bin/env python3
"""Inventory the pinned p4c corpora, positive samples and error tests; this does not execute P4.

The positive inventory (`manifest.json`) is the shard campaign's and the sweeps' denominator.
The error inventory (`errors.json`) lists p4c's `p4_16_errors` programs, which upstream runs
expecting every one it does not exclude to be rejected; it is a separate manifest so that the
positive identity, and every cache and campaign record keyed by it, is unchanged.
"""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[4]
PREFIX = "p4c/testdata/p4_16_samples/"
MANIFEST = ROOT / "P4SpecTecTest/Oracle/P4/Corpus/manifest.json"
ERRORS_PREFIX = "p4c/testdata/p4_16_errors/"
ERRORS_MANIFEST = ROOT / "P4SpecTecTest/Oracle/P4/Corpus/errors.json"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return json.dumps(value, ensure_ascii=True, sort_keys=True,
                      separators=(",", ":")).encode("utf-8")


def collect_files(directory, suffix, skip_include=True):
    """Mirror Util.Filesys.collect_files, retaining symlink path identity."""
    result = []
    for path in sorted(directory.iterdir(), key=lambda entry: entry.name):
        if path.is_dir() and (path.name != "include" or not skip_include):
            result.extend(collect_files(path, suffix, skip_include))
        elif str(path).endswith(suffix):
            result.append(path)
    return result


def exclude_lines(data):
    """Mirror OCaml input_line and its literal leading-comment predicate."""
    lines = data.decode("utf-8").split("\n")
    if lines[-1] == "":
        lines.pop()
    return [(index, line) for index, line in enumerate(lines, 1)
            if not line.startswith("#")]


def exclusions(upstream, prefix):
    """Every static exclusion reference under `prefix`, with its manifest and line, and
    the digests of every exclusion file."""
    references = {}
    files = []
    for path in collect_files(upstream / "excludes/static", ".exclude"):
        name = path.relative_to(upstream).as_posix()
        data = path.read_bytes()
        files.append({"path": name, "sha256": digest(data)})
        for line, entry in exclude_lines(data):
            if entry.startswith(prefix):
                references.setdefault(entry, []).append({"manifest": name, "line": line})
    return references, sorted(files, key=lambda item: item["path"])


def inventory(p4c, upstream):
    references, files = exclusions(upstream, PREFIX)
    cases = []
    sample_root = p4c / "testdata/p4_16_samples"
    collected = set(collect_files(sample_root, ".p4"))
    for path in collect_files(sample_root, ".p4", skip_include=False):
        if not path.is_file():
            raise ValueError(f"unresolved or non-file sample: {path}")
        name = "p4c/" + path.relative_to(p4c).as_posix()
        cases.append({"path": name, "sha256": digest(path.read_bytes()),
                      "collectorOmission": None if path in collected else "include-directory",
                      "symlink": path.readlink().as_posix() if path.is_symlink() else None,
                      "exclusions": references.get(name, [])})
    names = {case["path"] for case in cases}
    stale = [{"path": name, "exclusions": refs} for name, refs in sorted(references.items())
             if name not in names]
    return {"cases": sorted(cases, key=lambda case: case["path"]),
            "exclusionFiles": files, "staleExclusions": stale}


def inventory_errors(p4c, upstream):
    """p4c's error tests: a flat directory of programs upstream runs with `-neg`, each with
    its digest and its negative exclusion references. Upstream collects recursively, so a
    nested directory would be a different set: it is an error, not a smaller denominator."""
    references, files = exclusions(upstream, ERRORS_PREFIX)
    root = p4c / "testdata/p4_16_errors"
    if root.is_symlink() or not root.is_dir():
        raise ValueError("missing p4_16_errors directory")
    nested = sorted(entry.name for entry in root.iterdir() if entry.is_dir())
    if nested:
        raise ValueError(f"nested p4_16_errors directories: {nested}")
    cases = []
    for path in collect_files(root, ".p4", skip_include=False):
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"error test is not a regular file: {path}")
        name = "p4c/" + path.relative_to(p4c).as_posix()
        cases.append({"path": name, "sha256": digest(path.read_bytes()),
                      "exclusions": references.get(name, [])})
    names = {case["path"] for case in cases}
    stale = [{"path": name, "exclusions": refs} for name, refs in sorted(references.items())
             if name not in names]
    return {"cases": sorted(cases, key=lambda case: case["path"]),
            "exclusionFiles": files, "staleExclusions": stale}


def validate_manifest(manifest):
    """Reject a malformed inventory rather than silently changing its denominator."""
    if (not isinstance(manifest, dict) or set(manifest) != {
            "schemaVersion", "upstreamRevision", "p4cRevision", "snapshotSha256",
            "cases", "exclusionFiles", "staleExclusions", "counts", "inventorySha256"}
            or type(manifest["schemaVersion"]) is not int or manifest["schemaVersion"] != 1):
        raise ValueError("malformed inventory envelope")
    for key, length in (("upstreamRevision", 40), ("p4cRevision", 40),
                        ("snapshotSha256", 64), ("inventorySha256", 64)):
        if not is_digest(manifest[key], length):
            raise ValueError(f"malformed {key}")
    cases = manifest["cases"]
    if not isinstance(cases, list) or not cases:
        raise ValueError("empty/malformed case manifest")
    names = []
    for case in cases:
        if (not isinstance(case, dict) or set(case) != {
                "path", "sha256", "symlink", "exclusions", "collectorOmission"}
                or not canonical_sample(case["path"]) or not is_digest(case["sha256"], 64)
                or (case["symlink"] is not None and not isinstance(case["symlink"], str))
                or case["collectorOmission"] != (
                    "include-directory" if "include" in case["path"].split("/")[3:-1]
                    else None)):
            raise ValueError("malformed case")
        validate_refs(case["exclusions"])
        names.append(case["path"])
    if names != sorted(set(names)):
        raise ValueError("case identities duplicated or reordered")
    files = manifest["exclusionFiles"]
    if (not isinstance(files, list) or not files
            or any(not isinstance(item, dict) or set(item) != {"path", "sha256"}
                   or not exclusion_path(item["path"]) or not is_digest(item["sha256"], 64)
                   for item in files)):
        raise ValueError("malformed exclusion files")
    file_names = [item["path"] for item in files]
    if file_names != sorted(set(file_names)):
        raise ValueError("exclusion files duplicated or reordered")
    stale = manifest["staleExclusions"]
    if not isinstance(stale, list):
        raise ValueError("malformed stale exclusions")
    for entry in stale:
        if (not isinstance(entry, dict) or set(entry) != {"path", "exclusions"}
                or not canonical_sample(entry["path"]) or entry["path"] in names
                or not entry["exclusions"]):
            raise ValueError("malformed stale exclusion")
        validate_refs(entry["exclusions"])
    stale_names = [entry["path"] for entry in stale]
    if stale_names != sorted(set(stale_names)):
        raise ValueError("stale exclusions duplicated or reordered")
    for item in cases + stale:
        if any(ref["manifest"] not in file_names for ref in item["exclusions"]):
            raise ValueError("unknown exclusion provenance")
    expected_counts = counts(cases, stale)
    if (not isinstance(manifest["counts"], dict)
            or set(manifest["counts"]) != set(expected_counts)
            or any(type(value) is not int for value in manifest["counts"].values())
            or manifest["counts"] != expected_counts):
        raise ValueError("inventory counts differ")
    payload = {key: value for key, value in manifest.items() if key != "inventorySha256"}
    if manifest["inventorySha256"] != digest(encode(payload)):
        raise ValueError("inventory digest differs")


def validate_errors(manifest):
    """Reject a malformed error inventory rather than silently changing its denominator."""
    if (not isinstance(manifest, dict) or set(manifest) != {
            "schemaVersion", "upstreamRevision", "p4cRevision", "snapshotSha256",
            "cases", "exclusionFiles", "staleExclusions", "counts", "inventorySha256"}
            or type(manifest["schemaVersion"]) is not int or manifest["schemaVersion"] != 1):
        raise ValueError("malformed error inventory envelope")
    for key, length in (("upstreamRevision", 40), ("p4cRevision", 40),
                        ("snapshotSha256", 64), ("inventorySha256", 64)):
        if not is_digest(manifest[key], length):
            raise ValueError(f"malformed {key}")
    cases = manifest["cases"]
    if not isinstance(cases, list) or not cases:
        raise ValueError("empty/malformed error case manifest")
    names = []
    for case in cases:
        if (not isinstance(case, dict) or set(case) != {"path", "sha256", "exclusions"}
                or not canonical_error(case["path"]) or not is_digest(case["sha256"], 64)):
            raise ValueError("malformed error case")
        validate_refs(case["exclusions"])
        names.append(case["path"])
    if names != sorted(set(names)):
        raise ValueError("error case identities duplicated or reordered")
    files = manifest["exclusionFiles"]
    if (not isinstance(files, list) or not files
            or any(not isinstance(item, dict) or set(item) != {"path", "sha256"}
                   or not exclusion_path(item["path"]) or not is_digest(item["sha256"], 64)
                   for item in files)):
        raise ValueError("malformed exclusion files")
    file_names = [item["path"] for item in files]
    if file_names != sorted(set(file_names)):
        raise ValueError("exclusion files duplicated or reordered")
    stale = manifest["staleExclusions"]
    if not isinstance(stale, list):
        raise ValueError("malformed stale exclusions")
    for entry in stale:
        if (not isinstance(entry, dict) or set(entry) != {"path", "exclusions"}
                or not canonical_error(entry["path"]) or entry["path"] in names
                or not entry["exclusions"]):
            raise ValueError("malformed stale exclusion")
        validate_refs(entry["exclusions"])
    stale_names = [entry["path"] for entry in stale]
    if stale_names != sorted(set(stale_names)):
        raise ValueError("stale exclusions duplicated or reordered")
    for item in cases + stale:
        if any(ref["manifest"] not in file_names for ref in item["exclusions"]):
            raise ValueError("unknown exclusion provenance")
    expected_counts = error_counts(cases, stale)
    if (not isinstance(manifest["counts"], dict) or manifest["counts"] != expected_counts
            or any(type(value) is not int for value in manifest["counts"].values())):
        raise ValueError("error inventory counts differ")
    payload = {key: value for key, value in manifest.items() if key != "inventorySha256"}
    if manifest["inventorySha256"] != digest(encode(payload)):
        raise ValueError("error inventory digest differs")


def is_digest(value, length):
    return (isinstance(value, str) and len(value) == length
            and all(char in "0123456789abcdef" for char in value))


def canonical_sample(value):
    return (isinstance(value, str) and value.startswith(PREFIX) and value.endswith(".p4")
            and all(part not in ("", ".", "..") for part in value.split("/")))


def canonical_error(value):
    return (isinstance(value, str) and value.startswith(ERRORS_PREFIX) and value.endswith(".p4")
            and len(value.split("/")) == 4
            and all(part not in ("", ".", "..") for part in value.split("/")))


def exclusion_path(value):
    return (isinstance(value, str) and value.startswith("excludes/static/")
            and value.endswith(".exclude")
            and all(part not in ("", ".", "..") for part in value.split("/")))


def validate_refs(refs):
    if (not isinstance(refs, list)
            or any(not isinstance(ref, dict) or set(ref) != {"manifest", "line"}
                   or not exclusion_path(ref["manifest"])
                   or type(ref["line"]) is not int or ref["line"] <= 0 for ref in refs)):
        raise ValueError("malformed exclusion provenance")


def counts(cases, stale):
    collected = [case for case in cases if case["collectorOmission"] is None]
    excluded = sum(bool(case["exclusions"]) for case in collected)
    return {"paths": len(cases), "symlinks": sum(case["symlink"] is not None for case in cases),
            "collectorPaths": len(collected), "collectorOmitted": len(cases) - len(collected),
            "excluded": excluded, "candidates": len(collected) - excluded,
            "positiveReferences": sum(len(case["exclusions"]) for case in cases + stale),
            "staleReferences": sum(len(entry["exclusions"]) for entry in stale)}


def error_counts(cases, stale):
    excluded = sum(bool(case["exclusions"]) for case in cases)
    return {"paths": len(cases), "excluded": excluded, "candidates": len(cases) - excluded,
            "negativeReferences": sum(len(case["exclusions"]) for case in cases + stale),
            "staleReferences": sum(len(entry["exclusions"]) for entry in stale)}


def error_candidates(manifest):
    """The error tests upstream does not exclude, in manifest order."""
    validate_errors(manifest)
    return [case for case in manifest["cases"] if not case["exclusions"]]


def shard(manifest, index, total):
    validate_manifest(manifest)
    if type(total) is not int or type(index) is not int or not 0 <= index < total:
        raise ValueError("invalid shard selection")
    candidates = [case for case in manifest["cases"]
                  if case["collectorOmission"] is None and not case["exclusions"]]
    return [case for offset, case in enumerate(candidates) if offset % total == index]


def pins(p4c, upstream):
    """The guarded upstream revision, p4c pin and snapshot digest every manifest records."""
    spec = importlib.util.spec_from_file_location("p4_oracle_check", ROOT / "P4SpecTecTest/Oracle/P4/Replay/check.py")
    check = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(check)
    revision = check.load_export().revision_guard(upstream)
    check.p4c_pin_guard(upstream, p4c)
    pin = subprocess.check_output(["git", "-C", str(p4c), "rev-parse", "HEAD"], text=True).strip()
    snapshot = (ROOT / "exports/p4.al.json.sha256").read_text().split()[0]
    return {"schemaVersion": 1, "upstreamRevision": revision, "p4cRevision": pin,
            "snapshotSha256": snapshot}


def build(p4c, upstream):
    data = inventory(p4c, upstream)
    manifest = {**pins(p4c, upstream), **data,
                "counts": counts(data["cases"], data["staleExclusions"])}
    manifest["inventorySha256"] = digest(encode(manifest))
    validate_manifest(manifest)
    return manifest


def build_errors(p4c, upstream):
    data = inventory_errors(p4c, upstream)
    manifest = {**pins(p4c, upstream), **data,
                "counts": error_counts(data["cases"], data["staleExclusions"])}
    manifest["inventorySha256"] = digest(encode(manifest))
    validate_errors(manifest)
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p4c", type=Path, required=True)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not args.p4c.is_absolute() or not args.upstream.is_absolute():
        parser.error("checkout paths must be absolute")
    p4c, upstream = args.p4c.resolve(), args.upstream.resolve()
    for label, path, built, validate in (
            ("corpus", MANIFEST, build(p4c, upstream), validate_manifest),
            ("errors", ERRORS_MANIFEST, build_errors(p4c, upstream), validate_errors)):
        if args.check:
            committed = json.loads(path.read_text())
            validate(committed)
            if committed != built:
                raise SystemExit(f"pinned {label} inventory differs from {path.name}")
        else:
            path.write_bytes(encode(built) + b"\n")
        print(f"[p4-corpus] {label} inventory only: {built['counts']}")


if __name__ == "__main__":
    main()
