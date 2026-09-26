#!/usr/bin/env python3
"""Inventory the pinned positive seed corpus; this does not execute P4."""

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[2]
PREFIX = "p4c/testdata/p4_16_samples/"
MANIFEST = ROOT / "test/p4-corpus/manifest.json"


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


def inventory(p4c, upstream):
    exclusions = {}
    files = []
    for path in collect_files(upstream / "excludes/static", ".exclude"):
        name = path.relative_to(upstream).as_posix()
        data = path.read_bytes()
        files.append({"path": name, "sha256": digest(data)})
        for line, entry in exclude_lines(data):
            if entry.startswith(PREFIX):
                exclusions.setdefault(entry, []).append({"manifest": name, "line": line})
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
                      "exclusions": exclusions.get(name, [])})
    names = {case["path"] for case in cases}
    stale = [{"path": name, "exclusions": refs} for name, refs in sorted(exclusions.items())
             if name not in names]
    return {"cases": sorted(cases, key=lambda case: case["path"]),
            "exclusionFiles": sorted(files, key=lambda item: item["path"]),
            "staleExclusions": stale}


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


def is_digest(value, length):
    return (isinstance(value, str) and len(value) == length
            and all(char in "0123456789abcdef" for char in value))


def canonical_sample(value):
    return (isinstance(value, str) and value.startswith(PREFIX) and value.endswith(".p4")
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


def shard(manifest, index, total):
    validate_manifest(manifest)
    if type(total) is not int or type(index) is not int or not 0 <= index < total:
        raise ValueError("invalid shard selection")
    candidates = [case for case in manifest["cases"]
                  if case["collectorOmission"] is None and not case["exclusions"]]
    return [case for offset, case in enumerate(candidates) if offset % total == index]


def build(p4c, upstream):
    spec = importlib.util.spec_from_file_location("p4_oracle_check", ROOT / "test/p4-oracle/check.py")
    check = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(check)
    revision = check.load_export().revision_guard(upstream)
    check.p4c_pin_guard(upstream, p4c)
    pin = subprocess.check_output(["git", "-C", str(p4c), "rev-parse", "HEAD"], text=True).strip()
    data = inventory(p4c, upstream)
    snapshot = (ROOT / "exports/p4.al.json.sha256").read_text().split()[0]
    manifest = {"schemaVersion": 1, "upstreamRevision": revision, "p4cRevision": pin,
                "snapshotSha256": snapshot, **data, "counts": counts(data["cases"], data["staleExclusions"])}
    manifest["inventorySha256"] = digest(encode(manifest))
    validate_manifest(manifest)
    return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--p4c", type=Path, required=True)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if not args.p4c.is_absolute() or not args.upstream.is_absolute():
        parser.error("checkout paths must be absolute")
    manifest = build(args.p4c.resolve(), args.upstream.resolve())
    if args.check:
        committed = json.loads(MANIFEST.read_text())
        validate_manifest(committed)
        if committed != manifest:
            raise SystemExit("pinned corpus inventory differs from manifest")
    else:
        MANIFEST.write_bytes(encode(manifest) + b"\n")
    print(f"[p4-corpus] inventory only: {manifest['counts']}")


if __name__ == "__main__":
    main()
