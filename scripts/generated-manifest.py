#!/usr/bin/env python3
"""Pin a generated library that is too large to commit by the digests of its files.

`generated-manifest.py (--check|--update) <Lib> <manifest.json>` covers `<Lib>.lean` and
every regular file under `<Lib>/`. A check requires the exact file set, sizes and SHA-256
digests the manifest records, so a generator change that alters the library shows up as a
changed manifest in review, as a diff of committed generated files would.
"""

import argparse
import hashlib
import json
import pathlib
import sys


class ManifestError(Exception):
    """An unreadable input or a library that differs from its manifest."""


def inventory(root, library):
    """Digest the root module and every file of the library directory, by relative path."""
    top = root / f"{library}.lean"
    directory = root / library
    if not top.is_file() or top.is_symlink():
        raise ManifestError(f"missing generated root module: {top.name}")
    if not directory.is_dir() or directory.is_symlink():
        raise ManifestError(f"missing generated library directory: {library}/")
    paths = [top]
    for path in sorted(directory.rglob("*")):
        if path.is_symlink():
            raise ManifestError(f"symlink in generated library: {path.relative_to(root)}")
        if path.is_file():
            paths.append(path)
    files = {}
    for path in paths:
        data = path.read_bytes()
        files[path.relative_to(root).as_posix()] = {
            "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest(),
        }
    return {"library": library, "files": dict(sorted(files.items()))}


def render(manifest):
    """One stable text form, so that an unchanged library rewrites nothing."""
    return json.dumps(manifest, indent=1, sort_keys=True) + "\n"


def differences(expected, actual):
    """Name every file that is missing, unexpected or changed."""
    if (not isinstance(expected, dict) or set(expected) != {"library", "files"}
            or not isinstance(expected["files"], dict)):
        raise ManifestError("malformed manifest")
    if expected["library"] != actual["library"]:
        return [f"manifest is for {expected['library']!r}, not {actual['library']!r}"]
    found = []
    for name in sorted(set(expected["files"]) | set(actual["files"])):
        if name not in actual["files"]:
            found.append(f"missing: {name}")
        elif name not in expected["files"]:
            found.append(f"not in the manifest: {name}")
        elif expected["files"][name] != actual["files"][name]:
            found.append(f"differs: {name}")
    return found


def main(argv=None):
    """Return a nonzero exit unless the library matches or the manifest was written."""
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--update", action="store_true")
    parser.add_argument("library")
    parser.add_argument("manifest", type=pathlib.Path)
    parser.add_argument("--root", type=pathlib.Path,
                        default=pathlib.Path(__file__).resolve().parents[1])
    args = parser.parse_args(argv)
    try:
        actual = inventory(args.root.resolve(), args.library)
        if args.update:
            args.manifest.write_text(render(actual), encoding="utf-8")
            print(f"[generated-manifest] {args.library}: {len(actual['files'])} files recorded")
            return 0
        expected = json.loads(args.manifest.read_text(encoding="utf-8"))
        found = differences(expected, actual)
    except (ManifestError, OSError, UnicodeError, json.JSONDecodeError) as error:
        print(f"[generated-manifest] {error}", file=sys.stderr)
        return 1
    for line in found[:20]:
        print(f"[generated-manifest] {line}", file=sys.stderr)
    if found:
        print(f"[generated-manifest] {args.library}: {len(found)} difference(s); regenerate, "
              "then rerun with --update if the change is intended", file=sys.stderr)
        return 1
    print(f"[generated-manifest] {args.library}: {len(actual['files'])} files match")
    return 0


if __name__ == "__main__":
    sys.exit(main())
