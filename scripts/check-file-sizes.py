#!/usr/bin/env python3
"""Reject tracked files over 5 MiB, in both the index and the working tree."""

import pathlib
import subprocess
import sys

LIMIT = 5 * 1024 * 1024


def oversized(root, limit=LIMIT):
    """Inspect indexed blobs even when the corresponding working file is smaller."""
    entries = subprocess.check_output(
        ["git", "-C", str(root), "ls-files", "--stage", "-z"]
    ).split(b"\0")
    files = []
    for entry in entries:
        if not entry:
            continue
        metadata, name = entry.split(b"\t", 1)
        mode, oid, _stage = metadata.split()
        if mode != b"160000":  # Submodule contents belong to their own repositories.
            files.append((oid, name.decode("utf-8", errors="surrogateescape")))
    sizes = subprocess.check_output(
        ["git", "-C", str(root), "cat-file", "--batch-check=%(objectsize)"],
        input=b"".join(oid + b"\n" for oid, _ in files),
    ).splitlines()
    found = []
    for (_, name), stored in zip(files, sizes, strict=True):
        path = root / name
        working = path.lstat().st_size if path.exists() or path.is_symlink() else 0
        size = max(int(stored), working)
        if size > limit:
            found.append((name, size))
    return found


def main():
    root = pathlib.Path(__file__).resolve().parents[1]
    failures = oversized(root)
    for name, size in failures:
        print(f"[file-size] {name}: {size} bytes exceeds {LIMIT}; "
              "use a small snapshot or a checksum-pinned external artifact")
    if not failures:
        print("[file-size] all tracked files are at most 5 MiB")
    return bool(failures)


if __name__ == "__main__":
    sys.exit(main())
