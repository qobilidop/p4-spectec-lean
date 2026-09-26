#!/usr/bin/env python3
"""Check tracked source text, failing on missing or unreadable inputs."""

from pathlib import Path
import os
import re
import subprocess


SUFFIXES = {".lean", ".md", ".sh", ".toml", ".nix", ".yml", ".yaml", ".py"}


def check(root):
    """Return diagnostics for the working contents of indexed text files."""
    names = subprocess.check_output(["git", "-C", str(root), "ls-files", "-z"])
    errors = []
    for raw in names.split(b"\0"):
        if not raw:
            continue
        name = os.fsdecode(raw)
        path = root / name
        if path.suffix not in SUFFIXES:
            continue
        try:
            data = path.read_bytes()
            text = data.decode("utf-8")
        except (OSError, UnicodeError) as error:
            errors.append(f"cannot read {name!r}: {error}")
            continue
        if data and not data.endswith(b"\n"):
            errors.append(f"no final newline: {name!r}")
        for number, line in enumerate(text.split("\n"), 1):
            location = f"{name!r}:{number}"
            if line and line[-1].isspace():
                errors.append(f"trailing whitespace: {location}")
            if path.suffix != ".lean":
                continue
            if len(line) > 100 and not re.search(r"https?://", line):
                errors.append(f"line over 100 characters: {location}")
            if line == "import Lean" and not name.startswith("scripts/"):
                errors.append(f"bare 'import Lean': {location}")
    return errors


def main():
    """Run from any directory; the script location selects the repository."""
    root = Path(__file__).resolve().parents[1]
    try:
        errors = check(root)
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"[check-text] cannot enumerate tracked files: {error}")
        return 1
    for error in errors:
        print(f"[check-text] {error}")
    return int(bool(errors))


if __name__ == "__main__":
    raise SystemExit(main())
