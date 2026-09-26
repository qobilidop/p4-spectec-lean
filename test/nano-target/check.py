#!/usr/bin/env python3
"""Verify a pinned packet snapshot and replay it locally; no network or OCaml needed."""

import argparse
import pathlib
import subprocess
import fixture


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", type=pathlib.Path,
                        default=fixture.ROOT / ".lake/build/bin/check-nano-packet")
    args = parser.parse_args()
    _, data = fixture.read()
    subprocess.run([str(fixture.ROOT / ".lake/build/bin/check-nano-target")],
                   cwd=fixture.ROOT, timeout=30, check=True)
    subprocess.run([str(fixture.ROOT / ".lake/build/bin/check-nano-driver")],
                   cwd=fixture.ROOT, timeout=30, check=True)
    cache = fixture.ROOT / ".artifacts/nano-target/packet-observed.json"
    cache.parent.mkdir(parents=True, exist_ok=True)
    snapshot = fixture.load("packet_snapshot", fixture.ROOT / "scripts/spec-snapshot.py")
    snapshot.atomic_write(cache, data)
    subprocess.run([str(args.lean.resolve()), str(cache)], cwd=fixture.ROOT,
                   timeout=120, check=True)


if __name__ == "__main__":
    main()
