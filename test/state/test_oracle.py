#!/usr/bin/env python3
"""The compiled state oracle must reject corrupt or weakened observations."""

import copy
import json
import pathlib
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
BINARY = ROOT / ".lake/build/bin/check-state-oracle"


def main():
    original = json.loads((ROOT / "test/state/observed.json").read_bytes())
    mutations = []
    for change in ("missing", "duplicate", "reordered", "counter", "payload",
                   "scope", "unknown-status", "revision"):
        fixture = copy.deepcopy(original)
        cases = fixture["cases"]
        if change == "missing":
            cases.pop()
        elif change == "duplicate":
            cases.append(copy.deepcopy(cases[0]))
        elif change == "reordered":
            cases[0], cases[1] = cases[1], cases[0]
        elif change == "counter":
            cases[0]["counter"] += 1
        elif change == "payload":
            cases[0]["result"]["text"] = "incorrect"
        elif change == "scope":
            cases[0]["scope"] = "primitive"
        elif change == "unknown-status":
            cases[0]["result"]["status"] = "unknown"
        else:
            fixture["upstreamRevision"] = "0" * 40
        mutations.append((change, json.dumps(fixture).encode()))
    mutations.extend([("invalid-utf8", b'"\xff"'), ("invalid-json", b'{')])
    with tempfile.TemporaryDirectory(prefix="p4spectec-state-oracle-") as temporary:
        path = pathlib.Path(temporary) / "fixture.json"
        for name, payload in [("control", json.dumps(original).encode())] + mutations:
            path.write_bytes(payload)
            result = subprocess.run([str(BINARY), str(path)], cwd=ROOT,
                                    capture_output=True, text=True)
            if (result.returncode == 0) != (name == "control"):
                raise SystemExit(f"state oracle sensitivity failed: {name}\n"
                                 f"{result.stdout}{result.stderr}")
    print(f"[state-oracle] control passes; {len(mutations)} corrupt fixtures rejected")


if __name__ == "__main__":
    main()
