#!/usr/bin/env python3
"""Both differential legs reject invalid transport and corrupt expectations."""

import json
import pathlib
import shutil
import subprocess
import tempfile

ROOT = pathlib.Path(__file__).resolve().parents[2]
CORPUS = ROOT / "exports/programs/nano-p4"


def main():
    positives = [p for p in sorted(CORPUS.rglob("*.verdict"))
                 if p.read_text().strip() == "pass"
                 and p.with_suffix(".outputs.json").is_file()]
    if not positives:
        raise SystemExit("no positive program with expected outputs")
    source = positives[0].with_suffix(".json")
    # Corrupt only an ignored source filename in an otherwise valid program.
    # A top-level JSON string would fail the IL schema even after lossy decoding.
    payload = json.loads(source.read_bytes())
    marker = "p4spectec-json-transport-marker"
    payload["at"]["left"]["file"] = marker
    valid = json.dumps(payload).encode()
    if valid.count(marker.encode()) != 1:
        raise SystemExit("transport marker is not unique")
    with tempfile.TemporaryDirectory(prefix="p4spectec-json-boundary-") as temporary:
        directory = pathlib.Path(temporary)
        invalid = directory / "invalid.json"
        program = directory / "program.json"
        shutil.copyfile(source, program)
        expected = program.with_suffix(".outputs.json")
        for executable in ("nano-p4-run", "nano-p4-interp"):
            binary = ROOT / ".lake/build/bin" / executable
            invalid.write_bytes(valid)
            run = subprocess.run([str(binary), str(invalid)], cwd=ROOT,
                                 capture_output=True, text=True)
            if run.returncode != 0 or run.stdout.strip() != f"{invalid} pass":
                raise SystemExit(f"{executable}: transport control program did not pass")
            for malformed_text in (b'\xff', b'\\uD800', b'\\uDC00'):
                invalid.write_bytes(valid.replace(marker.encode(), malformed_text))
                run = subprocess.run([str(binary), str(invalid)], cwd=ROOT,
                                     capture_output=True, text=True)
                if run.returncode != 0 or run.stdout.strip() != f"{invalid} decode-error":
                    raise SystemExit(f"{executable}: malformed text was not a decode error")
            for malformed in (b'"\xff"', b'{not json', b'null'):
                expected.write_bytes(malformed)
                run = subprocess.run([str(binary), str(program)], cwd=ROOT,
                                     capture_output=True, text=True)
                if run.returncode == 0:
                    raise SystemExit(f"{executable}: corrupt expected output was ignored")
    print("[json-boundary] both legs reject invalid inputs and corrupt expectations")


if __name__ == "__main__":
    main()
