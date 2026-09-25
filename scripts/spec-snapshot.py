#!/usr/bin/env python3
"""Pack deterministic spec snapshots, or verify and unpack them without OCaml."""

import argparse
import gzip
import hashlib
import io
import pathlib
import tempfile


def atomic_write(path, data):
    """Publish only a complete file, leaving an existing cache intact on failure."""
    with tempfile.NamedTemporaryFile(dir=path.parent, delete=False) as handle:
        temporary = pathlib.Path(handle.name)
        try:
            handle.write(data)
            handle.close()
            temporary.replace(path)
        finally:
            temporary.unlink(missing_ok=True)


def pack(path):
    """Preserve every input byte, without timestamps or filenames in the gzip header."""
    data = path.read_bytes()
    buffer = io.BytesIO()
    with gzip.GzipFile(filename="", mode="wb", fileobj=buffer,
                       compresslevel=9, mtime=0) as stream:
        stream.write(data)
    atomic_write(path.with_suffix(path.suffix + ".gz"), buffer.getvalue())
    digest = hashlib.sha256(data).hexdigest()
    atomic_write(path.with_suffix(path.suffix + ".sha256"),
                 f"{digest}  {path.name}\n".encode("ascii"))


def unpack(path):
    """Verify the snapshot before replacing the ignored working JSON."""
    data = gzip.decompress(path.with_suffix(path.suffix + ".gz").read_bytes())
    digest = hashlib.sha256(data).hexdigest()
    expected = path.with_suffix(path.suffix + ".sha256").read_text(encoding="ascii")
    if expected != f"{digest}  {path.name}\n":
        raise ValueError(f"checksum mismatch: {path}")
    atomic_write(path, data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["pack", "unpack"])
    parser.add_argument("json", type=pathlib.Path)
    args = parser.parse_args()
    try:
        (pack if args.mode == "pack" else unpack)(args.json)
    except (OSError, ValueError, EOFError) as error:
        parser.exit(1, f"[snapshot] {error}\n")
    print(f"[snapshot] {args.mode}: {args.json}")


if __name__ == "__main__":
    main()
