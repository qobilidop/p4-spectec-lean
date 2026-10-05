#!/usr/bin/env python3
"""Keep a few generated modules committed as golden samples of an ignored generated library.

`golden-samples.py (--check|--update) <generated> <samples> [RELATIVE ...]`: every file
under `<samples>` is a byte-for-byte copy of the file at the same relative path under
`<generated>`. The manifest pins the whole library by digest, which shows no diff; the
samples make a generator change readable in review. `--update` refreshes the existing
samples and adds any named relative paths. Relative directory arguments are resolved
against the repository, whatever the working directory.
"""

import argparse
import pathlib
import sys


class SampleError(Exception):
    """An unreadable input or a sample that differs from the generated file."""


def plain_directory(path, what):
    """A real directory, reached through no symlink in its last component."""
    if path.is_symlink() or not path.is_dir():
        raise SampleError(f"{what} is not a plain directory: {path}")


def samples(directory):
    """The relative paths of the committed samples; no symlinks, files only."""
    plain_directory(directory, "samples directory")
    found = []
    for path in sorted(directory.rglob("*")):
        if path.is_symlink():
            raise SampleError(f"symlink among the samples: {path.relative_to(directory)}")
        if path.is_file():
            found.append(path.relative_to(directory))
    return found


def source(generated, relative):
    """The generated file a sample copies: a regular file inside the generated library,
    reached through no symlink."""
    relative = pathlib.PurePosixPath(relative)
    if relative.is_absolute() or ".." in relative.parts or not relative.parts:
        raise SampleError(f"not a path inside the generated library: {relative}")
    path = generated
    for part in relative.parts:
        path = path / part
        if path.is_symlink():
            raise SampleError(f"symlink in the generated library: {relative}")
    if not path.is_file():
        raise SampleError(f"no generated file for the sample: {relative} "
                          "(delete the sample if its module is no longer generated)")
    return path


def differences(generated, directory):
    """Every sample that is not a copy of its generated file; at least one sample."""
    plain_directory(generated, "generated library")
    found = samples(directory)
    if not found:
        raise SampleError(f"no samples under {directory}")
    return found, [str(relative) for relative in found
                   if source(generated, relative).read_bytes()
                   != (directory / relative).read_bytes()]


def update(generated, directory, added):
    """Copy the generated files over the existing samples and the newly named ones. Every
    source is read before anything is written."""
    plain_directory(generated, "generated library")
    if directory.is_symlink():
        raise SampleError(f"samples directory is a symlink: {directory}")
    existing = samples(directory) if directory.exists() else []
    chosen = sorted({pathlib.PurePosixPath(p.as_posix()) for p in existing}
                    | {pathlib.PurePosixPath(name) for name in added})
    if not chosen:
        raise SampleError("name at least one generated file to sample")
    contents = [(relative, source(generated, relative).read_bytes()) for relative in chosen]
    for relative, data in contents:
        target = directory / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    return len(contents)


def main(argv=None):
    """Return a nonzero exit unless every sample matches or the samples were written."""
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--update", action="store_true")
    parser.add_argument("generated", type=pathlib.Path)
    parser.add_argument("samples", type=pathlib.Path)
    parser.add_argument("added", nargs="*")
    parser.add_argument("--root", type=pathlib.Path,
                        default=pathlib.Path(__file__).resolve().parents[1])
    args = parser.parse_args(argv)
    generated, directory = args.root / args.generated, args.root / args.samples
    try:
        if args.update:
            count = update(generated, directory, args.added)
            print(f"[golden-samples] {count} samples written under {args.samples}")
            return 0
        if args.added:
            parser.error("--check takes no relative paths")
        found, differing = differences(generated, directory)
    except (SampleError, OSError) as error:
        print(f"[golden-samples] {error}", file=sys.stderr)
        return 1
    for name in differing:
        print(f"[golden-samples] differs from the generated file: {name}", file=sys.stderr)
    if differing:
        print("[golden-samples] regenerate, review the difference, then rerun with --update",
              file=sys.stderr)
        return 1
    print(f"[golden-samples] {len(found)} samples match the generated library")
    return 0


if __name__ == "__main__":
    sys.exit(main())
