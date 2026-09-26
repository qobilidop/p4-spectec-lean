#!/usr/bin/env python3
"""Check reusable-library imports under `lake env`, using Lean's header parser."""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tomllib


REUSABLE = frozenset({"P4SpecTec", "P4Lib", "NanoP4Spec", "P4Spec"})
CONSUMERS = frozenset({"ExampleProofs", "P4SpecTecTest"})
HELPER = Path(__file__).with_name("library-imports.lean")


class BoundaryError(Exception):
    """An invalid dependency, configuration or unavailable checker input."""


def run(command, **kwargs):
    """Run a required subprocess and preserve failures as checker errors."""
    try:
        result = subprocess.run(command, capture_output=True, text=True, check=False, **kwargs)
    except (OSError, UnicodeError) as error:
        raise BoundaryError(f"cannot run {command[0]}: {error}") from error
    if result.returncode:
        raise BoundaryError(
            f"{command[0]} exited {result.returncode}:\n{result.stderr}{result.stdout}"
        )
    return result.stdout


def check_config(root):
    """Keep library names aligned with the source namespaces the policy checks."""
    with (root / "lakefile.toml").open("rb") as stream:
        config = tomllib.load(stream)
    if config.get("srcDir", ".") != ".":
        raise BoundaryError("package srcDir must be the repository root")
    targets = config.get("defaultTargets")
    if not isinstance(targets, list) or any(not isinstance(name, str) for name in targets):
        raise BoundaryError("defaultTargets must be a list of reusable library names")
    for name in targets:
        if name not in REUSABLE:
            raise BoundaryError(f"default target {name} is not a reusable library")
    if len(targets) != len(REUSABLE) or set(targets) != REUSABLE:
        raise BoundaryError("defaultTargets must include each reusable library exactly once")
    libraries = config.get("lean_lib", [])
    if not isinstance(libraries, list) or any(not isinstance(lib, dict) for lib in libraries):
        raise BoundaryError("lean_lib must be an array of library tables")
    for library in libraries:
        name = library.get("name")
        if not isinstance(name, str) or name not in REUSABLE | CONSUMERS:
            raise BoundaryError(f"lean_lib {name!r} needs an explicit boundary classification")
    for name in sorted(REUSABLE | CONSUMERS):
        matches = [lib for lib in libraries if lib.get("name") == name]
        if len(matches) != 1:
            raise BoundaryError(f"{name} must be registered exactly once as a lean_lib")
        library = matches[0]
        if library.get("srcDir", ".") != "." or library.get("roots", [name]) != [name]:
            raise BoundaryError(f"{name} must use its canonical source directory and root")
        if "globs" in library and library["globs"] != [name, f"{name}.+"]:
            raise BoundaryError(f"{name} globs must cover only its canonical namespace")
    if config.get("testDriver") != "P4SpecTecTest":
        raise BoundaryError("testDriver must be P4SpecTecTest")


def namespace(path, root):
    """Classify a local source by its top-level directory or root filename."""
    relative = path.relative_to(root)
    return relative.parts[0] if len(relative.parts) > 1 else relative.stem


def is_local(path, root):
    """Only follow this package's sources, excluding vendored package trees."""
    if not path.is_relative_to(root):
        return False
    return path.relative_to(root).parts[0] not in {".lake", "upstream", ".artifacts"}


def require_source(path):
    """Reject missing, non-file and unreadable dependency sources."""
    if not path.is_file():
        raise BoundaryError(f"missing source file: {path}")
    with path.open("rb") as stream:
        stream.read(1)


def source_inventory(root):
    """Include new modules and reject deleted tracked reusable sources."""
    sources = set()
    for name in REUSABLE:
        sources.add(root / f"{name}.lean")
        directory = root / name
        if directory.exists():
            def traversal_error(error):
                raise error
            for folder, _, filenames in os.walk(directory, onerror=traversal_error):
                sources.update(Path(folder) / filename for filename in filenames
                               if filename.endswith(".lean"))
    tracked = run(["git", "-C", str(root), "ls-files", "-z", "--", "*.lean"])
    for filename in tracked.split("\0"):
        if filename and namespace(root / filename, root) in REUSABLE:
            sources.add(root / filename)
    for path in sources:
        require_source(path)
    return sources


def parse_dependencies(sources, root):
    """Parse a batch with Lean; validate the complete output before using it."""
    require_source(HELPER)
    environment = os.environ.copy()
    environment["LEAN_SRC_PATH"] = os.pathsep.join(
        [str(root), environment.get("LEAN_SRC_PATH", "")]
    )
    output = run(
        ["lean", "--run", str(HELPER), *map(str, sorted(sources))],
        cwd=root, env=environment,
    )
    try:
        rows = json.loads(output)
        if not isinstance(rows, list):
            raise ValueError("expected an array")
        graph = {}
        for row in rows:
            if not isinstance(row, dict) or set(row) != {"source", "dependencies"}:
                raise ValueError("invalid dependency row")
            if not isinstance(row["source"], str) or not isinstance(row["dependencies"], list):
                raise ValueError("invalid source/dependency types")
            if any(not isinstance(dep, str) or not Path(dep).is_absolute()
                   for dep in row["dependencies"]):
                raise ValueError("invalid dependency path")
            source = Path(row["source"])
            if source in graph or source not in sources:
                raise ValueError("duplicate or unexpected source")
            graph[source] = {Path(dep).resolve() for dep in row["dependencies"]}
        if set(graph) != sources:
            raise ValueError("missing dependency rows")
    except (ValueError, TypeError, KeyError) as error:
        raise BoundaryError(f"invalid Lean parser output: {error}") from error
    for dependencies in graph.values():
        for dependency in dependencies:
            require_source(dependency)
    return graph


def check_graph(graph, starts, root):
    """Reject any path from a reusable module to an example or test module."""
    for start in sorted(starts):
        pending = [(start, [start])]
        seen = set()
        while pending:
            source, chain = pending.pop()
            if source in seen:
                continue
            seen.add(source)
            if namespace(source, root) in CONSUMERS:
                display = " -> ".join(str(path.relative_to(root)) for path in chain)
                raise BoundaryError(f"reusable library imports a consumer: {display}")
            if source not in graph:
                raise BoundaryError(f"missing parsed dependency input: {source}")
            pending.extend((dep, chain + [dep]) for dep in sorted(graph[source])
                           if is_local(dep, root))


def check(root, parser=parse_dependencies):
    """Validate configuration and the local dependency closure of reusable sources."""
    check_config(root)
    starts = source_inventory(root)
    graph = {}
    pending = starts
    while pending:
        batch = parser(pending, root)
        graph.update(batch)
        pending = {dependency for dependencies in batch.values() for dependency in dependencies
                   if is_local(dependency, root) and dependency not in graph
                   and namespace(dependency, root) not in CONSUMERS}
    check_graph(graph, starts, root)


def main():
    """Return a nonzero exit on any policy violation or unavailable input."""
    arguments = argparse.ArgumentParser(description=__doc__)
    arguments.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = arguments.parse_args()
    try:
        check(args.root.resolve())
    except (BoundaryError, OSError, UnicodeError, ValueError, TypeError) as error:
        print(f"library boundaries: {error}", file=sys.stderr)
        return 1
    print("library boundaries: reusable libraries do not import examples or tests")
    return 0


if __name__ == "__main__":
    sys.exit(main())
