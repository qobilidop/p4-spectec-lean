"""Shared pinned-source validation and OCaml probe build plumbing.

Suites retain their own requests, observations and domain-specific link lists.
Keyed callers must hold their build lock across workspace validation and build.
"""

import os
from pathlib import Path
import shutil
import stat
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PATCH = "upstream/patches/0001-json-export.patch"
PATCHED_FILES = (
    "p4spec/bin/main.ml", "p4spec/bin/nano.ml",
    "p4spec/lib/lang/al/ast.ml", "p4spec/lib/lang/il/ast.ml",
)
LIBRARIES = [
    ("util", "util"), ("cache", "cache"), ("domain", "domain"),
    ("diagnostic", "diagnostic"), ("lang", "lang"),
    ("frontend", "frontend"),
    ("runtime/error_runtime", "error_runtime"),
    ("runtime/type", "type"), ("runtime/value", "value"),
    ("runtime/dynamic-runner", "dynamic_runner"),
    ("runtime/dynamic", "dynamic"),
    ("runtime/dynamic-al", "dynamic_al"),
    ("runtime/dynamic-sl", "dynamic_sl"),
    ("runtime/dynamic-pl", "dynamic_pl"),
    ("runtime/static", "static"), ("runtime/prose", "prose"),
    ("runtime/sim", "sim"), ("runtime", "runtime"),
    ("interface/builtin", "builtin"), ("pass", "pass"),
    ("interface/nano", "nano"), ("interface/p4", "p4"),
    ("interface/spectec", "spectec"), ("interface", "interface"),
    ("coverage/instr", "instr"),
    ("coverage/dangling", "dangling"),
    ("interp/inst", "inst"),
    ("interp/interp-common", "interp_common"),
    ("interp/interp-al", "interp_al"),
    ("interp/interp-sl", "interp_sl"),
    ("interp/interp-pl", "interp_pl"), ("interp", "interp"),
    ("runner", "runner"), ("stf", "stf"),
    ("coverage", "coverage"),
    ("backend-sim", "backend_sim"),
]


def revision_guard(upstream: Path) -> str:
    entry = subprocess.check_output(
        ["git", "-C", str(ROOT), "ls-files", "--stage", "--", "upstream/p4-spectec"],
        text=True,
    ).split()
    revision = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True,
    ).strip()
    root = subprocess.check_output(
        ["git", "-C", str(upstream), "rev-parse", "--show-toplevel"],
        text=True,
    ).strip()
    if root != str(upstream) or len(entry) != 4 or entry[:2] != ["160000", revision]:
        raise SystemExit("upstream must be a repository root at the indexed gitlink pin")
    expected_patch = subprocess.check_output(
        ["git", "-C", str(ROOT), "show", f"HEAD:{PATCH}"])
    actual_patch = subprocess.check_output(
        ["git", "-C", str(upstream), "diff", "HEAD", "--no-ext-diff",
         "--no-color", "--binary"])
    status = subprocess.check_output(
        ["git", "-C", str(upstream), "status", "--short", "--untracked-files=all"],
        text=True,
    ).splitlines()
    if actual_patch != expected_patch or status != [f" M {path}" for path in PATCHED_FILES]:
        raise SystemExit("upstream source differs from the exact committed export patch")
    return revision


def validate_probe_workspace(workspace: Path) -> None:
    """Never copy/link over symlinks, special files or outside hardlink aliases.

    The keyed caller holds its build lock across validation and compilation.
    This checks persisted cache entries, not hostile concurrent replacement by
    an uncooperative process with write access to the same directory.
    """
    if not stat.S_ISDIR(workspace.lstat().st_mode):
        raise SystemExit("probe workspace must be a real directory")
    for path in workspace.iterdir():
        info = path.lstat()
        if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
            raise SystemExit("probe workspace entries must be single-link regular files")


def compile_probe(
        upstream: Path, *, probe: Path, scratch: Path,
        libraries=LIBRARIES, packages: str =
        "core,core_unix,core_unix.sys_unix,bignum.bigint,yojson,"
        "ppx_deriving_yojson.runtime,uucp,uuseg,uutf,str,menhirLib",
        workspace_key: str | None = None, rebuild: bool = True) -> Path:
    """Build a caller-selected probe without sharing mutable suite configuration."""
    if workspace_key is not None and (
            not isinstance(workspace_key, str) or len(workspace_key) != 64
            or any(char not in "0123456789abcdef" for char in workspace_key)):
        raise SystemExit("probe workspace key must be a lowercase SHA-256")
    if rebuild and subprocess.run(["dune", "build", "p4spec/bin/main.exe"],
                                  cwd=upstream).returncode != 0:
        raise SystemExit("failed to rebuild pinned upstream source")
    build = upstream / "_build/default/p4spec/lib"
    workspace = scratch / (str(os.getpid()) if workspace_key is None else workspace_key)
    workspace.mkdir(parents=True, exist_ok=True)
    validate_probe_workspace(workspace)
    source = workspace / "probe.ml"
    shutil.copyfile(probe, source)
    command = [
        "ocamlfind", "ocamlopt", "-linkpkg", "-package",
        packages,
    ]
    for directory, name in libraries:
        objects = build / directory / f".{name}.objs"
        command += ["-I", str(objects / "byte"), "-I", str(objects / "native")]
    command += [str(build / directory / f"{name}.cmxa") for directory, name in libraries]
    executable = workspace / "probe"
    command += [str(source), "-o", str(executable)]
    validate_probe_workspace(workspace)
    if subprocess.run(command, cwd=ROOT).returncode != 0:
        raise SystemExit("failed to compile pinned full-P4 AL oracle probe")
    return executable
