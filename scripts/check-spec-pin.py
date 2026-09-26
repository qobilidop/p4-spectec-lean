#!/usr/bin/env python3
"""Validate an exact specification repository, including ignored extra inputs."""

from pathlib import Path
import subprocess


def revision_guard(checkout, pin):
    """Require the exact repository root, revision and clean complete input tree.

    Reject all untracked entries conservatively, not only known source suffixes.
    Without exclude-standard, Git reports ignored entries too. This is a local
    provenance check, not protection against concurrent hostile filesystem edits.
    """
    checkout = Path(checkout)
    if not checkout.is_absolute():
        raise ValueError("specification checkout path must be absolute")
    root = checkout.resolve()

    def git(*args):
        return subprocess.check_output(["git", "-C", str(root), *args])

    toplevel = Path(git("rev-parse", "--show-toplevel").decode().strip()).resolve()
    if root != toplevel:
        raise ValueError("specification path is not the repository root")
    actual = git("rev-parse", "HEAD").decode().strip()
    if actual != pin:
        raise ValueError("specification revision differs from gitlink")
    subprocess.run(["git", "-C", str(root), "diff", "--exit-code", "HEAD"],
                   check=True, stdout=subprocess.DEVNULL)
    if git("ls-files", "--others", "-z"):
        raise ValueError("specification checkout contains untracked or ignored inputs")
    return actual
