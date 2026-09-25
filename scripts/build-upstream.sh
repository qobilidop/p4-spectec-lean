#!/usr/bin/env bash
# Build P4-SpecTec at the pinned submodule commit with our patches applied,
# and print the path of the resulting `p4spectec` binary.
#
# Not implemented yet. Milestone M1 fills this in: create the opam switch
# at OPAM_REPO_COMMIT, apply upstream/patches/*.patch in name order, run
# `make build` in upstream/p4-spectec, and record a stamp with the commit
# and a digest of the patches so a changed patch rebuilds.
set -euo pipefail

# The opam package universe is pinned so every machine resolves the same
# OCaml dependency versions. Bump together with the submodule when its
# build needs newer packages.
OPAM_REPO=https://github.com/ocaml/opam-repository
OPAM_REPO_COMMIT=TODO-pin-at-M1
SWITCH=5.1.0

echo "build-upstream: not implemented yet (docs/design.md, milestone M1)" >&2
exit 2
