#!/usr/bin/env bash
# Restore only p4c's P4 1.6 sample, include and sample symlink-target
# trees at P4-SpecTec's nested gitlink. Run in the default Nix shell
# after initializing the containing upstream/p4-spectec submodule
# (without --recursive).
set -euo pipefail

script_dir="$(realpath "$(dirname "$0")")"
root="$(git -C "$script_dir" rev-parse --show-toplevel)"
up="$root/upstream/p4-spectec"

fail() { printf '[fetch-p4c] %s\n' "$*" >&2; exit 1; }

[[ $# -eq 0 ]] || fail 'usage: fetch-p4c.sh'
[[ "$script_dir" == "$root/scripts" ]] || fail 'script is outside its repository'
[[ -e "$up/.git" ]] || fail 'initialize upstream/p4-spectec first'
[[ "$(git -C "$up" rev-parse --show-toplevel)" == "$up" ]] \
  || fail 'upstream path is not a Git checkout root'

up_entry="$(git -C "$root" ls-tree HEAD -- upstream/p4-spectec)"
up_pattern='^160000[[:space:]]commit[[:space:]]([0-9a-f]{40})[[:space:]]upstream/p4-spectec$'
[[ "$up_entry" =~ $up_pattern ]] \
  || fail 'top-level upstream gitlink is missing'
[[ "$(git -C "$up" rev-parse HEAD)" == "${BASH_REMATCH[1]}" ]] \
  || fail 'upstream checkout differs from its pinned gitlink'

p4c_entry="$(git -C "$up" ls-tree HEAD -- p4c)"
[[ "$p4c_entry" =~ ^160000[[:space:]]commit[[:space:]]([0-9a-f]{40})[[:space:]]p4c$ ]] \
  || fail 'p4c gitlink is missing at the pinned upstream commit'
pin="${BASH_REMATCH[1]}"
url="$(git -C "$up" config --blob HEAD:.gitmodules --get submodule.p4c.url)"
[[ "$url" == https://* ]] || fail 'pinned p4c submodule URL is not HTTPS'

artifact_root="$root/.artifacts"
dest="$artifact_root/p4c"
[[ ! -L "$artifact_root" ]] || fail 'refusing symlink artifact root'
mkdir -p "$artifact_root"
[[ ! -L "$dest" ]] || fail 'refusing symlink artifact destination'

if [[ -e "$dest" ]]; then
  [[ -d "$dest/.git" || -f "$dest/.git" ]] \
    || fail 'artifact destination exists but is not a Git checkout'
  [[ "$(git -C "$dest" rev-parse --show-toplevel)" == "$dest" ]] \
    || fail 'artifact destination is not its Git checkout root'
  [[ "$(git -C "$dest" remote get-url origin)" == "$url" ]] \
    || fail 'artifact checkout has a different origin URL'
  [[ -z "$(git -C "$dest" status --porcelain=v1 --untracked-files=all)" ]] \
    || fail 'artifact checkout is dirty'
  [[ "$(git -C "$dest" rev-parse --verify HEAD)" == "$pin" ]] \
    || fail 'artifact checkout is at a different commit'
else
  git init -q "$dest"
  git -C "$dest" remote add origin "$url"
  # Set the sparse paths before checkout so unrelated p4c blobs stay absent.
  git -C "$dest" sparse-checkout set p4include testdata/p4_16_samples \
    backends/ubpf/tests/testdata
  git -C "$dest" fetch --depth=1 --filter=blob:none origin "$pin"
  git -C "$dest" checkout --detach "$pin"
fi

git -C "$dest" sparse-checkout set p4include testdata/p4_16_samples \
  backends/ubpf/tests/testdata
[[ "$(git -C "$dest" rev-parse HEAD)" == "$pin" ]] || fail 'p4c HEAD moved from pin'
[[ -f "$dest/p4include/core.p4" ]] || fail 'p4include/core.p4 is missing'
[[ -d "$dest/testdata/p4_16_samples" ]] || fail 'p4_16_samples is missing'
broken_links="$(find -L "$dest/testdata/p4_16_samples" -type l -print)" \
  || fail 'could not inspect p4c sample symlinks'
[[ -z "$broken_links" ]] || fail 'a p4c sample symlink has no restored target'
[[ -z "$(git -C "$dest" status --porcelain=v1 --untracked-files=all)" ]] \
  || fail 'restored checkout is dirty'

count="$(find -L "$dest/testdata/p4_16_samples" -type f -name '*.p4' -print | wc -l)" \
  || fail 'could not count p4c samples'
[[ "$count" -gt 0 ]] || fail 'no p4c samples were restored'
printf '[fetch-p4c] %s: %s samples at %s\n' "$dest" "$count" "$pin"
