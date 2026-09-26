#!/usr/bin/env bash
# Stable entry point for the tracked-file text-hygiene check.
set -euo pipefail
exec python3 "$(dirname "$0")/check-text.py"
