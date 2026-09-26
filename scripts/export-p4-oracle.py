#!/usr/bin/env python3
"""Compatibility CLI for capturing pinned full-P4 AL observations."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from P4SpecTecTest.Oracle.P4.Replay.capture import *

if __name__ == "__main__":
    main()
