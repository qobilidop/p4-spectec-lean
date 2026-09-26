#!/usr/bin/env python3
"""Capture pinned NanoSwitch target observations."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "P4SpecTecTest/Oracle/NanoSwitch"))
from request_capture import main

if __name__ == "__main__":
    main(Path(__file__).parent, "data-and-dynamic-handler",
         ROOT / ".artifacts/nano-target-oracle", allow_update=False)
