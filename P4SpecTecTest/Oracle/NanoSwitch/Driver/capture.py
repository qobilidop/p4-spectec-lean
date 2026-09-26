#!/usr/bin/env python3
"""Capture pinned NanoSwitch driver observations."""

from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / "P4SpecTecTest/Oracle/NanoSwitch"))
from request_capture import main

if __name__ == "__main__":
    main(Path(__file__).parent, "dynamic-driver",
         ROOT / ".artifacts/nano-driver-oracle", allow_update=True)
