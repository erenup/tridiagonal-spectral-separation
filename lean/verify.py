#!/usr/bin/env python3
"""Compile the scalar/polynomial core and check its exact axiom closure."""
import os
from pathlib import Path
import runpy

ROOT = Path(__file__).resolve().parent

if __name__ == "__main__":
    os.chdir(ROOT)
    runpy.run_path(str(ROOT / "audit" / "verify.py"), run_name="__main__")
