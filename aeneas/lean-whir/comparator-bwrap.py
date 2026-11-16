#!/usr/bin/env python3
"""Expose the canonical sibling dependency read-only inside Lake comparator's sandbox.

Usage (from this package):
  COMPARATOR_BWRAP="$PWD/comparator-bwrap.py" lake comparator --paranoid

Run lake build first to warm ../../lean/.lake. All default namespace isolation and
home masking remain enabled; only the canonical Lean package is made visible.
"""
import os
from pathlib import Path
import sys

canonical = Path(__file__).resolve().parents[2] / "lean"
if not (canonical / "lakefile.toml").is_file():
    raise SystemExit(f"Missing canonical Lean dependency: {canonical}")
args = sys.argv[1:]
try:
    separator = args.index("--")
except ValueError:
    raise SystemExit("Expected the comparator's bwrap command separator")
args[separator:separator] = ["--ro-bind", str(canonical), str(canonical)]
os.execvp("bwrap", ["bwrap", *args])
