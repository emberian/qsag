#!/usr/bin/env python3
"""Compare synth/area.sh mapped-area reports (IHP SG13G2 or Sky130 HD liberty)."""
import re
import sys
from pathlib import Path

def area(path):
    matches = re.findall(r"Chip area for (?:top )?module '\\?qsag_ni_asic_top':\s*([\d.]+)", Path(path).read_text())
    if len(matches) != 1:
        raise ValueError(f"expected one mapped top area in {path}")
    return float(matches[0])

base, candidate = map(area, sys.argv[1:3])
delta = 100 * (candidate / base - 1)
print(f"baseline={base:.3f} um^2  candidate={candidate:.3f} um^2  change={delta:+.4f}%")
sys.exit(0 if delta < 5 else 1)
