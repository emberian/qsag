#!/usr/bin/env python3
"""Condense a Yosys `stat -top` report (hierarchy totals) and `ltp -noff` into one table row set."""
import re, sys
stat, ltp, fam, tag = sys.argv[1:5]
text = open(stat).read()
# The last "design hierarchy" section holds the totals across the hierarchy.
tail = text[text.rfind("design hierarchy"):] if "design hierarchy" in text else text
cells = {}
for m in re.finditer(r"^\s+(\d+)\s+(?:[\d.]+\s+)?(\S+)\s*$", tail, re.M):
    cells[m.group(2)] = cells.get(m.group(2), 0) + int(m.group(1))
if not cells:
    for m in re.finditer(r"^\s+(\S+)\s+(\d+)\s*$", tail, re.M):
        cells[m.group(1)] = cells.get(m.group(1), 0) + int(m.group(2))
def tot(pred):
    return sum(v for k, v in cells.items() if pred(k))
rows = []
if fam == "xcup":
    rows = [("LUT (LUT1-6)", tot(lambda k: re.fullmatch(r"LUT[1-6]", k))),
            ("  of which LUT6", cells.get("LUT6", 0)),
            ("MUXF7/F8/F9", tot(lambda k: k.startswith("MUXF"))),
            ("FF (FDRE/FDSE/FDCE/FDPE)", tot(lambda k: re.fullmatch(r"FD[RSCP]E", k))),
            ("CARRY8", cells.get("CARRY8", 0)),
            ("DSP48E2", cells.get("DSP48E2", 0)),
            ("RAMB36E2", cells.get("RAMB36E2", 0)), ("RAMB18E2", cells.get("RAMB18E2", 0)),
            ("SRL16E/SRLC32E", tot(lambda k: k.startswith("SRL"))),
            ("LUTRAM (RAM32M/RAM64M/...)", tot(lambda k: re.match(r"RAM(32|64|128|256)", k)))]
else:
    rows = [("LUT4", cells.get("LUT4", 0)),
            ("TRELLIS_FF", cells.get("TRELLIS_FF", 0)),
            ("CCU2C", cells.get("CCU2C", 0)),
            ("L6MUX21/PFUMX", tot(lambda k: k in ("L6MUX21", "PFUMX"))),
            ("MULT18X18D", cells.get("MULT18X18D", 0)),
            ("DP16KD", cells.get("DP16KD", 0)),
            ("TRELLIS_DPR16X4", cells.get("TRELLIS_DPR16X4", 0))]
depths = [int(x) for x in re.findall(r"Longest topological path in \S+ \(length=(\d+)\)", open(ltp).read())]
print(f"== {tag} [{fam}]")
for k, v in rows:
    print(f"  {k:28s} {v}")
print(f"  {'max logic depth (cells, ltp)':28s} {max(depths) if depths else 'n/a'}")
