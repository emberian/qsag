#!/usr/bin/env python3
"""Inclusive area per module instance tree from a hierarchical Yosys `stat` report.

Usage: area_table.py <synth_chip_hier.stat> [max-depth] [min-area-um2] [top]

Each module section gives the local area (excluding submodules) and the submodule instance
counts; the inclusive area is local + sum(count * inclusive(child)). Prints um^2, the share of
the SLOT_0P5X0P5 core (1052 x 1647 um) and the local (exclusive) area."""
import re
import sys

CORE = 1052 * 1647
txt = open(sys.argv[1]).read()
maxd = int(sys.argv[2]) if len(sys.argv) > 2 else 2
mina = float(sys.argv[3]) if len(sys.argv) > 3 else 0.0
top = sys.argv[4] if len(sys.argv) > 4 else "chip_core"
local, kids = {}, {}
for m in re.finditer(r"^=== (\S+) ===\n(.*?)(?=^=== |\Z)", txt, re.S | re.M):
    name, body = m.group(1), m.group(2)
    if "design hierarchy" in name:
        continue
    a = re.search(r"Chip area for module.*?:\s+([\d.]+)", body)
    if not a:
        continue
    local[name] = float(a.group(1))
    kids[name] = []
    sub = re.search(r"^\s*\d+\s+-\s+submodules\n((?:\s+\d+\s+-\s+\S+\n)*)", body, re.M)
    if sub:
        for k in re.finditer(r"^\s+(\d+)\s+-\s+(\S+)$", sub.group(1), re.M):
            kids[name].append((int(k.group(1)), k.group(2)))


def short(n):
    n = re.sub(r"\$paramod(\$[0-9a-f]+)?\\", "", n)
    n = re.sub(r"\\(\w+)=s32'0*([01]+)", lambda k: f" {k.group(1)}={int(k.group(2), 2)}", n)
    n = re.sub(r"\\(\w+)=\d+'([01]+)", lambda k: f" {k.group(1)}={int(k.group(2), 2)}", n)
    return n


def incl(n):
    return local[n] + sum(c * incl(k) for c, k in kids[n])


def show(n, cnt, depth):
    a = cnt * incl(n)
    if a < mina:
        return
    lab = ("  " * depth + (f"{cnt} x " if cnt > 1 else "") + short(n))[:52]
    print(f"{lab:<52} {a:>10.0f} um^2 {100 * a / CORE:6.2f} %   local {cnt * local[n]:>9.0f}")
    if depth < maxd:
        for c, k in sorted(kids[n], key=lambda ck: -ck[0] * incl(ck[1])):
            show(k, c, depth + 1)


show(top if top in local else "\\" + top, 1, 0)
