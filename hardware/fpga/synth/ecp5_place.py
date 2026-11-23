"""Row-aligned 9-DSP Goldilocks multiplier placement for high-DSP ECP5-85F targets.
Keeps the three MULT18X18D tiles of each 33x32 Karatsuba product adjacent and spreads
the 9-DSP 64x64 multipliers evenly across the three DSP rows of LFE5U-85F.
"""
from collections import defaultdict
import os
import re

top = os.environ.get("QSAG_ECP5_TOP", "")
rows = defaultdict(list)
for bel in ctx.getBels():
    if ctx.getBelType(bel) == "MULT18X18D":
        loc = ctx.getBelLocation(bel)
        rows[loc.y].append((loc.x, bel))

if top == "fmax_ext5_mac":
    assert len(rows) == 3
    products = defaultdict(list)
    for name, cell in ctx.cells:
        if cell.type == "MULT18X18D":
            match = re.search(r"g_mul\[(\d+)\]", name)
            products[int(match[1])].append(name)
    assert len(products) == 14
    layout = [[6, 8, 10, 13, 7], [3, 1, 4, 5], [9, 0, 12, 2, 11]]
    for y, row in zip(sorted(rows), layout):
        sites = sorted(rows[y])
        for column, product in enumerate(row):
            cells = sorted(products[product])
            assert len(cells) == 9
            start = int((column + 0.5) * len(sites) / len(row) - 4.5)
            window = sites[start : start + 9]
            assert len(window) == 9
            for name, (_, bel) in zip(cells, window):
                ctx.bindBel(bel, ctx.cells[name], STRENGTH_USER)
elif top == "fmax_ecp5_fullrate_top":
    assert len(rows) == 3
    groups = defaultdict(list)
    for name, cell in ctx.cells:
        if cell.type == "MULT18X18D":
            group = re.search(r"(g_mul\[\d+\]|u_x[2347])\.u_mul\.", name)[1]
            groups[group].append(name)
    layout = [
        ["u_x2", "u_x3", "u_x4", "u_x7"],
        ["g_mul[0]", "g_mul[2]", "g_mul[1]"],
        ["g_mul[3]", "g_mul[4]"],
    ]
    assert sum(map(len, groups.values())) == 81
    for y, row in zip(sorted(rows), layout):
        sites = sorted(rows[y])
        for column, product in enumerate(row):
            cells = sorted(groups[product])
            assert len(cells) == 9
            start = int((column + 0.5) * len(sites) / len(row) - 4.5)
            window = sites[start : start + 9]
            assert len(window) == 9
            for name, (_, bel) in zip(cells, window):
                ctx.bindBel(bel, ctx.cells[name], STRENGTH_USER)
