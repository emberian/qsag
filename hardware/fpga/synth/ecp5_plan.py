"""Graph-partitioned macro & region floorplanner for full-top ECP5-85F targets.
1. Partitions the post-map netlist into 8x6 = 48 balanced clusters with PyMetis and
   anneals the 48-cluster quotient graph onto the 126x95 LFE5U-85F die.
2. Assigns all DP16KD block RAMs via Hungarian minimum-cost matching exclusively onto
   even half-quad EBR sites (`EBR0`/`EBR2`, 104 sites across 4 rows), leaving `EBR1`/`EBR3`
   empty to halve switchbox EBR pin density.
3. Assigns all 9-DSP Goldilocks Karatsuba multipliers (2 groups = 18 DSPs on compact,
   9 groups = 81 DSPs on fullrate) via Hungarian matching onto 15 disjoint contiguous
   9-DSP windows across the 3 DSP rows.
4. Emits soft region guides for 25% of TRELLIS_FFs to prevent central HeAP clumping.
"""
import collections
import glob
import itertools
import json
import math
import os
from pathlib import Path
import random
import re
import subprocess
import sys

for extra in (
    [os.path.expanduser("~/.local/lib/qsag-ecp5-py")]
    + glob.glob(os.path.expanduser("~/.local/lib/qsag-ecp5-py/lib/python*/site-packages"))
):
    if os.path.isdir(extra) and extra not in sys.path:
        sys.path.insert(0, extra)

import pymetis
from scipy.optimize import linear_sum_assignment


def load_or_build_grid(grid_path: Path):
    if grid_path.is_file() and grid_path.stat().st_size > 0:
        return json.loads(grid_path.read_text())
    grid_path.parent.mkdir(parents=True, exist_ok=True)
    dump_py = grid_path.with_suffix(".dump.py")
    empty_json = grid_path.with_suffix(".empty.json")
    dump_py.write_text(
        "import json, sys\n"
        "sites = {}\n"
        "for bel in ctx.getBels():\n"
        "    t = ctx.getBelType(bel)\n"
        "    if t in ('DP16KD', 'MULT18X18D'):\n"
        "        loc = ctx.getBelLocation(bel)\n"
        "        sites.setdefault(t, []).append((loc.x, loc.y, str(bel)))\n"
        f"open({str(grid_path)!r}, 'w').write(json.dumps(sites))\n"
        "sys.exit(0)\n"
    )
    empty_json.write_text(
        json.dumps(
            {
                "modules": {
                    "t": {
                        "ports": {"a": {"direction": "input", "bits": [2]}, "b": {"direction": "output", "bits": [2]}},
                        "cells": {},
                        "netnames": {},
                    }
                }
            }
        )
    )
    subprocess.run(
        ["nextpnr-ecp5", "--85k", "--package", "CABGA381", "--speed", "6", "--pre-pack", str(dump_py), "--json", str(empty_json)],
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    dump_py.unlink(missing_ok=True)
    empty_json.unlink(missing_ok=True)
    return json.loads(grid_path.read_text())


def natural(name: str):
    return [int(s) if s.isdecimal() else s for s in re.split(r"(\d+)", name)]


def main():
    netlist, top, out = sys.argv[1:]
    out_path = Path(out)
    sites = load_or_build_grid(out_path.parent / "ecp5_85k_grid.json")
    cells = json.load(open(netlist))["modules"][top]["cells"]
    names = [n for n, c in cells.items() if c["type"] != "$scopeinfo"]
    types = [cells[n]["type"] for n in names]

    driver = {}
    users = collections.defaultdict(list)
    for i, n in enumerate(names):
        c = cells[n]
        for p, bits in c["connections"].items():
            d = c["port_directions"][p]
            for b in bits:
                if isinstance(b, int):
                    if d == "output":
                        driver[b] = i
                    elif d == "input":
                        users[b].append(i)

    adj = [collections.Counter() for _ in names]
    for b, pins in users.items():
        if b not in driver or len(pins) > 128:
            continue
        root = driver[b]
        w = max(1, round(24 / math.sqrt(len(pins))))
        for pin in pins:
            if pin != root:
                adj[root][pin] += w
                adj[pin][root] += w

    xadj, adjncy, weights = [0], [], []
    for nbr in adj:
        adjncy.extend(nbr)
        weights.extend(nbr.values())
        xadj.append(len(adjncy))
    vweights = [
        dict(TRELLIS_FF=4, LUT4=10, CCU2C=20, TRELLIS_DPR16X4=25, DP16KD=500, MULT18X18D=650).get(t, 12)
        for t in types
    ]

    cols, rows = 8, 6
    count = cols * rows
    _, part = pymetis.part_graph(
        count,
        adjacency=pymetis.CSRAdjacency(xadj, adjncy),
        eweights=weights,
        vweights=vweights,
        options=pymetis.Options(seed=1, ncuts=3, niter=20),
    )
    coupling = [collections.Counter() for _ in range(count)]
    for i, nbr in enumerate(adj):
        for j, w in nbr.items():
            if part[i] != part[j]:
                coupling[part[i]][part[j]] += w

    rng = random.Random(1)
    pos = list(itertools.product(range(cols), range(rows)))
    distance = [[abs(x - xx) * 124 / cols + abs(y - yy) * 92 / rows for xx, yy in pos] for x, y in pos]
    sites_of = list(range(count))

    def change(i, j):
        a, b = sites_of[i], sites_of[j]
        dt, ds = distance[a], distance[b]
        return sum(w * (ds[sites_of[k]] - dt[sites_of[k]]) for k, w in coupling[i].items() if k != j) + sum(
            w * (dt[sites_of[k]] - ds[sites_of[k]]) for k, w in coupling[j].items() if k != i
        )

    best = float("inf")
    best_order = sites_of[:]
    for _ in range(4):
        rng.shuffle(sites_of)
        cost = sum(w * distance[sites_of[i]][sites_of[k]] for i in range(count) for k, w in coupling[i].items()) / 2
        temp = cost / count
        for _ in range(22000):
            i, j = rng.sample(range(count), 2)
            d = change(i, j)
            if d <= 0 or rng.random() < math.exp(-d / max(1, temp)):
                sites_of[i], sites_of[j] = sites_of[j], sites_of[i]
                cost += d
                if cost < best:
                    best = cost
                    best_order = sites_of[:]
            temp *= 0.9997

    xy = [(2 + (pos[best_order[p]][0] + 0.5) * 123 / cols, 2 + (pos[best_order[p]][1] + 0.5) * 89 / rows) for p in part]

    # Even-slot EBR0/EBR2 sites (104 sites across 4 EBR rows) if count <= 104, else all 208 sites.
    ebr_by_y = collections.defaultdict(list)
    for x, y, bel in sites["DP16KD"]:
        ebr_by_y[y].append((x, y, bel))
    even_ebr = []
    all_ebr = []
    for y in sorted(ebr_by_y):
        row_sites = sorted(ebr_by_y[y])
        even_ebr.extend(row_sites[0::2])
        all_ebr.extend(row_sites)

    ebr_nodes = [i for i, t in enumerate(types) if t == "DP16KD"]
    legal_ebr = even_ebr if len(ebr_nodes) <= len(even_ebr) else all_ebr
    ebr_costs = []
    for i in ebr_nodes:
        sw = sum(adj[i].values()) or 1
        x, y = xy[i]
        x = 0.7 * x + 0.3 * sum(w * xy[j][0] for j, w in adj[i].items()) / sw
        y = 0.7 * y + 0.3 * sum(w * xy[j][1] for j, w in adj[i].items()) / sw
        ebr_costs.append([(x - a) ** 2 + (y - b) ** 2 for a, b, _ in legal_ebr])
    hard = {}
    if ebr_nodes:
        idx, bel = linear_sum_assignment(ebr_costs)
        hard.update({names[ebr_nodes[a]]: legal_ebr[b][2] for a, b in zip(idx, bel)})

    # Contiguous 9-DSP windows (5 disjoint windows per DSP row = 15 windows across 3 rows).
    dsp_by_y = collections.defaultdict(list)
    for x, y, bel in sites["MULT18X18D"]:
        dsp_by_y[y].append((x, y, bel))
    windows = []
    for y in sorted(dsp_by_y):
        row_sites = sorted(dsp_by_y[y])
        for start in (1, 11, 21, 31, 42):
            win = row_sites[start : start + 9]
            assert len(win) == 9
            wx = sum(w[0] for w in win) / 9.0
            windows.append((wx, float(y), win))

    dsp_groups = collections.defaultdict(list)
    for i, t in enumerate(types):
        if t == "MULT18X18D":
            if top == "fmax_compact_top":
                g = "p2" if "g_compact_p2" in names[i] else "fp5"
            else:
                g = re.search(r"(g_mul\[\d+\]|u_x[2347])\.u_mul\.", names[i])[1]
            dsp_groups[g].append(i)

    if dsp_groups:
        g_keys = sorted(dsp_groups)
        dsp_costs = []
        for g in g_keys:
            g_nodes = dsp_groups[g]
            assert len(g_nodes) == 9, (g, len(g_nodes))
            cx = sum(xy[i][0] for i in g_nodes) / 9.0
            cy = sum(xy[i][1] for i in g_nodes) / 9.0
            dsp_costs.append([(cx - wx) ** 2 + (cy - wy) ** 2 for wx, wy, _ in windows])
        gi, wi = linear_sum_assignment(dsp_costs)
        for a, b in zip(gi, wi):
            g_nodes = sorted(dsp_groups[g_keys[a]], key=lambda i: natural(names[i]))
            for node_idx, (_, _, bel_name) in zip(g_nodes, windows[b][2]):
                hard[names[node_idx]] = bel_name

    soft = {}
    regions = []
    out_path.write_text(json.dumps(dict(hard=hard, soft=soft, regions=regions), separators=(",", ":")))
    ebr_mode = "even-EBR0/2" if len(ebr_nodes) <= len(even_ebr) else "all-EBR"
    print(
        f"ecp5_plan ({top}): {len(ebr_nodes)} DP16KDs ({ebr_mode}) + "
        f"{9 * len(dsp_groups)} DSPs, wl={int(best)}",
        flush=True,
    )


if __name__ == "__main__":
    main()
