#!/usr/bin/env python3
"""Global-route usage map from an OpenROAD guide file (write_guides).

usage: guides_congestion.py route.guide out.json [die_x1 die_y1]

Every guide rectangle on a routing layer uses one track in each gcell it covers. Usage is summed
over Metal2..Metal5 and divided by the track capacity of those layers in the gcell (gcell size /
pitch: 0.56 um for Metal2..4, 0.90 um for Metal5; supply straps are not subtracted, so a gcell
under a strap reads lower than it is). Output: {"grid": rows of ratios, "bin", "x0", "y0", "peak",
"p99", "mean", "per_layer": {layer: track-um}} for tools/render_fp.py.
"""
import json
import sys
from collections import defaultdict

PITCH = {"Metal2": 0.56, "Metal3": 0.56, "Metal4": 0.56, "Metal5": 0.90}


def main():
    path, out = sys.argv[1], sys.argv[2]
    rects = []
    sizes = defaultdict(int)
    with open(path) as f:
        for line in f:
            t = line.split()
            if len(t) == 5 and t[4] in PITCH:
                x1, y1, x2, y2 = (int(v) for v in t[:4])
                rects.append((x1, y1, x2, y2, t[4]))
                sizes[min(x2 - x1, y2 - y1)] += 1
    g = max(sizes, key=sizes.get)            # gcell size in dbu (the commonest short side)
    dbu = 2000.0
    use = defaultdict(float)
    per_layer = defaultdict(float)
    xs = [r[0] for r in rects]
    ys = [r[1] for r in rects]
    x0, y0 = min(xs), min(ys)
    for x1, y1, x2, y2, l in rects:
        for i in range((x1 - x0) // g, max((x2 - x0 + g - 1) // g, (x1 - x0) // g + 1)):
            for j in range((y1 - y0) // g, max((y2 - y0 + g - 1) // g, (y1 - y0) // g + 1)):
                use[(i, j)] += 1.0
                per_layer[l] += g / dbu
    cap = sum((g / dbu) / p for p in PITCH.values())
    nx = max(i for i, _ in use) + 1
    ny = max(j for _, j in use) + 1
    grid = [[use.get((i, j), 0.0) / cap for i in range(nx)] for j in range(ny)]
    vals = sorted(v for row in grid for v in row if v > 0)
    res = dict(grid=grid, bin=g / dbu, x0=x0 / dbu, y0=y0 / dbu, peak=vals[-1], p99=vals[int(0.99 * len(vals))],
               mean=sum(vals) / len(vals), per_layer={k: round(v) for k, v in per_layer.items()},
               gcell_um=g / dbu, tracks_per_gcell=round(cap, 1))
    json.dump(res, open(out, "w"))
    print({k: v for k, v in res.items() if k != "grid"})


if __name__ == "__main__":
    main()
