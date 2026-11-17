"""Roll up per-instance area of a hierarchical Yosys stat.json (LibreLane 06-yosys-synthesis/reports/stat.json)."""
import json, sys, re
from collections import defaultdict
j = json.load(open(sys.argv[1]))
mods = {k.lstrip("\\"): v for k, v in j["modules"].items()}
for _v in mods.values():
    _v["num_cells_by_type"] = {k.lstrip("\\"): n for k, n in _v.get("num_cells_by_type", {}).items()}
def clean(n): return n.lstrip("\\")
memo = {}
def roll(m):
    if m in memo: return memo[m]
    v = mods[m]
    c = 0
    for k, n in v.get("num_cells_by_type", {}).items():
        c += roll(k)[2] * n if k in mods else n
    memo[m] = (float(v.get("area", 0) or 0), float(v.get("sequential_area", 0) or 0), c)
    return memo[m]
def local(m):
    a, s, c = roll(m)
    for k, n in mods[m].get("num_cells_by_type", {}).items():
        if k in mods:
            ra, rs, rc = roll(k)
            a -= ra * n; s -= rs * n; c -= rc * n
    return a, s, c
memo.clear()
top = [m for m in mods if clean(m) == "chip_top"][0]
core = [k for k in mods[top]["num_cells_by_type"] if "chip_core" in k][0]
print("module-local keys:", [k for k in mods[core] if k != "num_cells_by_type"])
ca, cs, cc = roll(core)
print(f"chip_core total: {ca:,.0f} um2, seq {cs:,.0f}, cells {cc}")
def show(m, depth, maxdepth, prefix=""):
    rows = []
    for k, n in mods[m].get("num_cells_by_type", {}).items():
        if k in mods:
            a, s, c = roll(k)
            rows.append((a * n, s * n, c * n, n, k))
    rows.sort(reverse=True)
    la, ls, lc = local(m)
    print(f"{prefix}{'(local logic)':46s} {la:12,.0f} {100*la/ca:5.1f}%  seq {ls:10,.0f}  cells {lc}")
    for a, s, c, n, k in rows:
        nm = re.sub(r"\$paramod(\$[0-9a-f]+)?\\", "", clean(k))[:44]
        if a < 0.004 * ca and depth > 0: continue
        print(f"{prefix}{nm:46s} {a:12,.0f} {100*a/ca:5.1f}%  seq {s:10,.0f}  cells {c}  x{n}")
        if depth < maxdepth: show(k, depth + 1, maxdepth, prefix + "    ")
show(core, 0, int(sys.argv[2]) if len(sys.argv) > 2 else 2)
