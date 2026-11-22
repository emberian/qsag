#!/usr/bin/env python3
"""Sum the extracted capacitance on each net of the marked cell in env?.spice (Magic ext2spice, cthresh 0).
usage: parse_env_cap.py envA.spice u2 envB.spice u2 envC.spice u1 envD.spice u2      (pure Python)"""
import re, sys
def caps(path, inst):
    tot = {}
    for line in open(path):
        m = re.match(r"^C\S*\s+(\S+)\s+(\S+)\s+([0-9.eE+-]+)([a-zA-Z]*)", line)
        if not m: continue
        a, b, v, u = m.group(1), m.group(2), float(m.group(3)), m.group(4).lower()
        v *= {"f": 1e-15, "ff": 1e-15, "a": 1e-18, "af": 1e-18, "p": 1e-12, "pf": 1e-12, "": 1.0}.get(u, 1.0)
        for n, o in ((a, b), (b, a)):
            if n.startswith(inst + "/") or n.startswith(inst + "."):
                d = tot.setdefault(n, [0.0, 0.0])
                d[0] += v
                if not (o.upper() in ("VSS", "VDD", "0", "VSUBS", "VNW", "VPW") or o.startswith(inst)): d[1] += v
    return tot
for k in range(1, len(sys.argv), 2):
    t = caps(sys.argv[k], sys.argv[k + 1])
    print(sys.argv[k], {n.split("/")[-1]: "total %.1f aF, to other cells %.1f aF" % (v[0] * 1e18, v[1] * 1e18) for n, v in sorted(t.items())})
