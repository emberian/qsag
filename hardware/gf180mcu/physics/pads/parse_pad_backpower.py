#!/usr/bin/env python3
"""Tabulate pad_backpower_dc.log (ngspice prints each table after its CASE line).  Pure Python."""
import re, sys
t = open(sys.argv[1]).read()
parts = re.split(r'CASE (rload=\S+ rser=\S+)', t)
print("%-22s %6s %7s %7s %10s" % ("case", "Vsrc", "Vpad", "Vrail", "Ipad mA"))
for i in range(1, len(parts), 2):
    name, body = parts[i], parts[i + 1]
    rows, cur = {}, {}
    for m in re.finditer(r'^(\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*$', body, re.M):
        rows[int(m.group(1))] = [float(x) for x in m.groups()[1:]]
    for m in re.finditer(r'^(\d+)\s+(\S+)\s+(\S+)\s*$', body, re.M):
        cur[int(m.group(1))] = float(m.group(3))
    for idx in (0, 1, 2, 5, 9, 13, 14):
        if idx in rows:
            r = rows[idx]
            print("%-22s %6.1f %7.3f %7.3f %10.4f" % (name, r[0], r[2], r[3], 1e3 * cur.get(idx, float('nan'))))
