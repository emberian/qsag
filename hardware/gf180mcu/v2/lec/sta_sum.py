#!/usr/bin/env python3
"""One line per report section of v2/lec/sta.sh output: arrival time, cells on the path, where the path
enters and leaves the register-file array, and its largest single step."""
import re
import sys

for f in sys.argv[1:]:
    t = open(f).read()
    print(f.split("/")[-1])
    for sec in re.split(r"^== ", t, flags=re.M)[1:]:
        title = sec.splitlines()[0]
        if "Startpoint" not in sec:
            if title != "wns":
                print(f"  {title:32s} no path")
            continue
        rows = [(float(a), float(b), n, c.replace("gf180mcu_fd_sc_mcu7t5v0__", ""))
                for a, b, n, c in re.findall(r"^\s+([0-9.]+)\s+([0-9.]+) [\^v] (\S+) \((\S+)\)", sec, re.M)]
        arr = re.search(r"([0-9.]+)\s+data arrival time", sec).group(1)
        ep = re.search(r"Endpoint: (\S+)", sec).group(1)
        rf = [r for r in rows if "u_rf/g_" in r[2]]
        big = max(rows, key=lambda r: r[0])
        where = f"array {rf[0][1]:.1f}..{rf[-1][1]:.1f}" if rf else "not through the array"
        kind = "hold register" if "u_rf/" in ep else "other flop"
        print(f"  {title:32s} arrival {arr:>6s} ns, {len(rows):3d} cells, {where}, largest step {big[0]:.1f} ns ({big[3]}), ends at {kind}")
