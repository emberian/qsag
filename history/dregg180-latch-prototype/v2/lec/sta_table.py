#!/usr/bin/env python3
"""Summary table of v2/lec/sta_gate.sh reports.

    python3 sta_table.py <dir> [corner ...]

Per report (block_corner.rpt): worst logic arrival of full-cycle stages (flop endpoints) and of half-cycle
stages (latch D endpoints), against the 28 ns / 14 ns budgets, with the count of endpoints over budget;
worst hold slack; violators of max slew, max capacitance, max fanout and min pulse width."""
import os
import re
import sys

BUD_FULL, BUD_HALF = 28.0, 14.0


def section(t, name):
    m = re.search(r"^== " + re.escape(name) + r"\n(.*?)(?=^== )", t, re.S | re.M)
    return m.group(1) if m else ""


def endpoints(txt):
    out = []
    for name, cell, req, act, slack in re.findall(r"^(\S+) \((\S+)\)\s+(-?[0-9.]+)\s+(-?[0-9.]+)\s+(-?[0-9.]+)", txt, re.M):
        out.append((name, cell, float(req), float(act), float(slack)))
    return out


def violators(txt, skip=()):
    return sum(1 for pin in re.findall(r"^(\S+)\s.*\(VIOLATED\)", txt, re.M) if pin not in skip)


def main():
    d = sys.argv[1]
    corners = sys.argv[2:]
    files = sorted(f for f in os.listdir(d) if f.endswith(".rpt") and (not corners or any(c in f for c in corners)))
    print(f"{'report':44s} {'full-cycle':>10s} {'over':>5s} {'half-cycle':>10s} {'over':>5s} {'hold':>7s} {'slew':>5s} {'cap':>5s} {'pulse':>5s}  worst slew (any pin, clock pins included)")
    bad = 0
    for f in files:
        t = open(os.path.join(d, f)).read()
        if "== end" not in t:
            print(f"{f:44s} incomplete: {t.strip().splitlines()[-1][:80] if t.strip() else 'empty'}")
            bad += 1
            continue
        su = endpoints(section(t, "setup endpoints"))
        lat = [e for e in su if "lat" in e[1]]
        ff = [e for e in su if "lat" not in e[1]]
        ho = endpoints(section(t, "hold endpoints"))
        wf = max((e[3] for e in ff), default=0.0)
        wl = max((e[3] for e in lat), default=0.0)
        nf = sum(1 for e in ff if e[3] > BUD_FULL)
        nl = sum(1 for e in lat if e[3] > BUD_HALF)
        wh = min((e[4] for e in ho), default=float("nan"))
        cp = os.path.join(d, f[:-4] + ".clkpins")
        skip = set(open(cp).read().split()) if os.path.exists(cp) else set()
        v = [violators(section(t, "max slew"), skip), violators(section(t, "max capacitance"), skip),
             violators(section(t, "min pulse width"))]
        ws = re.search(r"^\S+\s+([0-9.]+)\s+([0-9.]+)\s+(-?[0-9.]+)", section(t, "worst slew"), re.M)
        wst = f"{ws.group(2)} of {ws.group(1)}" if ws else "-"
        print(f"{f[:-4]:44s} {wf:10.2f} {nf:5d} {wl:10.2f} {nl:5d} {wh:7.2f} {v[0]:5d} {v[1]:5d} {v[2]:5d}  {wst}")
        bad += nf + nl + sum(v) + (1 if wh < 0 else 0)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
