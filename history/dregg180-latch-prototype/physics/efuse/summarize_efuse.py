#!/usr/bin/env python3
"""Tables from results/*.json(l) written by run_efuse_experiments.py.  Pure Python."""
import json, os, sys, glob
HERE = os.path.dirname(os.path.abspath(__file__))

def load(name):
    p = os.path.join(HERE, "results", name + ".json")
    if os.path.exists(p): return json.load(open(p))
    p = os.path.join(HERE, "results", name + ".partial.jsonl")
    return [json.loads(l) for l in open(p)] if os.path.exists(p) else []

def regime(r):
    if "t_boil" in r: return "boil"
    if "t_melt_bridge" in r: return "melt-through"
    if "t_melt_onset" in r: return "partial melt"
    return "solid %4.0f K" % r["Tmax"]

def t(x): return "-" if x is None else ("%.1f ns" % (x * 1e9) if x < 1e-6 else "%.2f us" % (x * 1e6))

def row(r):
    return "%-46s %-13s melt %-9s through %-9s | I %5.1f mA  R %6.1f  P %5.1f mW  Tpeak %4.0f K  molten %3.0f %%" % (
        r["tag"].split("/", 1)[1], regime(r), t(r.get("t_melt_onset")), t(r.get("t_melt_bridge")),
        r["pl_I"] * 1e3, r["pl_R"], r["pl_P"] * 1e3, r["Tmax"], 100 * r["pl_fmolten"])

for name in sys.argv[1:] or ["verify", "valid", "corners", "sens", "scan_01", "scan_23"]:
    rs = sorted(load(name), key=lambda r: r["tag"])
    print("== %s (%d runs)" % (name, len(rs)))
    for r in rs: print(row(r))
    if name == "corners":
        for macro in ("async", "array"):
            m = [r for r in rs if "/%s/" % macro in r["tag"]]
            cnt = {}
            for r in m: cnt[regime(r).split()[0]] = cnt.get(regime(r).split()[0], 0) + 1
            print("  %s: %s; plateau I %.1f-%.1f mA, P %.1f-%.1f mW, peak T %.0f-%.0f K, melt onset %s-%s" % (
                macro, cnt, min(r["pl_I"] for r in m) * 1e3, max(r["pl_I"] for r in m) * 1e3, min(r["pl_P"] for r in m) * 1e3,
                max(r["pl_P"] for r in m) * 1e3, min(r["Tmax"] for r in m), max(r["Tmax"] for r in m),
                t(min(r["t_melt_onset"] for r in m if "t_melt_onset" in r)), t(max(r["t_melt_onset"] for r in m if "t_melt_onset" in r))))
