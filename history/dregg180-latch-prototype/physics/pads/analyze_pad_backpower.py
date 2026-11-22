#!/usr/bin/env python3
"""Tables from pad_backpower_corners.json (run_pad_backpower.py).  Pure Python."""
import json, sys, math
d = json.load(open(sys.argv[1] if len(sys.argv) > 1 else "results/pad_backpower_corners.json"))
cells = ["bi_24t", "in_c", "in_s", "asig_5p0"]
def interp_v(vf, i, target):
    """forward voltage at which the current reaches target (log interpolation)"""
    for k in range(len(vf) - 1):
        a, b = i[k], i[k + 1]
        if a <= 0 or b <= 0: continue
        if a <= target <= b: return vf[k] + (vf[k + 1] - vf[k]) * (math.log(target / a) / math.log(b / a))
    return None
print("== upper path (pad -> rail), rails at 0 V: forward voltage for a given current; min-max over 9 corners")
for c in cells:
    row = []
    for tgt in (1e-6, 1e-5, 1e-4, 1e-3):
        v = [interp_v(r["vf"], r["i_up"], tgt) for k, r in d.items() if k.startswith(c + "/") and r["ok"]]
        v = [x for x in v if x is not None]
        row.append("%g A: %s" % (tgt, "%.2f-%.2f V" % (min(v), max(v)) if v else "above 1.2 V"))
    i12 = [r["i_up"][-1] for k, r in d.items() if k.startswith(c + "/")]
    i02 = [r["i_up"][0] for k, r in d.items() if k.startswith(c + "/")]
    print("  %-9s %s | I at 0.2 V: %.1e-%.1e A, at 1.2 V: %.1f-%.1f mA" % (c, "; ".join(row), min(i02), max(i02), 1e3 * min(i12), 1e3 * max(i12)))
print("== lower path (VSS -> pad), pad below ground")
for c in cells:
    i07 = [r["i_down"][5] for k, r in d.items() if k.startswith(c + "/")]; i10 = [r["i_down"][8] for k, r in d.items() if k.startswith(c + "/")]
    print("  %-9s at -0.7 V: %.2g-%.2g mA; at -1.0 V: %.3g-%.3g mA" % (c, 1e3 * min(i07), 1e3 * max(i07), 1e3 * min(i10), 1e3 * max(i10)))
print("== floating rail: rail voltage (min-max over 9 corners) for source voltage / series resistor / rail load")
for c in cells:
    print(" ", c)
    r0 = next(r for k, r in d.items() if k.startswith(c + "/"))
    RL, RS, VS = r0["rl"], r0["rs"], r0["vs"]
    for vs in (5.0, 5.5, 3.3):
        for rs in RS:
            row = []
            for rl in RL:
                idx = (RL.index(rl) * len(RS) + RS.index(rs)) * len(VS) + VS.index(vs)
                v = [r["v_rail"][idx] for k, r in d.items() if k.startswith(c + "/")]
                i = [r["i_pad"][idx] for k, r in d.items() if k.startswith(c + "/")]
                row.append("%s: %.2f-%.2f V" % (rl, min(v), max(v)))
            print("    Vsrc %.1f Rs %-5s | %s" % (vs, rs, " | ".join(row)))
