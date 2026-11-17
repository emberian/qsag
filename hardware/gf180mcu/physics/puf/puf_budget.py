#!/usr/bin/env python3
"""PUF entropy budget: Monte Carlo ring frequencies (ngspice, foundry mismatch) plus an explicit sweep of
systematic layout offsets.  Pure Python.

  python3 puf_budget.py results/mc_tt27_local.json

Rings sit in one row at a fixed pitch.  A systematic (layout-determined, same on every die) relative
frequency error is added to ring i at position x_i = i * pitch:
    e_i = a * (i odd) + g * x_i + c * x_i^2
  a : odd/even asymmetry (the two rings of a pair differ: routing, neighbours, supply tap)
  g : linear across-field gradient (%/mm), c : curvature (%/mm^2)
Schemes:
  pair : bit = sign(f[2k] - f[2k+1])                                  2 rings per bit
  quad : bit = sign((f[4k] + f[4k+3]) - (f[4k+1] + f[4k+2]))           4 rings per bit (common centroid)
The offset is known to an attacker, so P(bit = likely value) = Phi(|delta| / sigma) and
h = -log2 of that.  Key budget (syndrome construction, BCH(63,36,5)): blocks * (63 h - 27) >= 128.
"""
import json, math, sys, statistics as st
PITCH_MM = 0.0185      # ring macro pitch: buf_2 + 5 nand2_1 = 18.48 um
def phi(x): return 0.5 * (1 + math.erf(x / math.sqrt(2)))
def h_of(delta_over_sigma): return -math.log2(phi(abs(delta_over_sigma)))
def blocks_needed(h, key=128):
    per = 63 * h - 27
    return None if per <= 0 else math.ceil(key / per)

def main():
    mc = json.load(open(sys.argv[1]))["result"]
    dies = [[x / st.mean(f) - 1 for x in f] for f in mc.values()]      # relative deviations, per die
    def bits(a, g, c, scheme):
        ones = n = 0; vals = []
        for d in dies:
            f = [d[i] + a * (i % 2) + g * i * PITCH_MM + c * (i * PITCH_MM) ** 2 for i in range(len(d))]
            if scheme == "pair": v = [f[2 * k] - f[2 * k + 1] for k in range(len(f) // 2)]
            else: v = [f[4 * k] + f[4 * k + 3] - f[4 * k + 1] - f[4 * k + 2] for k in range(len(f) // 4)]
            vals += v; ones += sum(1 for x in v if x > 0); n += len(v)
        return ones, n, vals
    _, npair, vp = bits(0, 0, 0, "pair"); _, nquad, vq = bits(0, 0, 0, "quad")
    sp = math.sqrt(sum(x * x for x in vp) / npair); sq = math.sqrt(sum(x * x for x in vq) / nquad)
    print("Monte Carlo (TT 5 V 27 C, %d dies x %d rings): sigma pair = %.4f %% of f (%d pairs), sigma quad = %.4f %% (%d quads)" % (
        len(dies), len(dies[0]), 100 * sp, npair, 100 * sq, nquad))
    print("\nsweep (a in %% of f, g in %%/mm, c in %%/mm^2): analytic h, Monte Carlo fraction of the likely value, blocks of 63 bits and rings for 128 key bits")
    print("%-34s | %-44s | %-44s" % ("systematic offset", "pair (2 rings/bit)", "quad (4 rings/bit)"))
    cases = [("none", 0, 0, 0), ("a = 0.003 (1.5 aF / 0.2 mV)", 0.003e-2, 0, 0), ("a = 0.0114 (6 aF / 0.8 mV)", 0.0114e-2, 0, 0),
             ("a = 0.03 (16 aF)", 0.03e-2, 0, 0), ("a = 0.14 (73 aF: filler neighbour)", 0.14e-2, 0, 0),
             ("a = 0.24 (128 aF: row end)", 0.24e-2, 0, 0), ("a = 1.0 (0.5 fF: auto-routed wire)", 1.0e-2, 0, 0),
             ("g = 0.2 %/mm", 0, 0.2e-2, 0), ("g = 0.5 %/mm", 0, 0.5e-2, 0), ("g = 1 %/mm", 0, 1e-2, 0), ("g = 3 %/mm", 0, 3e-2, 0),
             ("c = 1 %/mm^2", 0, 0, 1e-2), ("c = 10 %/mm^2", 0, 0, 10e-2),
             ("a = 0.01, g = 0.5", 0.01e-2, 0.5e-2, 0), ("a = 0.03, g = 1, c = 1", 0.03e-2, 1e-2, 1e-2)]
    for name, a, g, c in cases:
        row = []
        for scheme, sig, per in (("pair", sp, 2), ("quad", sq, 4)):
            if scheme == "pair": delta = -a - g * PITCH_MM          # ignoring the tiny curvature term
            else: delta = 4 * c * PITCH_MM ** 2 * 1.0                # (x0^2 + x3^2 - x1^2 - x2^2) = 4 pitch^2, a and g cancel
            ones, n, _ = bits(a, g, c, scheme)
            frac = max(ones, n - ones) / n
            h = h_of(delta / sig); nb = blocks_needed(h)
            row.append("d/s %.3f h %.3f MC %.3f  %s" % (abs(delta) / sig, h, frac, "no key" if nb is None else "%d blocks, %d rings" % (nb, nb * 63 * per)))
        print("%-34s | %-44s | %-44s" % (name, row[0], row[1]))
    print("\nrings for 128 bits against h (blocks of 63 bits, 27 syndrome bits each):")
    for h in (1.0, 0.98, 0.95, 0.94, 0.92, 0.90, 0.85, 0.80, 0.70, 0.60, 0.50):
        nb = blocks_needed(h)
        print("  h = %.2f: %d blocks = %d bits, key %.0f bits; pair %d rings, quad %d rings" % (h, nb, nb * 63, nb * (63 * h - 27), nb * 126, nb * 252))
    print("\nscreening power: dies needed to see a common offset delta/sigma with 3 standard errors, n positions per die")
    for npos in (16, 64):
        for ds in (0.0442, 0.09, 0.2):
            # fraction of ones shifts by about delta/sigma * 0.399; s.e. = 0.5/sqrt(N)
            N = (3 * 0.5 / (0.399 * ds)) ** 2
            print("  %d positions/die, delta/sigma = %.3f (h = %.2f): %d dies" % (npos, ds, h_of(ds), math.ceil(N / npos)))
main()
