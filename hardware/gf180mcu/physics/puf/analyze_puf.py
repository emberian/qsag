#!/usr/bin/env python3
"""Analyse ring-oscillator Monte Carlo output (run_puf_mc.py).  Pure Python.

  python3 analyze_puf.py results/mc_tt27_local.json results/sens_tt27.json [results/mc_tt27_global.json]

What the foundry mismatch model can and cannot say about entropy: every device gets an independent,
zero-mean Gaussian threshold and mobility offset, so a bit made from two nominally identical rings is
unbiased and independent of every other bit BY CONSTRUCTION.  The Monte Carlo therefore measures only the
size of the random spread (sigma).  Min-entropy is then decided by how large any SYSTEMATIC difference
between the two rings of a pair is, compared with that sigma: such a difference is the same on every die,
so an attacker who knows the layout knows it.
"""
import json, math, sys, statistics as st

def phi(x): return 0.5 * (1 + math.erf(x / math.sqrt(2)))

def main():
    mc = json.load(open(sys.argv[1]))["result"]; sens = json.load(open(sys.argv[2]))["result"]
    allf, rel_pairs, bits = [], [], {}
    for seed, f in sorted(mc.items()):
        f = [x for x in f if x]
        mu = st.mean(f); sd = st.pstdev(f)
        d = [(f[2 * k] - f[2 * k + 1]) / mu for k in range(len(f) // 2)]
        rel_pairs += d; bits[seed] = [1 if x > 0 else 0 for x in d]; allf += [x / mu for x in f]
        print("die %s: %d rings, mean %.2f MHz, sigma_f/f %.3f %%, sigma_pair/f %.3f %%, ones %d/%d" % (
            seed, len(f), mu / 1e6, 100 * sd / mu, 100 * st.pstdev(d), sum(bits[seed]), len(d)))
    n = len(rel_pairs); sp = math.sqrt(sum(x * x for x in rel_pairs) / n)
    sf = st.pstdev(allf)
    ones = sum(sum(b) for b in bits.values()); p = ones / n; se = math.sqrt(0.25 / n)
    print("\npooled: %d rings, sigma_f/f = %.4f %% ; %d pairs, sigma_pair/f = %.4f %% (sqrt2*sigma_f = %.4f %%)" % (
        len(allf), 100 * sf, n, 100 * sp, 100 * math.sqrt(2) * sf))
    # normality: excess kurtosis and fraction beyond 2 sigma
    m4 = sum(x ** 4 for x in rel_pairs) / n / sp ** 4
    print("pair difference: kurtosis %.2f (Gaussian 3), |d|>2sigma %.3f (Gaussian 0.046)" % (m4, sum(1 for x in rel_pairs if abs(x) > 2 * sp) / n))
    print("bias: %d ones of %d = %.3f, standard error %.3f -> the sample can only bound h_min >= %.2f at 2 s.e." % (
        ones, n, p, se, -math.log2(0.5 + abs(p - 0.5) + 2 * se)))
    seeds = sorted(bits); hd = []
    for i in range(len(seeds)):
        for j in range(i + 1, len(seeds)):
            a, b = bits[seeds[i]], bits[seeds[j]]; m = min(len(a), len(b))
            hd.append(sum(x != y for x, y in zip(a[:m], b[:m])) / m)
    if hd: print("inter-die Hamming distance: mean %.3f, min %.3f, max %.3f over %d die pairs (ideal 0.5; binomial s.d. per pair %.3f)" % (
        st.mean(hd), min(hd), max(hd), len(hd), math.sqrt(0.25 / len(bits[seeds[0]]))))
    # sensitivities (mismatch off)
    c = sens["cases"]; f0 = c["nominal"]
    s_load_all = (c["load_all_+5pct"] / f0 - 1) / 0.05          # df/f per dC/C of the wire load on all stages
    s_one = (c["load_one_stage_+0.5fF"] / f0 - 1) / 0.5         # df/f per fF on one stage
    s_vdd = (c["vdd_-50mV"] / f0 - 1) / (-0.050)                # df/f per volt
    print("\nsensitivities (TT 27 C, mismatch off): df/f = %.3f per unit dC/C of all stage loads; %.4f %% per aF on one stage; %.3f %% per mV of supply" % (
        s_load_all, 100 * s_one / 1000, 100 * s_vdd / 1000))
    print("\nsystematic offset delta between the rings of a pair -> bias and min-entropy (per bit):")
    print("  %-10s %-8s %-7s %-22s %-18s" % ("delta/sig", "P(bit)", "h_min", "one-stage load diff", "supply diff"))
    for r in (0.0, 0.02, 0.053, 0.1, 0.2, 0.5, 1.0, 2.0):
        pb = phi(r); h = -math.log2(pb); d = r * sp
        print("  %-10.3f %-8.4f %-7.3f %-22s %-18s" % (r, pb, h, "%.1f aF" % (d / abs(s_one) * 1000), "%.2f mV" % (d / abs(s_vdd) * 1000)))
    for target in (0.95, 0.94, 0.90):
        lo, hi = 0.0, 3.0
        for _ in range(60):
            mid = (lo + hi) / 2
            if -math.log2(phi(mid)) > target: lo = mid
            else: hi = mid
        print("  h_min >= %.2f needs |delta| <= %.4f sigma_pair = %.4f %% of f = %.1f aF on one stage = %.2f mV of supply difference" % (
            target, lo, 100 * lo * sp, lo * sp / abs(s_one) * 1000, lo * sp / abs(s_vdd) * 1000))
    if len(sys.argv) > 3:
        g = json.load(open(sys.argv[3]))["result"]
        means = [st.mean([x for x in f if x]) for f in g.values()]
        print("\ndie-to-die (statistical library, sw_stat_global=1): die means %s MHz; spread %.1f %% (s.d./mean, %d dies)" % (
            ", ".join("%.0f" % (m / 1e6) for m in means), 100 * st.pstdev(means) / st.mean(means), len(means)))
main()
