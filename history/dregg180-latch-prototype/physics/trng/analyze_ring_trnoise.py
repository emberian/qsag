#!/usr/bin/env python3
"""kappa (jitter accumulation constant, sigma(t) = kappa*sqrt(t)) from run_ring_trnoise.py output.
usage: analyze_ring_trnoise.py scale file.dat [scale file.dat ...]   (numpy)"""
import sys, numpy as np
def periods(path, vmid=2.5):
    d = np.loadtxt(path); t, v = d[:, 0], d[:, 1]
    i = np.where((v[:-1] < vmid) & (v[1:] >= vmid))[0]
    tc = t[i] + (vmid - v[i]) * (t[i + 1] - t[i]) / (v[i + 1] - v[i])
    tc = tc[tc > 20e-9]
    return np.diff(tc)
for k in range(1, len(sys.argv), 2):
    scale, path = float(sys.argv[k]), sys.argv[k + 1]
    p = periods(path); T = p.mean(); n = len(p)
    out = []
    for m in (1, 2, 4, 8, 16, 32):
        s = np.add.reduceat(p[: n // m * m], np.arange(0, n // m * m, m))
        out.append((m, s.std()))
    k1 = out[0][1] / np.sqrt(T)                      # from single-period jitter
    # slope of var(m periods) against m T: white-FM part
    ms = np.array([o[0] for o in out[:5]]); var = np.array([o[1] ** 2 for o in out[:5]])
    slope = np.polyfit(ms * T, var, 1)[0]
    c1 = np.corrcoef(p[:-1], p[1:])[0, 1]
    print("%-22s periods %5d  T %.4f ns  sigma_period %.4f ps  kappa(1 period) %.3e  kappa(slope) %.3e  /scale: %.3e  lag-1 corr %+.3f  sigma(m)/sqrt(m): %s" % (
        path.split("/")[-1], n, T * 1e9, out[0][1] * 1e12, k1, np.sqrt(max(slope, 0)), np.sqrt(max(slope, 0)) / max(scale, 1e-9) if scale else float("nan"), c1,
        " ".join("%.3f" % (o[1] / np.sqrt(o[0]) * 1e12) for o in out)))
