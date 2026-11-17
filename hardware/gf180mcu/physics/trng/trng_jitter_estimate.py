#!/usr/bin/env python3
"""Thermal-jitter entropy estimate for the two-ring TRNG (rtl/qsag_trng.sv).  Pure Python.

Inputs measured from simulation (trng_rings.sp, TT 5 V 27 C, ngspice 45, foundry models):
  fast ring period, slow ring period, average supply current of each ring.
Analytic model (taken from literature):
  white-noise phase noise of an inverter ring, A. A. Abidi, "Phase Noise and Jitter in CMOS Ring
  Oscillators", IEEE JSSC 41(8), 2006:  L(df) = (2kT/I) * ((gN+gP)/(VDD-Vt) + 1/VDD) * (f0/df)^2
  accumulated jitter sigma(t) = kappa*sqrt(t), kappa^2 = L(df)*df^2/f0^2 (Hajimiri et al., JSSC 34(6), 1999)
Assumed: gamma = 2/3 for both devices, Vt = 0.8 V; flicker noise, supply and substrate noise ignored
(they add jitter that is partly deterministic or attacker-influenced, so they are not counted).
"""
import math, sys

def kappa(i_avg, vdd=5.0, vt=0.8, gamma=2.0 / 3.0, temp=300.0):
    k = 1.380649e-23
    return math.sqrt(2 * k * temp / i_avg * (2 * gamma / (vdd - vt) + 1.0 / vdd))

def hbin(p):
    return 0.0 if p <= 0 or p >= 1 else -(p * math.log2(p) + (1 - p) * math.log2(1 - p))

def phi(x): return 0.5 * (1 + math.erf(x / math.sqrt(2)))

def entropy_per_sample(sig_over_t, n=20000):
    """Sampled square wave (50 % duty) with Gaussian phase jitter sigma (in periods); the mean phase is
    assumed known to the attacker and uniformly distributed over a period.  Returns the average Shannon
    entropy and the average min-entropy of one sample."""
    s = sig_over_t; hs = hm = 0.0
    for i in range(n):
        u = (i + 0.5) / n                      # mean phase in periods
        p1 = 0.0                               # probability the sample is 1 (wave is 1 on [0, 0.5) mod 1)
        for kk in range(-8, 9):
            p1 += phi((kk + 0.5 - u) / s) - phi((kk - u) / s)
        p1 = min(max(p1, 0.0), 1.0)
        hs += hbin(p1); hm += -math.log2(max(p1, 1 - p1))
    return hs / n, hm / n

def main():
    t_fast, t_slow, i_fast, i_slow, div = 1.950e-9, 3.608e-9, 2.50e-4, 2.55e-4, 64
    kf, ks = kappa(i_fast), kappa(i_slow)
    if len(sys.argv) > 1:      # kappa measured by the transient-noise simulation (run_ring_trnoise.py), both rings
        kf = ks = float(sys.argv[1]); print('using simulated kappa')
    t_acc = div * t_slow
    sig = math.sqrt(kf * kf + ks * ks) * math.sqrt(t_acc)
    print("kappa fast %.2e sqrt(s), slow %.2e sqrt(s)" % (kf, ks))
    print("period jitter of the fast ring: %.3f ps (%.4f %% of the period)" % (kf * math.sqrt(t_fast) * 1e12, 100 * kf / math.sqrt(t_fast)))
    print("sampling interval %.1f ns; accumulated relative jitter %.2f ps = %.2e of the fast period" % (t_acc * 1e9, sig * 1e12, sig / t_fast))
    for mult in (1, 3, 10, 30):
        hs, hm = entropy_per_sample(mult * sig / t_fast)
        print("jitter x%-3d sigma/T=%.2e  Shannon %.4f bit/sample  min-entropy %.4f bit/sample  -> %.1f bits in 512 samples" % (
            mult, mult * sig / t_fast, hs, hm, 512 * hm))
    print("accumulation needed for a given min-entropy per sample (thermal only):")
    for target in (0.5, 0.9):
        lo, hi = 1e-3, 3.0
        for _ in range(40):
            mid = math.sqrt(lo * hi)
            if entropy_per_sample(mid, 4000)[1] < target: lo = mid
            else: hi = mid
        t_need = (hi * t_fast) ** 2 / (kf * kf + ks * ks)
        print("  h_min >= %.1f needs sigma/T >= %.3f -> %.2f ms between samples (divider 2^%.1f), %.0f raw bits/s; with 10x jitter %.3f ms" % (
            target, hi, t_need * 1e3, math.log2(t_need / t_slow), 1 / t_need, t_need * 1e1))
main()
