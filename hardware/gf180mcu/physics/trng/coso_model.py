#!/usr/bin/env python3
"""Stochastic model of a coherent-sampling ring pair (numpy).

Two free-running rings, periods T and T(1+d).  Ring B's rising edge clocks a flip-flop that samples ring A;
the flip-flop output is a slow beat square wave of about 1/|d| ring periods.  A counter clocked by ring B
counts the periods between successive rising edges of the beat; the raw output is the count C_k (the low
bits are the random part).

Noise model: each ring period is T_i + kappa*sqrt(T_i)*N(0,1), independent (white FM, thermal).  kappa is
the accumulation constant from the transient-noise simulation.  Flicker noise, supply noise and locking are
NOT in the model: they are what the health test and the design rules have to deal with.
Theory (drifted Brownian first passage): var(C) = 2 kappa^2 T^2 / dT^3 with dT = |d| T.

  python3 coso_model.py            # table over d for the proposed 17-stage rings
"""
import sys, math, numpy as np

def counts(T, d, kappa, nbeats, seed=1, chunk=2_000_000):
    rng = np.random.default_rng(seed)
    Ta, Tb = T, T * (1 + d)
    ta = tb = 0.0; out = []; prev = None; run = 0
    while len(out) < nbeats:
        pa = Ta + kappa * math.sqrt(Ta) * rng.standard_normal(chunk)
        pb = Tb + kappa * math.sqrt(Tb) * rng.standard_normal(chunk)
        ea = ta + np.cumsum(pa); eb = tb + np.cumsum(pb)
        lim = min(ea[-1], eb[-1])                          # only use the stretch both sequences cover
        nb = int(np.searchsorted(eb, lim)); na = int(np.searchsorted(ea, lim))
        eb_u = eb[:nb]
        idx = np.searchsorted(ea, eb_u, side="right") - 1   # last A edge before each B edge
        start = np.where(idx >= 0, ea[np.maximum(idx, 0)], ta)
        per = np.where(idx >= 0, pa[np.minimum(np.maximum(idx, 0) + 1, chunk - 1)], Ta)
        s = ((eb_u - start) / per) < 0.5                   # sampled level of A (high in the first half period)
        if prev is None: prev = bool(s[0])
        sp = np.concatenate(([prev], s[:-1]))
        rise = np.nonzero(s & ~sp)[0]
        last = -run
        for r in rise:
            out.append(int(r - last)); last = r
        run = nb - last; prev = bool(s[-1])
        ta = ea[na - 1] if na else ta; tb = eb[nb - 1] if nb else tb
        # restart both generators from the last used edges (unused tail discarded: independent increments)
    return np.array(out[1:nbeats + 1])

def minent_lsb(c, kmax=6):
    """Conservative per-bit min-entropy estimates of the LSB stream: most-common-value bound and the
    best order-k Markov predictor (k = 1..kmax), each with a 99 % upper confidence bound on the hit rate."""
    b = (c & 1).astype(np.int64); n = len(b)
    p = max(b.mean(), 1 - b.mean()); pu = min(1.0, p + 2.576 * math.sqrt(p * (1 - p) / n))
    h = [-math.log2(pu)]
    for k in range(1, kmax + 1):
        ctx = np.zeros(n - k, dtype=np.int64)
        for j in range(k): ctx = (ctx << 1) | b[j:n - k + j]
        nxt = b[k:]
        tot = np.bincount(ctx, minlength=1 << k).astype(float); one = np.bincount(ctx, weights=nxt, minlength=1 << k)
        hit = np.maximum(one, tot - one).sum() / (n - k)
        hu = min(1.0, hit + 2.576 * math.sqrt(hit * (1 - hit) / (n - k)))
        h.append(-math.log2(hu))
    return min(h), h[0]

def stats(c):
    dc = np.diff(c)
    return c.mean(), c.std(), 0.5 * np.mean(dc.astype(float) ** 2), len(np.unique(c))

if __name__ == "__main__":
    T = float(sys.argv[1]) if len(sys.argv) > 1 else 4.72e-9
    kappa = float(sys.argv[2]) if len(sys.argv) > 2 else 4.1e-9
    nb = int(sys.argv[3]) if len(sys.argv) > 3 else 60000
    print("T = %.3f ns, kappa = %.2e sqrt(s) per ring" % (T * 1e9, kappa))
    print("%-9s %-9s %-10s %-10s %-9s %-8s %-9s %-11s %-11s %-10s" % ("d (%)", "dT (ps)", "mean C", "sd C", "theory", "V", "values", "h_min LSB", "(bias only)", "rate kbit/s"))
    for d in (0.0003, 0.0005, 0.001, 0.0015, 0.002, 0.003, 0.004, 0.006, 0.01):
        for kap in (kappa, 0.0):
            n = nb if d >= 0.001 else nb // 4
            c = counts(T, d, kap, n)
            m, sd, V, nv = stats(c); hm, hb = minent_lsb(c)
            th = math.sqrt(2) * kap * T / (d * T) ** 1.5
            print("%-9.3f %-9.2f %-10.1f %-10.3f %-9.3f %-8.3f %-9d %-11.3f %-11.3f %-10.0f %s" % (
                100 * d, d * T * 1e12, m, sd, th, V, nv, hm, hb, 1e-3 / (m * T), "" if kap else "<- no noise (deterministic pattern)"))
