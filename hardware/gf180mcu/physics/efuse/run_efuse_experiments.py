#!/usr/bin/env python3
"""Experiments with fuse_thermal.py.  Run on a build box, not the Mac:

  python run_efuse_experiments.py verify   # grid / step refinement, energy balance
  python run_efuse_experiments.py valid    # published fuses (Kothandaraman 2002, Tonti 2003)
  python run_efuse_experiments.py corners  # gf180 cell, both macros, 27 PVT corners each
  python run_efuse_experiments.py sens     # sensitivity to the unknown fuse parameters
  python run_efuse_experiments.py margin   # critical drive scale by bisection
Results go to results/<name>.json.  --jobs N (default 12).
"""
import json, os, sys, time, copy
os.environ.setdefault("OMP_NUM_THREADS", "1"); os.environ.setdefault("OPENBLAS_NUM_THREADS", "1")
import numpy as np
from multiprocessing import Pool
import fuse_thermal as ft

HERE = os.path.dirname(os.path.abspath(__file__))
DRIVE = json.load(open(os.path.join(HERE, "drive.json")))["curves"]
TAMB = {-40: 233.15, 27: 300.15, 125: 398.15}
# production sweeps: coarse grid, large steps, step cap.  Mode "verify" compares them with the base and fine settings.
FAST_GRID = dict(hlink=0.09, hpad=0.2)
FAST_RUN = dict(dT_step=120.0, max_steps=2500)

def mkparams(over):
    p = ft.Params()
    for k, v in over.items(): setattr(p, k, v)
    return p

def one(job):
    """job: dict(tag, geom kwargs, params overrides, drive spec, t_end, grid)."""
    t0 = time.time()
    g = ft.geom_gf180(**job.get("geom", {})) if job.get("kind", "gf180") == "gf180" else ft.geom_generic(**job["geom"])
    p = mkparams(job.get("params", {}))
    f = ft.Fuse(g, p, **job.get("grid", FAST_GRID))
    d = job["drive"]
    if d[0] == "table": drv = ft.table_drive(DRIVE[d[1]], d[2] if len(d) > 2 else 1.0)
    elif d[0] == "const": drv = (lambda R, t, i=d[1]: i)
    elif d[0] == "limited": drv = ft.limited_source(d[1], d[2], d[3])
    elif d[0] == "nfet": drv = ft.nfet_drive(d[1], d[2], d[3], d[4])
    rcold = f.r_cold()
    H = f.run(drv, t_end=job.get("t_end", 50e-6), **job.get("run", FAST_RUN))
    s = ft.summarize(H); s["tag"] = job["tag"]; s["Rcold"] = rcold; s["wall"] = time.time() - t0
    s["cells"] = f.N
    # plateau = average over the last 20 % of the run
    t = np.array(H["t"]); m = t > 0.8 * t[-1]
    for k in ("I", "R", "P", "Tmax", "Tlink", "fmolten"):
        s["pl_" + k] = float(np.mean(np.array(H[k])[m]))
    if job.get("keep"):
        s["hist"] = {k: H[k] for k in ("t", "I", "R", "P", "Tmax", "Tlink", "fmolten")}
    if job.get("energy"):
        # energy balance: delivered = stored (sensible + latent) + conducted to the substrate (not tracked)
        s["E_in"] = float(np.trapezoid(H["P"], H["t"]))
    return s

def run(name, jobs, nproc):
    os.makedirs(os.path.join(HERE, "results"), exist_ok=True)
    t0 = time.time()
    with Pool(nproc) as pool:
        res = []
        part = open(os.path.join(HERE, "results", name + ".partial.jsonl"), "w")
        for r in pool.imap_unordered(one, jobs):
            res.append(r); part.write(json.dumps(r) + "\n"); part.flush()
            print("%-44s R0=%6.1f I0=%5.1fmA melt=%s bridge=%s end=%-6s | plateau I=%5.1fmA R=%6.1f P=%5.1fmW T=%5.0fK fm=%.2f (%.0fs)" % (
                r["tag"], r["Rcold"], r["I0"] * 1e3, fmt(r.get("t_melt_onset")), fmt(r.get("t_melt_bridge")), ("boil" if "t_boil" in r else "steady" if "t_steady" in r else "cap" if "t_step_cap" in r else "t_end"),
                r["pl_I"] * 1e3, r["pl_R"], r["pl_P"] * 1e3, r["pl_Tmax"], r["pl_fmolten"], r["wall"]), flush=True)
    res.sort(key=lambda r: r["tag"])
    json.dump(res, open(os.path.join(HERE, "results", name + ".json"), "w"), indent=0)
    print("wrote results/%s.json  %d runs  %.0fs" % (name, len(res), time.time() - t0))
    return res

def fmt(x): return "   -   " if x is None else "%7.1e" % x

def corner_key(macro, c, v, t): return "%s/%s/%.1f/%d" % (macro, c, v, t)

def calib_rs(kind, geom, params, target):
    """Silicide sheet resistance that gives the published cold resistance."""
    rs = []
    for v in (5.0, 20.0):
        p = dict(params); p["rs_sil"] = v
        g = ft.geom_generic(**geom) if kind == "generic" else ft.geom_gf180(**geom)
        rs.append(ft.Fuse(g, mkparams(p)).r_cold())
    a = (rs[1] - rs[0]) / 15.0; b = rs[0] - 5 * a
    return (target - b) / a

def main():
    mode = sys.argv[1]; nproc = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 12
    nom = "async/typical/5.0/27"
    if mode == "verify":
        jobs = []
        for tag, grid, runkw in (("fast", FAST_GRID, FAST_RUN), ("base", {}, {}),
                                 ("fine-grid", dict(hlink=0.0225, hpad=0.07), {}),
                                 ("coarse-grid", dict(hlink=0.09, hpad=0.2), {}),
                                 ("small-steps", {}, dict(dT_step=20.0, dt0=1e-11, max_steps=20000)),
                                 ("large-steps", {}, dict(dT_step=120.0))):
            for dname, d in (("table", ("table", nom)), ("i8mA", ("const", 8e-3)), ("i4mA", ("const", 4e-3))):
                jobs.append(dict(tag="verify/%s/%s" % (dname, tag), grid=grid, run=runkw, drive=d, t_end=20e-6, energy=True))
        jobs += [dict(tag="verify/table/dTmelt40", params=dict(dT_melt=40.0), drive=("table", nom), t_end=20e-6),
                 dict(tag="verify/i8mA/dTmelt40", params=dict(dT_melt=40.0), drive=("const", 8e-3), t_end=20e-6)]
        run("verify", jobs, nproc)
    elif mode == "valid":
        jobs = []
        # Kothandaraman, Iyer, Iyer, IEEE EDL 23(9) 2002, Fig. 1, 2, 5: 0.12 um CMOS, 30 nm CoSi2 on 150 nm p+ poly on
        # STI, link length 1.2 um, width <= 0.12 um, R0 = 120 ohm, FS = 3.3 V, 10 ohm series, select NFET.
        # Measured: peak 10 mA; plateau (region B, 50-200 us) 7.3 mA with 0.6 V on the NFET drain, i.e.
        # 2.63 V across the fuse = 360 ohm, 19 mW.  Drive model from those two points: saturation 10 mA,
        # triode resistance 0.6 V / 7.3 mA = 82 ohm.  With a higher gate voltage: rupture in 1-5 us.
        # Assumed (not in the paper): STI depth, pad sizes, dielectric above.
        for wd, fox, pname, pov, drives in (
                (0.12, 0.30, "nom", {}, ("gate1.5V", "0.5x", "0.3x", "2x")),
                (0.12, 0.40, "nom", {}, ("gate1.5V",)), (0.10, 0.30, "nom", {}, ("gate1.5V",)),
                (0.12, 0.30, "Tm1532", dict(T_melt=1532.0), ("gate1.5V",)),
                (0.12, 0.30, "tcr_sat", dict(tc2=0.0, tcr_cap=4.0), ("gate1.5V",)),
                (0.12, 0.30, "kox1.3", dict(k_ox_scale=1.3), ("gate1.5V",))):
            geom = dict(L=1.2, Wd=wd, pad_an=(1.0, 0.5), pad_ca=(2.0, 1.0), t_sil=0.03, t_fox=fox, t_poly=0.18, t_ild=0.6, name="kothandaraman")
            rs = calib_rs("generic", geom, pov, 120.0)
            for iname, isat, ron in (("gate1.5V", 10e-3, 82.0), ("0.5x", 5e-3, 164.0), ("0.3x", 3e-3, 273.0), ("2x", 20e-3, 41.0)):
                if iname not in drives: continue
                p = dict(rs_sil=rs); p.update(pov)
                jobs.append(dict(tag="valid/koth/w%.2f/fox%.2f/%s/%s" % (wd, fox, pname, iname), kind="generic", geom=geom,
                                 params=p, drive=("nfet", 3.3, 10.0, ron, isat), t_end=200e-6, keep=True))
        # Tonti et al., IRW 2003, E-fuse B: neck 0.2 x 2.0 um, WSi2 50 nm on n++ poly 100 nm on 250 nm isolation,
        # ~350 ohm intrinsic, 5 mA maintained, 4.7 V; 250 us programs (100 %), 25 us does not.
        geom = dict(L=2.0, Wd=0.2, pad_an=(1.5, 0.6), pad_ca=(1.5, 0.6), t_sil=0.05, t_fox=0.25, t_poly=0.15, t_ild=0.69, name="tonti-B")
        rs = calib_rs("generic", geom, {}, 350.0)
        for iname, ilim in (("5mA", 5e-3), ("3mA", 3e-3), ("2mA", 2e-3), ("8mA", 8e-3)):
            jobs.append(dict(tag="valid/tontiB/%s" % iname, kind="generic", geom=geom, params=dict(rs_sil=rs),
                             drive=("limited", 4.7, ilim, 0.0), t_end=250e-6, keep=True))
        run("valid", jobs, nproc)
    elif mode == "corners":
        jobs = []
        for macro in ("async", "array"):
            for c in ("typical", "ss", "ff"):
                for v in (4.5, 5.0, 5.5):
                    for t in (-40, 27, 125):
                        k = corner_key(macro, c, v, t)
                        jobs.append(dict(tag="corners/" + k, params=dict(T0=TAMB[t]), drive=("table", k), t_end=20e-6,
                                         keep=(k in (nom, "array/ss/4.5/125", "async/ff/5.5/-40"))))
        run("corners", jobs, nproc)
    elif mode == "sens":
        jobs = []
        cases = [("async/typical/5.0/27", 27), ("array/typical/5.0/27", 27), ("array/ss/4.5/125", 125)]
        if "--cases" in sys.argv: cases = [cases[int(i)] for i in sys.argv[sys.argv.index("--cases") + 1].split(",")]
        var = [("nominal", {}, {})]
        for rs in (1.0, 2.0, 3.0, 4.0, 5.0, 10.0, 15.0, 25.0): var.append(("rs_sil=%g" % rs, dict(rs_sil=rs), {}))
        var += [("t_fox=0.25", {}, dict(t_fox=0.25)), ("t_fox=0.40", {}, dict(t_fox=0.40)),
                ("t_sil=0.02", {}, dict(t_sil=0.02)), ("t_sil=0.05", {}, dict(t_sil=0.05)),
                ("k_ox*0.8", dict(k_ox_scale=0.8), {}), ("k_ox*1.2", dict(k_ox_scale=1.2), {}),
                ("T_melt=1532", dict(T_melt=1532.0), {}), ("r_contact=2", dict(r_contact=2.0), {}),
                ("r_contact=40", dict(r_contact=40.0), {}), ("k_poly=15", dict(k_poly300=15.0), {}),
                ("k_poly=45", dict(k_poly300=45.0), {}), ("tcr_saturating", dict(tc2=0.0, tcr_cap=4.0), {}),
                ("rs_poly=1000", dict(rs_poly=1000.0), {}),
                ("rs=3,k_ox*1.2,fox0.25", dict(rs_sil=3.0, k_ox_scale=1.2), dict(t_fox=0.25))]
        for k, t in cases:
            for name, pov, gov in var:
                p = dict(T0=TAMB[t]); p.update(pov)
                jobs.append(dict(tag="sens/%s/%s" % (k, name), params=p, geom=gov, drive=("table", k), t_end=20e-6))
        run("sens" + ("_" + sys.argv[sys.argv.index("--cases") + 1].replace(",", "") if "--cases" in sys.argv else ""), jobs, nproc)
    elif mode == "margin":
        # critical drive scale s*: smallest multiple of the corner's I(R) that still melts the link within 50 us.
        cases = []
        for k, t in (("async/typical/5.0/27", 27), ("async/ss/4.5/125", 125), ("array/typical/5.0/27", 27), ("array/ss/4.5/125", 125)):
            for name, pov in (("nominal", {}), ("rs_sil=3", dict(rs_sil=3.0)), ("rs_sil=15", dict(rs_sil=15.0))):
                cases.append((k, t, name, pov))
        lo = {c[:3]: 0.03 for c in cases}; hi = {c[:3]: 1.0 for c in cases}; allres = []
        for it in range(5):
            jobs = []
            for k, t, name, pov in cases:
                s = (lo[(k, t, name)] * hi[(k, t, name)]) ** 0.5
                p = dict(T0=TAMB[t]); p.update(pov)
                jobs.append(dict(tag="margin/%s/%s/s=%.4f" % (k, name, s), params=p, drive=("table", k, s),
                                 run=dict(stop_at_bridge=True, dT_step=120.0, max_steps=1200), t_end=5e-6, meta=(k, t, name, s)))
            with Pool(nproc) as pool: res = pool.map(one, jobs)
            for j, r in zip(jobs, res):
                k, t, name, s = j["meta"]
                melted = r.get("t_melt_onset") is not None
                if melted: hi[(k, t, name)] = s
                else: lo[(k, t, name)] = s
                r["scale"] = s; allres.append(r)
                print("%-52s melt=%s Tmax=%.0f I0=%.2fmA" % (r["tag"], melted, r["Tmax"], r["I0"] * 1e3), flush=True)
            json.dump(dict(bracket={"%s|%s" % (k, name): dict(lo=lo[(k, t, name)], hi=hi[(k, t, name)]) for k, t, name, _ in cases}, runs=allres),
                      open(os.path.join(HERE, "results", "margin.json"), "w"), indent=0)
        out = {"%s|%s" % (k, name): dict(lo=lo[(k, t, name)], hi=hi[(k, t, name)]) for k, t, name, _ in cases}
        json.dump(dict(bracket=out, runs=allres), open(os.path.join(HERE, "results", "margin.json"), "w"), indent=0)
        for kk, v in out.items(): print("%-40s s* in [%.3f, %.3f]  margin = %.1fx" % (kk, v["lo"], v["hi"], 1 / v["hi"]))

if __name__ == "__main__":
    main()
