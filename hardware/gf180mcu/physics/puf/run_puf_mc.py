#!/usr/bin/env python3
"""Ring-oscillator PUF Monte Carlo with the gf180mcu local-mismatch models.

Ring = dregg_puf_ro5 topology as in ../../spice/ro_puf_pelgrom_mc.sp (buf_2 enable
isolation + five nand2_1, 5 fF assumed wire load per stage).

Statistical switches (design.ngspice + sm141064.ngspice):
  sw_stat_mismatch=1  per-instance Pelgrom terms inside the nfet_06v0/pfet_06v0 subcircuits
                      (delvto = agauss(0, 0.7071*par_vth*1e-6/sqrt(Weff*Leff), 1), mulu0 likewise)
  sw_stat_global=1    die-to-die terms (.lib statistical: mc_sig_vth, mc_toxe, mc_xl, ...) times mc_skew
  .options seed=N     required; .spiceinit setseed alone does not seed agauss (see ../../spice/README.md)

Modes:
  mc    --seeds a,b,c --rings 64 [--corner typical --vdd 5.0 --temp 27] [--global 1]
  sens  nominal rings (mismatch off) with deliberate asymmetries: load, supply
Output: JSON with per-ring frequencies.  Linux only; ngspice in container dregg180-h4-spice.
"""
import argparse, json, os, re, subprocess, sys, platform
from concurrent.futures import ThreadPoolExecutor

HEAD = """* RO PUF {mode} seed={seed}
.include "{pdk}/ngspice/design.ngspice"
.param sw_stat_global={glob} sw_stat_mismatch={mm}
.lib "{pdk}/ngspice/sm141064.ngspice" {corner}
{statlib}
.param vdd_val={vdd}
.temp {temp}
.include "{pdk}/gf180mcu_fd_sc_mcu7t5v0.spice"
.options klu method=gear reltol=1e-4 seed={seed}
VVDD VDD 0 {{vdd_val}}
VVSS VSS 0 0
VEN EN 0 PWL(0 0 0.4n 0 0.6n {{vdd_val}})
.subckt ring en osc vdd vss cl=5.0f c0=5.0f
XI en  eni    vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__buf_2
X0 osc eni n1 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C0 n1  vss {{c0}}
X1 n1  n1  n2 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C1 n2  vss {{cl}}
X2 n2  n2  n3 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C2 n3  vss {{cl}}
X3 n3  n3  n4 vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C3 n4  vss {{cl}}
X4 n4  n4  osc vdd vdd vss vss gf180mcu_fd_sc_mcu7t5v0__nand2_1
C4 osc vss {{cl}}
.ends ring
"""
TAIL = """.param vmid='vdd_val/2'
.tran 10p 60n 0 10p
{meas}
.end
"""

def meas(i, node):
    return (".meas tran period_%d TRIG v(%s) VAL=vmid RISE=5 TARG v(%s) VAL=vmid RISE=25\n" % (i, node, node))

def run_deck(a, text, name):
    path = os.path.join(a.work, name + ".sp")
    open(path, "w").write(text)
    out = subprocess.run(["timeout", "850", a.ngspice, "-b", path], capture_output=True, text=True).stdout
    open(os.path.join(a.work, name + ".log"), "w").write(out)
    per = {int(k): float(v) for k, v in re.findall(r"^period_(\d+)\s*=\s*(\S+)", out, re.M)}
    cur = re.findall(r"^iavg\s*=\s*(\S+)", out, re.M)
    return per, (float(cur[0]) if cur else None)

def mc(a, seed):
    # the "statistical" section is itself a complete MOS library (typical centre + die-to-die terms)
    corner = "statistical" if a.glob else a.corner
    t = HEAD.format(mode="mc", seed=seed, pdk=a.pdk, glob=a.glob, mm=1, corner=corner, vdd=a.vdd, temp=a.temp, statlib="")
    m = ""
    for i in range(a.rings):
        t += "XR%d EN OSC%d VDD VSS ring\n" % (i, i); m += meas(i, "OSC%d" % i)
    per, _ = run_deck(a, t + TAIL.format(meas=m), "mc_%s_%s_%s_g%d_s%d" % (a.corner, a.vdd, a.temp, a.glob, seed))
    return seed, [20.0 / per[i] if i in per else None for i in range(a.rings)]

def sens(a):
    t = HEAD.format(mode="sens", seed=1, pdk=a.pdk, glob=0, mm=0, corner=a.corner, vdd=a.vdd, temp=a.temp, statlib="")
    cases = [("nominal", "cl=5.0f c0=5.0f", "VDD"), ("load_all_+5pct", "cl=5.25f c0=5.25f", "VDD"),
             ("load_one_stage_+0.5fF", "cl=5.0f c0=5.5f", "VDD"), ("vdd_-50mV", "cl=5.0f c0=5.0f", "VDDL"),
             ("isupply", "cl=5.0f c0=5.0f", "VDDM")]
    t += "VVDDL VDDL 0 {vdd_val-0.05}\nVM VDD VDDM 0\n"
    m = ""
    for i, (name, par, sup) in enumerate(cases):
        t += "XR%d EN OSC%d %s VSS ring %s\n" % (i, i, sup, par); m += meas(i, "OSC%d" % i)
    m += ".meas tran iavg AVG i(VM) FROM=20n TO=60n\n"
    t += ".save all i(VM)\n"
    per, iavg = run_deck(a, t + TAIL.format(meas=m), "sens_%s_%s_%s" % (a.corner, a.vdd, a.temp))
    return {"cases": {c[0]: 20.0 / per[i] for i, c in enumerate(cases) if i in per}, "iavg_ring_A": iavg}

def main():
    if platform.system() != "Linux": raise SystemExit("run on the Linux build box, not the Mac")
    ap = argparse.ArgumentParser()
    ap.add_argument("mode"); ap.add_argument("--pdk", default="/spice/pdk"); ap.add_argument("--ngspice", default="ngspice")
    ap.add_argument("--seeds", default="1"); ap.add_argument("--rings", type=int, default=64)
    ap.add_argument("--corner", default="typical"); ap.add_argument("--vdd", type=float, default=5.0)
    ap.add_argument("--temp", type=float, default=27); ap.add_argument("--global", dest="glob", type=int, default=0)
    ap.add_argument("--jobs", type=int, default=8); ap.add_argument("--work", default="work"); ap.add_argument("--out", default="puf.json")
    a = ap.parse_args(); os.makedirs(a.work, exist_ok=True)
    if a.mode == "sens":
        res = sens(a)
    else:
        seeds = [int(s) for s in a.seeds.split(",")]
        with ThreadPoolExecutor(a.jobs) as ex: res = {str(s): f for s, f in ex.map(lambda s: mc(a, s), seeds)}
    json.dump({"args": vars(a), "result": res}, open(a.out, "w"))
    print(json.dumps(res)[:600])
main()
