#!/usr/bin/env python3
"""Transient-noise simulation of a NAND2 ring (nand2_1 cells, 5 fF per stage assumed).

ngspice has no device noise in transient analysis, so every ring node gets an independent white current
source (TRNOISE) whose spectral density is the stage's thermal output-current noise from the foundry
BSIM4 noise model (cell_noise_psd.sp: 2.4e-24 to 6.2e-24 A^2/Hz along a transition; S0 = 4.0e-24 used).
TRNOISE(NA NT): Gaussian samples of rms NA every NT, linearly interpolated: one-sided density 2*NA^2*NT
up to about 1/(2 NT).  The noise is scaled by --scale (amplitude) so that the jitter stands clear of the
integrator's own timing error; jitter is linear in the amplitude for small noise (checked with two scales
and a noise-free control), so kappa = kappa_measured / scale.

  python3 run_ring_trnoise.py --stages 7 --scale 10 --seed 1 --tstop 3e-6 --out r7_a10_s1
writes <out>.dat (time, v(osc)); analyse with analyze_ring_trnoise.py on the host.
Linux only; ngspice in container dregg180-h4-spice with the lane's .spiceinit (hsa mode).
"""
import argparse, subprocess, math, platform
ap = argparse.ArgumentParser()
ap.add_argument("--stages", type=int, default=7); ap.add_argument("--scale", type=float, default=10.0)
ap.add_argument("--seed", type=int, default=1); ap.add_argument("--tstop", type=float, default=3e-6)
ap.add_argument("--s0", type=float, default=4.0e-24); ap.add_argument("--nt", type=float, default=4e-12)
ap.add_argument("--corner", default="typical"); ap.add_argument("--vdd", type=float, default=5.0); ap.add_argument("--temp", type=float, default=27)
ap.add_argument("--out", default="ring"); ap.add_argument("--pdk", default="/spice/pdk")
a = ap.parse_args()
if platform.system() != "Linux": raise SystemExit("run on the Linux build box, not the Mac")
na = a.scale * math.sqrt(a.s0 / (2 * a.nt))
d = ["* ring %d stages, trnoise scale %g seed %d" % (a.stages, a.scale, a.seed),
     '.include "%s/ngspice/design.ngspice"' % a.pdk, ".param sw_stat_global=0 sw_stat_mismatch=0",
     '.lib "%s/ngspice/sm141064.ngspice" %s' % (a.pdk, a.corner), ".temp %g" % a.temp,
     '.include "%s/gf180mcu_fd_sc_mcu7t5v0.spice"' % a.pdk,
     ".options klu method=gear reltol=1e-5 seed=%d" % a.seed,
     "VDD vdd 0 %g" % a.vdd, "VEN en 0 PWL(0 0 0.4n 0 0.6n %g)" % a.vdd]
for i in range(a.stages):
    inp = "n%d" % (i if i else a.stages); out = "n%d" % (i + 1)
    g = "en" if i == 0 else inp
    d.append("X%d %s %s %s vdd vdd 0 0 gf180mcu_fd_sc_mcu7t5v0__nand2_1" % (i, inp, g, out))
    d.append("C%d %s 0 5.0f" % (i, out))
    d.append("IN%d %s 0 dc 0 trnoise(%g %g 0 0)" % (i, out, max(na, 1e-18), a.nt))
d += [".save v(n%d)" % a.stages, ".control", "tran 2p %g" % a.tstop, "wrdata %s.dat v(n%d)" % (a.out, a.stages), ".endc", ".end"]
open(a.out + ".sp", "w").write("\n".join(d) + "\n")
r = subprocess.run(["ngspice", "-b", a.out + ".sp"], capture_output=True, text=True)
open(a.out + ".log", "w").write(r.stdout[-4000:] + r.stderr[-2000:])
print(a.out, "done, NA = %.3e A rms" % na)
