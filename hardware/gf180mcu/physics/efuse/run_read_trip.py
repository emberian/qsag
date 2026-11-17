#!/usr/bin/env python3
"""Read threshold of the gf180mcu_re_efuse sense amplifier.

The sense amplifier (efuse_senseamp in efuse_async_mem_1x8.spice) precharges net1 high, then a 0.82/0.60 um
NFET connects net1 to the bit line; the fuse must pull net1 low against the latch's feedback inverter
(inv_1, PMOS 1.22/0.50 um).  A fuse that wins reads as unblown (OUT = 0); otherwise OUT stays 1 (blown).
This finds, per corner, the fuse resistance R_trip at which the result changes: a programmed fuse must end
above it, an intact fuse must stay below it, with margin on both sides.

Circuit: async macro column (two off programming PMOS on the bit line as load) and the array column
(one PMOS + select NFET 30.5/0.60 um in series with the fuse).  PRESET_N low 5 ns, then SENSE high for
TSENSE (default 20 ns; the documented minimum is 4 ns async / 10 ns sync).
Linux only; ngspice in container dregg180-h4-spice.
"""
import argparse, json, os, re, subprocess, sys, tempfile, platform

RL = [100, 150, 200, 300, 400, 500, 600, 700, 800, 900, 1000, 1200, 1400, 1600, 1800, 2000, 2400, 2800, 3200,
      3600, 4000, 4500, 5000, 6000, 7000, 8000, 10000, 12000, 15000, 20000, 30000, 50000, 100000]
DECK = """* efuse read trip {macro} {corner} {vdd} {temp}
.include "{pdk}/design.ngspice"
.lib "{pdk}/sm141064.ngspice" {corner}
.param sw_stat_global=0 sw_stat_mismatch=0
.temp {temp}
.param vdd={vdd}
VDD vdd 0 {{vdd}}
VPR presetn 0 PWL(0 0 5n 0 5.2n {{vdd}})
VSE sense 0 PWL(0 0 7n 0 7.2n {{vdd}} {t1}n {{vdd}} {t2}n 0)
VCP colprogn 0 {{vdd}}
.SUBCKT inv_1 I ZN VDD VNW VPW VSS
X0 ZN I VSS VPW nfet_06v0 W=8.2e-07 L=6e-07
X1 ZN I VDD VNW pfet_06v0 W=1.22e-06 L=5e-07
.ENDS
.subckt efuse_senseamp VSS VPW VDD PRESET_N OUT SENSE FUSE
X2 net1 PRESET_N VDD VDD pfet_06v0 L=0.5u W=2.44u nf=2
X1 net2 OUT VDD VDD VPW VSS inv_1
X2b net1 net2 VDD VDD VPW VSS inv_1
X3 net2 net1 VDD VDD VPW VSS inv_1
X1n net1 SENSE FUSE VPW nfet_06v0 L=0.60u W=0.82u
.ends
{column}
Xsa 0 0 vdd presetn out sense bl efuse_senseamp
CL out 0 10f
.control
foreach rv {rlist}
  alter rfuse $rv
  tran 20p {tstop}n
  meas tran vout find v(out) at={tm}n
end
.endc
.end
"""
COL = {
 "async": """Xp0 bl colprogn vdd vdd pfet_06v0 L=0.50u W=62u nf=2
Xp1 bl colprogn vdd vdd pfet_06v0 L=0.50u W=62u nf=2
rfuse bl 0 200""",
 "array": """Xp0 bl colprogn vdd vdd pfet_06v0 L=0.50u W=76.5u nf=2
rfuse bl c 200
Xn c vdd 0 0 nfet_06v0 L=0.60u W=30.5u""",
}

def run(a, macro, corner, vdd, temp):
    t1 = 7.2 + a.tsense; deck = DECK.format(macro=macro, corner=corner, vdd=vdd, temp=temp, pdk=a.pdk, column=COL[macro],
                                            rlist=" ".join(map(str, RL)), t1=t1, t2=t1 + 0.2, tstop=t1 + 3, tm=t1 + 2.5)
    with tempfile.NamedTemporaryFile("w", suffix=".sp", delete=False, dir=".") as f:
        f.write(deck); name = f.name
    out = subprocess.run([a.ngspice, "-b", name], capture_output=True, text=True, timeout=600).stdout
    os.unlink(name)
    v = [float(x) for x in re.findall(r"^vout\s*=\s*(\S+)", out, re.M)]
    if len(v) != len(RL):
        sys.stderr.write(out[-2000:]); raise SystemExit("parse failure")
    blown = [x > vdd / 2 for x in v]
    lo = max([r for r, b in zip(RL, blown) if not b], default=None)   # largest R still read as intact
    hi = min([r for r, b in zip(RL, blown) if b], default=None)       # smallest R read as blown
    mono = all((not b0) or b1 for b0, b1 in zip(blown[:-1], blown[1:]))
    return dict(read_intact_up_to=lo, read_blown_from=hi, monotone=mono)

def main():
    if platform.system() != "Linux": raise SystemExit("run on the Linux build box, not the Mac")
    ap = argparse.ArgumentParser(); ap.add_argument("--pdk", default="/spice/pdk/ngspice"); ap.add_argument("--ngspice", default="ngspice")
    ap.add_argument("--tsense", type=float, default=20.0); ap.add_argument("--out", default="read_trip.json")
    a = ap.parse_args(); res = {}
    for macro in COL:
        for corner in ("typical", "ss", "ff", "sf", "fs"):
            for vdd in (4.5, 5.0, 5.5):
                for temp in (-40, 27, 125):
                    k = "%s/%s/%.1f/%d" % (macro, corner, vdd, temp); res[k] = run(a, macro, corner, vdd, temp)
                    print("%-26s intact up to %s ohm, blown from %s ohm%s" % (k, res[k]["read_intact_up_to"], res[k]["read_blown_from"],
                                                                             "" if res[k]["monotone"] else "  NON-MONOTONE"), flush=True)
    json.dump({"tsense_ns": a.tsense, "R": RL, "result": res}, open(a.out, "w"))
main()
