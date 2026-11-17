#!/usr/bin/env python3
"""Programming-drive characteristic of the gf180mcu_re_efuse macros.

For each process corner / supply / temperature, sweep an ideal resistor in the
fuse position and record the current the macro's programming path delivers.
The result I(R) is the load line used by fuse_thermal.py.

Circuits (taken from libs.ref/gf180mcu_re_efuse/spice/*.spice):
  async : 2 x pfet_06v0 L=0.5u W=62u nf=2 from VDD to bitline; fuse bitline->VSS
          (efuse_async_mem_1x8)
  array : 1 x pfet_06v0 L=0.5u W=76.5u nf=2 from VDD to bitline; fuse; then
          nfet_06v0 L=0.6u W=30.5u select to VSS (efuse_array_64x32 bit cell)
Assumed (not in the netlist): RPAR ohms of supply + bitline wiring in series.

Runs ngspice (Linux only; on hbox inside container dregg180-h4-spice):
  python3 run_prog_drive.py --pdk /spice/pdk/ngspice --out drive.json
"""
import argparse, json, subprocess, sys, tempfile, os, re, platform

RLIST = [1, 5, 10, 20, 30, 40, 50, 60, 70, 80, 100, 120, 150, 200, 250, 300, 400, 500,
         700, 1000, 1500, 2000, 3000, 5000, 10000, 30000, 100000]

DECK = """* efuse programming drive, {macro} {corner} {vdd} V {temp} C
.include "{pdk}/design.ngspice"
.lib "{pdk}/sm141064.ngspice" {corner}
.param sw_stat_global=0 sw_stat_mismatch=0
.temp {temp}
VDD vddx 0 {vdd}
RPAR vddx vdd {rpar}
VG colprogn 0 0
{circuit}
.control
foreach rv {rlist}
  alter rfuse $rv
  op
  print v(a) v(c) i(vm)
end
.endc
.end
"""
CIRC = {
 "async": """Xp0 bl colprogn vdd vdd pfet_06v0 L=0.50u W=62u nf=2
Xp1 bl colprogn vdd vdd pfet_06v0 L=0.50u W=62u nf=2
VM bl a 0
rfuse a c 100
VC c 0 0""",
 "array": """Xp0 bl colprogn vdd vdd pfet_06v0 L=0.50u W=76.5u nf=2
VM bl a 0
rfuse a c 100
VSEL sel 0 {vdd}
Xn c sel 0 0 nfet_06v0 L=0.60u W=30.5u""",
}

def run(ngspice, pdk, macro, corner, vdd, temp, rpar):
    deck = DECK.format(macro=macro, corner=corner, vdd=vdd, temp=temp, pdk=pdk, rpar=rpar,
                       circuit=CIRC[macro].format(vdd=vdd), rlist=" ".join(map(str, RLIST)))
    with tempfile.NamedTemporaryFile("w", suffix=".sp", delete=False) as f:
        f.write(deck); name = f.name
    out = subprocess.run([ngspice, "-b", name], capture_output=True, text=True, timeout=300).stdout
    os.unlink(name)
    va = [float(x) for x in re.findall(r"^v\(a\) = (\S+)", out, re.M)]
    vc = [float(x) for x in re.findall(r"^v\(c\) = (\S+)", out, re.M)]
    im = [float(x) for x in re.findall(r"^i\(vm\) = (\S+)", out, re.M)]
    if len(im) != len(RLIST):
        sys.stderr.write(out[-3000:]); raise SystemExit("ngspice parse failure %s %s" % (macro, corner))
    return {"R": RLIST, "I": im, "Va": va, "Vc": vc}

def main():
    if platform.system() != "Linux":
        raise SystemExit("run on the Linux build box, not the Mac")
    ap = argparse.ArgumentParser()
    ap.add_argument("--pdk", default="/spice/pdk/ngspice")
    ap.add_argument("--ngspice", default="ngspice")
    ap.add_argument("--rpar", type=float, default=2.0)
    ap.add_argument("--out", default="drive.json")
    a = ap.parse_args()
    res = {}
    for macro in CIRC:
        for corner in ("typical", "ss", "ff"):
            for vdd in (4.5, 5.0, 5.5):
                for temp in (-40, 27, 125):
                    key = "%s/%s/%.1f/%d" % (macro, corner, vdd, temp)
                    res[key] = run(a.ngspice, a.pdk, macro, corner, vdd, temp, a.rpar)
                    r = res[key]; i60 = r["I"][RLIST.index(60)]; i200 = r["I"][RLIST.index(200)]
                    print("%-28s Ishort=%.2f mA  I(60)=%.2f mA  I(200)=%.2f mA  I(1k)=%.2f mA" % (
                        key, 1e3*r["I"][0], 1e3*i60, 1e3*i200, 1e3*r["I"][RLIST.index(1000)]), flush=True)
    json.dump({"rpar": a.rpar, "curves": res}, open(a.out, "w"))
main()
