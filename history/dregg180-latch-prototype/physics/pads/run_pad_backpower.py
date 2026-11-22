#!/usr/bin/env python3
"""Back-powering through a pad of an unpowered chip, all four pad cells, process and temperature corners.

Two measurements per cell/corner/temperature (ngspice DC operating points, foundry IO netlists):
  fwd : chip rails held at 0 V; pad forced to +Vf and -Vf.  Gives the current of the upper path (pad into
        DVDD/VDD) and of the lower path (DVSS into pad) against forward voltage.
  flt : chip rails undriven, tied together, loaded by RLOAD to ground; pad driven from VSRC through RSER.
        Gives the rail voltage a host pin can raise.
Corners: MOS typical/ss/ff with the matching diode_* and res_* sections; -40, 27, 125 C.
Assumed: control inputs of the cell at 0 V; DVDD and VDD shorted (as in this chip's pad ring).
Linux only; run inside container dregg180-h4-spice in a directory holding moscap_with_esr.inc and the
lane's .spiceinit (ngbehavior=hsa).   python3 run_pad_backpower.py --out pad_backpower_corners.json
"""
import argparse, json, re, subprocess, platform, sys
CELLS = {  # instance line with PAD -> padx, rails -> rail
 "bi_24t":  "XPAD 0 0 rail 0 0 0 padx 0 0 0 rail 0 y gf180mcu_fd_io__bi_24t",
 "in_c":    "XPAD rail 0 padx 0 0 rail 0 y gf180mcu_fd_io__in_c",
 "in_s":    "XPAD rail 0 padx 0 0 rail 0 y gf180mcu_fd_io__in_s",
 "asig_5p0": "XPAD padx rail 0 rail 0 gf180mcu_fd_io__asig_5p0",
}
SUF = {"typical": "typical", "ss": "ss", "ff": "ff"}
VF = [0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9, 1.0, 1.2]
RL = ["10meg", "1meg", "100k", "10k", "1k"]; RS = ["1", "330", "1k", "2.2k", "10k"]; VS = [3.3, 5.0, 5.5]
HEAD = """* pad back-power {cell} {corner} {temp}
.include "/spice/pdk/ngspice/design.ngspice"
.lib "/spice/pdk/ngspice/sm141064.ngspice" {corner}
.lib "/spice/pdk/ngspice/sm141064.ngspice" diode_{suf}
.lib "/spice/pdk/ngspice/sm141064.ngspice" res_{suf}
.param cap_nmos_06v0_corner=1
.temp {temp}
.include "moscap_with_esr.inc"
.include "/spice/pdk/gf180mcu_fd_io.spice"
.options klu gmin=1e-13
VSRC src 0 0
RSER src pad 1
VMP pad padx 0
{inst}
RY y 0 100meg
"""
def run(deck, name):
    open(name + ".sp", "w").write(deck)
    return subprocess.run(["timeout", "300", "ngspice", "-b", name + ".sp"], capture_output=True, text=True).stdout
def val(out, key):
    return [float(x) for x in re.findall(r"^%s = (\S+)" % re.escape(key), out, re.M)]
def main():
    if platform.system() != "Linux": raise SystemExit("run on the Linux build box, not the Mac")
    ap = argparse.ArgumentParser(); ap.add_argument("--out", default="pad_backpower_corners.json"); a = ap.parse_args()
    res = {}
    for cell, inst in CELLS.items():
        for corner in ("typical", "ss", "ff"):
            for temp in (-40, 27, 125):
                key = "%s/%s/%d" % (cell, corner, temp)
                head = HEAD.format(cell=cell, corner=corner, suf=SUF[corner], temp=temp, inst=inst if cell != "asig_5p0" else inst + "\nRYY y 0 100meg")
                # forward characteristics, rails at 0 V through an ammeter
                d = head + "VRAIL rail 0 0\n.control\nforeach v %s\n alter vsrc dc = $v\n op\n print i(vmp) i(vrail)\n alter vsrc dc = -$v\n op\n print i(vmp)\nend\n.endc\n.end\n" % " ".join(map(str, VF))
                o = run(d, "fwd"); ip = val(o, "i(vmp)"); ir = val(o, "i(vrail)")
                # floating rail
                d = head + "RLOAD rail 0 10k\n.control\nforeach rl %s\n foreach rs %s\n  foreach v %s\n   alter rload $rl\n   alter rser $rs\n   alter vsrc dc = $v\n   op\n   print v(rail) i(vmp)\n  end\n end\nend\n.endc\n.end\n" % (
                    " ".join(RL), " ".join(RS), " ".join(map(str, VS)))
                o2 = run(d, "flt"); vr = val(o2, "v(rail)"); i2 = val(o2, "i(vmp)")
                ok = len(ip) == 2 * len(VF) and len(vr) == len(RL) * len(RS) * len(VS)
                res[key] = dict(ok=ok, vf=VF, i_up=ip[0::2], i_rail=[-x for x in ir], i_down=[-x for x in ip[1::2]] if ok else [],
                                rl=RL, rs=RS, vs=VS, v_rail=vr, i_pad=i2)
                if ok:
                    k = lambda rl, rs, v: (RL.index(rl) * len(RS) + RS.index(rs)) * len(VS) + VS.index(v)
                    print("%-22s Iup(0.5/0.7/1.0V)=%.2e/%.2e/%.2e A  Idown(0.7V)=%.2e | rail @5.5V: 10meg,1ohm %.2f V; 10k,2.2k %.2f V; 1k,2.2k %.2f V" % (
                        key, ip[2 * 3], ip[2 * 5], ip[2 * 8], -ip[2 * 5 + 1], vr[k("10meg", "1", 5.5)], vr[k("10k", "2.2k", 5.5)], vr[k("1k", "2.2k", 5.5)]), flush=True)
                else:
                    print(key, "FAILED", len(ip), len(vr), flush=True); sys.stderr.write(o[-1500:] + o2[-1500:])
    json.dump(res, open(a.out, "w"))
main()
