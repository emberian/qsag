#!/usr/bin/env python3
"""Prove HD=4, 0x000/0xFFF crowbar/laser rejection, loop-counter shadow guard, and
hardwired enclave secret non-exfiltration (`e_rd >= 44 => out_data == 0`) on `qsag_wire_engine`.
"""
import os
import re
import sys

os.environ["LEC_BUILD"] = "build/lec_control"
sys.argv = [sys.argv[0], "control", "90"]
import run_lec as l  # noqa: E402

path = "rtl/qsag_wire_engine.sv"
source = open(path).read()
codes = [int(x, 16) for x in re.findall(r"S_\w+\s*=\s*12'h([0-9a-f]+)", source)]
assert len(codes) == 125 and len(set(codes)) == 125, f"expected 125 unique states, got {len(codes)}/{len(set(codes))}"
assert 0x000 not in codes and 0xFFF not in codes, "0x000 and 0xFFF must never be legal states!"
assert min(c.bit_count() for c in codes) >= 4, "dist(0x000, valid) must be >= 4"
assert max(c.bit_count() for c in codes) <= 8, "dist(0xFFF, valid) must be >= 4"
assert min((a ^ b).bit_count() for a in codes for b in codes if a != b) == 4
print(f"{len(codes)} actual RTL state constants: pairwise HD >= 4, dist(0x000) >= 4, dist(0xFFF) >= 4", flush=True)

files = (
    "rtl/qsag_gl64_karatsuba_csa.sv rtl/qsag_p2_rc.sv "
    "rtl/qsag_sponge.sv rtl/qsag_keccak_serial.sv rtl/qsag_gf128_clmul.sv "
    "rtl/qsag_field_engine.sv rtl/dregg_captp_vat.sv "
)


def build_smt(src):
    return l.smt(files + src, "qsag_wire_engine", "ctrl")


rtl_main = build_smt(path)


def hd4_query(rtl, reg):
    n = lambda x: f"(|ctrl_n {x}| s)"
    q = "(declare-fun s () |ctrl_s|)\n(declare-const base (_ BitVec 12))\n(declare-const flips (_ BitVec 12))\n"
    q += "(assert (or " + " ".join(f"(= base {l.bv(c, 12)})" for c in codes) + "))\n"
    count = "(bvadd " + " ".join(f"((_ zero_extend 3) ((_ extract {i} {i}) flips))" for i in range(12)) + ")"
    q += f"(assert (and (bvuge {count} #x1) (bvule {count} #x3)))\n"
    q += f"(assert (= {n('steps_inv_q')} (bvnot {n('steps')})))\n"
    for r in ("st", "ret", "ret2", "ret3"):
        q += f"(assert (= {n(r)} " + ("(bvxor base flips)" if r == reg else l.bv(codes[0], 12)) + "))\n"
    q += f'(assert (not (and {n("control_bad")} (not {n("out_push")}) (not {n("launch")}) (not {n("in_pop")}))))\n'
    return rtl + q


def collapse_query(rtl, bad_val):
    n = lambda x: f"(|ctrl_s_dummy|)" if False else f"(|ctrl_n {x}| s)"
    q = "(declare-fun s () |ctrl_s|)\n"
    q += f"(assert (= {n('steps_inv_q')} (bvnot {n('steps')})))\n"
    q += "(assert (or " + " ".join(f"(= {n(r)} {l.bv(bad_val, 12)})" for r in ("st", "ret", "ret2", "ret3")) + "))\n"
    q += f'(assert (not (and {n("control_bad")} (not {n("out_push")}) (not {n("launch")}) (not {n("in_pop")}))))\n'
    return rtl + q


def counter_glitch_query(rtl):
    n = lambda x: f"(|ctrl_n {x}| s)"
    q = "(declare-fun s () |ctrl_s|)\n"
    for r in ("st", "ret", "ret2", "ret3"):
        q += f"(assert (= {n(r)} {l.bv(codes[0], 12)}))\n"
    q += f"(assert (not (= {n('steps_inv_q')} (bvnot {n('steps')}))))\n"
    q += f'(assert (not (and {n("control_bad")} (not {n("out_push")}) (not {n("launch")}) (not {n("in_pop")}))))\n'
    return rtl + q


def non_exfil_query(rtl):
    n = lambda x: f"(|ctrl_n {x}| s)"
    q = "(declare-fun s () |ctrl_s|)\n"
    q += f"(assert {n('emit_port')})\n"
    q += f"(assert (bvuge {n('e_rd')} (_ bv44 6)))\n"
    q += f"(assert (not (= {n('out_data')} (_ bv0 64))))\n"
    return rtl + q


for reg in ("st", "ret", "ret2", "ret3"):
    l.check(f"HD4: {reg} 1..3 flips block output, launch, input and detect", "unsat", hd4_query(rtl_main, reg))

l.check("Crowbar 12'h000 zeroing collapse trapped & fail-closed", "unsat", collapse_query(rtl_main, 0x000))
l.check("Laser 12'hFFF saturation collapse trapped & fail-closed", "unsat", collapse_query(rtl_main, 0xFFF))
l.check("Loop counter steps != ~steps_inv_q fault trapped & fail-closed", "unsat", counter_glitch_query(rtl_main))
l.check("Enclave non-exfiltration: emit_port & e_rd >= 44 => out_data == 0", "unsat", non_exfil_query(rtl_main))

mut = f"{l.B}/control_mutant.sv"
assert source.count("&& !(^c)") == 1
open(mut, "w").write(source.replace("&& !(^c)", ""))
l.check("HD4 negative control: remove overall parity check", "sat", hd4_query(build_smt(mut), "st"))

print(f"{sum(l.results)}/{len(l.results)} control queries as expected")
sys.exit(0 if all(l.results) else 1)
