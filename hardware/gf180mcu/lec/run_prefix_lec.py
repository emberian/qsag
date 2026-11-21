#!/usr/bin/env python3
"""Prove the actual RTL Han-Carlson parallel-prefix network (`qsag_prefix_add`) at every width
instantiated across the datapath (including N=65, 66, 68, 76 for `qsag_mul_step4` & `qsag_gl64_canon`),
plus negative mutant control.
"""
import os
import sys

os.environ["LEC_BUILD"] = "build/lec_prefix"
sys.argv = [sys.argv[0], "prefix", "75"]
import run_lec as l  # noqa: E402

src = l.GL
for width in (1, 2, 3, 4, 11, 32, 33, 34, 35, 53, 64, 65, 66, 68, 76):
    tag = f"prefix{width}"
    rtl = l.smt(src, "qsag_prefix_add", tag, f"N={width}")
    n = lambda x: f"(|{tag}_n {x}| s)"
    if width == 1:
        q = f"(declare-fun s () |{tag}_s|)\n(assert (not (= {n('sum')} (xor {n('a')} {n('b')} {n('cin')}))))"
    else:
        cin = f"(ite {n('cin')} {l.bv(1, width)} {l.bv(0, width)})"
        q = f"(declare-fun s () |{tag}_s|)\n(assert (not (= {n('sum')} (bvadd {n('a')} {n('b')} {cin}))))"
    l.check(f"Han-Carlson prefix N={width} == a+b+cin modulo 2^N", "unsat", rtl + q)
    if width == 68:
        text = open(src).read()
        old = "assign g_o = g_hi | (p_hi & g_lo);"
        assert text.count(old) >= 1
        path = f"{l.B}/prefix_mutant.sv"
        open(path, "w").write(text.replace(old, "assign g_o = g_hi ^ (p_hi | g_lo);", 1))
        mutant = l.smt(path, "qsag_prefix_add", tag, f"N={width}")
        l.check("Han-Carlson negative control: corrupted generate merge", "sat", mutant + q)

print(f"{sum(l.results)}/{len(l.results)} prefix adder queries as expected")
sys.exit(0 if all(l.results) else 1)
