#!/usr/bin/env python3
"""Prove the actual RTL prefix network at each width used by the reducer.
Run inside the remote container. Negative control mutates the carry merge.
"""
import sys
import os
os.environ["LEC_BUILD"] = "build/lec_prefix"
sys.argv = [sys.argv[0], 'prefix', '75']
import run_lec as l

src = l.GL
for width in (1, 32, 35, 64, 65, 66, 76):
    tag = f'prefix{width}'
    rtl = l.smt(src, 'qsag_prefix_add', tag, f'N={width}')
    n = lambda x: f'(|{tag}_n {x}| s)'
    cin = f'(ite {n("cin")} {l.bv(1, width)} {l.bv(0, width)})'
    q = f'(declare-fun s () |{tag}_s|)\n(assert (not (= {n("sum")} (bvadd {n("a")} {n("b")} {cin}))))'
    l.check(f'prefix N={width} == a+b+cin modulo 2^N', 'unsat', rtl + q)
    if width == 64:
        text = open(src).read()
        old = 'gg[l][i] | (pp[l][i] & gg[l][i-(1 << l)])'
        assert text.count(old) == 1
        path = f'{l.B}/prefix_mutant.sv'
        open(path, 'w').write(text.replace(old, 'gg[l][i] ^ (pp[l][i] | gg[l][i-(1 << l)])'))
        mutant = l.smt(path, 'qsag_prefix_add', tag, f'N={width}')
        l.check('prefix negative control: corrupted generate merge', 'sat', mutant + q)
print(f'{sum(l.results)}/{len(l.results)} prefix queries as expected')
sys.exit(0 if all(l.results) else 1)
