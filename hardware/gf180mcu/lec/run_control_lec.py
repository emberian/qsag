#!/usr/bin/env python3
"""Prove HD=4 and fail-closed decode of the actual wire-engine state registers.
Checks 1..3 flips in each of st/ret/ret2/ret3, all 99 legal source states.
Does not claim resistance to faults in the detector itself or >=4 flips.
"""
import re
import sys
import os
os.environ["LEC_BUILD"] = "build/lec_control"
sys.argv = [sys.argv[0], 'control', '75']
import run_lec as l

path = 'rtl/qsag_wire_engine.sv'
source = open(path).read()
codes = [int(x,16) for x in re.findall(r"S_\w+\s*=\s*12'h([0-9a-f]+)", source)]
assert len(codes) == 99 and len(set(codes)) == 99
assert min((a^b).bit_count() for a in codes for b in codes if a!=b) == 4
print('99 actual RTL state constants: minimum Hamming distance 4', flush=True)
files = 'rtl/qsag_cells.sv rtl/qsag_gl64_karatsuba_csa.sv rtl/qsag_p2_rc.sv rtl/qsag_sponge.sv rtl/qsag_keccak_serial.sv rtl/qsag_gf128_clmul.sv rtl/qsag_field_engine.sv '

def query(src, reg):
    rtl = l.smt(files + src, 'qsag_wire_engine', 'ctrl')
    n = lambda x: f'(|ctrl_n {x}| s)'
    q = '(declare-fun s () |ctrl_s|)\n(declare-const base (_ BitVec 12))\n(declare-const flips (_ BitVec 12))\n'
    q += '(assert (or ' + ' '.join(f'(= base {l.bv(c,12)})' for c in codes) + '))\n'
    count = '(bvadd ' + ' '.join(f'((_ zero_extend 3) ((_ extract {i} {i}) flips))' for i in range(12)) + ')'
    q += f'(assert (and (bvuge {count} #x1) (bvule {count} #x3)))\n'
    for r in ('st','ret','ret2','ret3'):
        q += f'(assert (= {n(r)} ' + ('(bvxor base flips)' if r == reg else l.bv(codes[0],12)) + '))\n'
    q += f'(assert (not (and {n("control_bad")} (not {n("out_push")}) (not {n("launch")}) (not {n("in_pop")}))))\n'
    return rtl + q

for reg in ('st','ret','ret2','ret3'):
    l.check(f'HD4: {reg} 1..3 flips block output, launch, input and detect', 'unsat', query(path, reg))
mut = f'{l.B}/control_mutant.sv'
assert source.count('&& !(^c)') == 1
open(mut,'w').write(source.replace('&& !(^c)', ''))
l.check('HD4 negative control: remove overall parity check', 'sat', query(mut, 'st'))
print(f'{sum(l.results)}/{len(l.results)} control queries as expected')
sys.exit(0 if all(l.results) else 1)
