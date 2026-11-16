#!/usr/bin/env python3
import lec as L, os
os.makedirs(L.OUT,exist_ok=True)
for top,w,n in [('qsag_add_split',128,2),('qsag_sum_csa',128,3),('qsag_sum_csa',128,4),('qsag_add_split',95,2),('qsag_add_split',80,2),('qsag_sum_csa',136,13)]:
    ys=L.yosys_smt2(f'{top}_{w}_{n}',top,[],f'-chparam W {w}'+(f' -chparam N {n}' if top.endswith('csa') else ''))
    if top.endswith('split'): spec=f"(bvadd {L.acc('a','s0')} {L.acc('b','s0')})"
    else:
        terms=[f"((_ extract {(i+1)*w-1} {i*w}) {L.acc('x','s0')})" for i in range(n)]
        spec=terms[0]
        for term in terms[1:]:spec=f'(bvadd {spec} {term})'
    body=ys+'(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n'+f"(assert (not (= {L.acc('y','s0')} {spec})))\n(check-sat)\n"
    L.record(f'{top}_{w}_{n}','universal adder/compressor equivalence','unsat',body,secs=40)
