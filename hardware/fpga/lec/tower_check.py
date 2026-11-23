#!/usr/bin/env python3
"""Z3 miters for both linear maps and the actual tower-wrapper Lean KATs.
The Artin-Schreier equations, rank, and bilinear multiplicativity are checked
independently by exact GF(2) arithmetic on every pair of basis vectors.
"""
import sys, os, json
sys.path.insert(0,os.path.join(os.path.dirname(__file__),'../scripts'))
import gen_tower_map as G
import lec as L
from pathlib import Path
os.makedirs(L.OUT,exist_ok=True)
rows,inv,cols,ic,gs=G.matrices()
rtl=Path(L.ROOT)/'rtl'
def parity(x,mask):
    bits=[f'((_ extract {i} {i}) {x})' for i in range(128) if mask>>i&1]
    v='#b0'
    for b in bits: v=f'(bvxor {v} {b})'
    return v
for direction,rs in enumerate([rows,inv]):
    ys=L.yosys_smt2(f'tower_map_{direction}', 'qsag_gf128_tower_map',[str(rtl/'qsag_gf128_tower_map.sv')],f'-chparam INVERSE {direction}')
    x=L.acc('x','s0');y=L.acc('y','s0')
    # Each single-output obligation is universal in all 128 input bits.
    base=ys+'(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n'
    assertions=[f'(= ((_ extract {i} {i}) {y}) {parity(x,m)})' for i,m in enumerate(rs)]
    assert L.record(f'tower_map_{direction}', 'all 2^128 inputs: RTL map equals the exact qsag-asm basis matrix', 'unsat',base+'(assert (not (and '+' '.join(assertions)+')))\n(check-sat)\n')
# All basis-pair products, using the defining tower recurrence rather than a matrix identity.
def tmul(k,a,b):
    if k==0:return a&b
    h=1<<(k-1);mask=(1<<h)-1
    a0,a1=a&mask,a>>h;b0,b1=b&mask,b>>h
    p=tmul(k-1,a0,b0);q=tmul(k-1,a1,b1)
    cross=tmul(k-1,a0^a1,b0^b1)^p^q
    g=1 if k==1 else 1<<(h//2)
    return (p^q)|((cross^tmul(k-1,g,q))<<h)
for i in range(128):
    for j in range(128):
        assert G.apply(cols,tmul(7,1<<i,1<<j))==G.mul(cols[i],cols[j])
print('[PASS] 16384 basis products: tower recurrence -> polynomial multiplication (exact bilinear certificate)',flush=True)
files=[str(rtl/n) for n in ['qsag_clmul_kara.sv','qsag_gf128_reduce.sv','qsag_gf128_clmul.sv','qsag_gf128_tower_map.sv','qsag_gf128_tower_mul.sv']]
ys=L.yosys_smt2('tower_kat','qsag_gf128_tower_mul',files)
fixture=json.load(open(os.environ.get('QSAG_FIXTURE', Path(L.ROOT)/'tb/fixtures/lean_oracle.json')))
for i,k in enumerate(fixture['tower128']):
    vals=[int.from_bytes(bytes.fromhex(k[n]),'little') for n in ['a_le_hex','b_le_hex','mul_le_hex','inv_a_le_hex']]
    for name,b,want in [('mul',vals[1],vals[2]),('inv',vals[3],int(vals[0]!=0))]:
        body=ys+L.unroll(3)+f"(assert (= {L.acc('a','s0')} {L.bv(vals[0],128)}))\n(assert (= {L.acc('b','s0')} {L.bv(b,128)}))\n(assert (not (= {L.acc('r','s3')} {L.bv(want,128)})))\n(check-sat)\n"
        assert L.record(f'tower_kat_{i}_{name}','actual 3-cycle wrapper vs Lean tower128 fixture','unsat',body)
Path(L.OUT,'results_tower.txt').write_text('\n'.join('\t'.join(map(str,r)) for r in L.results)+'\n')
