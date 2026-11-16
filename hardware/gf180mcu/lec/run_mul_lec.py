#!/usr/bin/env python3
"""Full-width compositional proof of the radix-4 multiplier.
P: actual shifted rows match signed Booth digits times a (all 17 digits).
B: the signed digit expansion equals unsigned b, including its leading zero.
C: actual compressor tree returns the sum of those rows modulo 2^66.
Thus P+B+C and distributivity imply p=a*b. Prefix results are assumed only
at their instance output cutpoints, using actual input ports; run_prefix_lec
proves those instances' parametric RTL at N=35 and N=66 separately.
"""
import sys, os
os.environ['LEC_BUILD']='build/lec_mul'
sys.argv=[sys.argv[0], 'mul', '75']
import run_lec as l
N, PW, R = 33, 66, 17

def digits_query(src):
    t=l.smt(src, 'qsag_mul33', 'mul', passes='cutpoint w:u_neg.sum;')
    n=lambda x: f'(|mul_n {x}| s)'
    q='(declare-fun s () |mul_s|)\n'
    q+=f'(assert (= {n("u_neg.sum")} (bvadd {n("u_neg.a")} {n("u_neg.b")} (ite {n("u_neg.cin")} {l.bv(1,35)} {l.bv(0,35)}))))\n'
    terms=[]; rows=[]
    for j in range(R):
        digit=f'((_ extract {2*j+2} {2*j}) {n("bx")})'
        # radix-4 coefficient = low bit + middle bit - 2*high bit
        ext=lambda k: f'((_ zero_extend 65) ((_ extract {k} {k}) {digit}))'
        coeff=f'(bvsub (bvadd {ext(0)} {ext(1)}) (bvshl {ext(2)} {l.bv(1,PW)}))'
        shifted=f'(bvshl {coeff} {l.bv(2*j,PW)})'
        terms.append(shifted)
        actual=f'((_ extract {(j+1)*PW-1} {j*PW}) {n("rows")})'
        # Small signed digit multiply represented by ite avoids a nonlinear solver term.
        a=l.zx(n('a'),33,PW)
        pa=f'(bvshl {a} {l.bv(1,PW)})'
        val=f'(ite (= {coeff} {l.bv(0,PW)}) {l.bv(0,PW)} (ite (= {coeff} {l.bv(1,PW)}) {a} (ite (= {coeff} {l.bv(2,PW)}) {pa} (ite (= {coeff} {l.bv(-1,PW)}) (bvneg {a}) (bvneg {pa})))))'
        rows.append(f'(= {actual} (bvshl {val} {l.bv(2*j,PW)}))')
    bproof=f'(= (bvadd {" ".join(terms)}) {l.zx(n("b"),33,PW)})'
    return t+q+'(assert (not (and '+bproof+' '+' '.join(rows)+')))\n'

l.check('P+B: full 33x33 actual Booth rows and unsigned digit expansion','unsat',digits_query(l.GL))
# The final tree adder has a stable recursive hierarchy depth determined by ROWS.
rows=R; path=''
while rows>2:
    path+='g_reduce.u_next.'
    rows=2*(rows//3)+rows%3
path+='g_final.u_add'
t=l.smt(l.GL,'qsag_mul_csa_tree','tree',f'N={PW} ROWS={R}',passes=f'cutpoint w:{path}.sum;')
n=lambda x:f'(|tree_n {x}| s)'
q='(declare-fun s () |tree_s|)\n'
q+=f'(assert (= {n(path+".sum")} (bvadd {n(path+".a")} {n(path+".b")} (ite {n(path+".cin")} {l.bv(1,PW)} {l.bv(0,PW)}))))\n'
terms=[f'((_ extract {(j+1)*PW-1} {j*PW}) {n("rows")})' for j in range(R)]
q+=f'(assert (not (= {n("sum")} (bvadd {" ".join(terms)}))))\n'
l.check('C: full-width tree output == sum of its 17 input rows', 'unsat', t+q)
text=open(l.GL).read(); old="3'b011: digit = ap << 1;"; assert text.count(old)==1
mut=f'{l.B}/booth_mutant.sv';open(mut,'w').write(text.replace(old,"3'b011: digit = ap;"))
l.check('P+B negative control: +2 Booth digit becomes +1','sat',digits_query(mut))
print(f'{sum(l.results)}/{len(l.results)} multiplier queries as expected')
sys.exit(0 if all(l.results) else 1)
