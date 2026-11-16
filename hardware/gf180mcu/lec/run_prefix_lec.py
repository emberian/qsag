#!/usr/bin/env python3
"""Prove the actual RTL Han-Carlson parallel-prefix network at every width used by the
datapath, plus unsigned squarer/multiplier helpers and 5-row Goldilocks squarer.
Run inside the remote container. Negative controls mutate carry/row logic and must give sat.
"""
import os
import sys

os.environ["LEC_BUILD"] = "build/lec_prefix"
sys.argv = [sys.argv[0], "prefix", "75"]
import run_lec as l  # noqa: E402

src = l.GL
for width in (1, 2, 3, 4, 32, 33, 34, 35, 64, 65, 66, 76):
    tag = f"prefix{width}"
    rtl = l.smt(src, "qsag_prefix_add", tag, f"N={width}")
    n = lambda x: f"(|{tag}_n {x}| s)"
    if width == 1:
        q = f"(declare-fun s () |{tag}_s|)\n(assert (not (= {n('sum')} (xor {n('a')} {n('b')} {n('cin')}))))"
    else:
        cin = f"(ite {n('cin')} {l.bv(1, width)} {l.bv(0, width)})"
        q = f"(declare-fun s () |{tag}_s|)\n(assert (not (= {n('sum')} (bvadd {n('a')} {n('b')} {cin}))))"
    l.check(f"Han-Carlson prefix N={width} == a+b+cin modulo 2^N", "unsat", rtl + q)
    if width == 64:
        text = open(src).read()
        old = "go[l][i] | (po[l][i] & go[l][i - STEP])"
        assert text.count(old) == 1
        path = f"{l.B}/prefix_mutant.sv"
        open(path, "w").write(text.replace(old, "go[l][i] ^ (po[l][i] | go[l][i - STEP])"))
        mutant = l.smt(path, "qsag_prefix_add", tag, f"N={width}")
        l.check("Han-Carlson negative control: corrupted generate merge", "sat", mutant + q)

for w in (4, 6, 8):
    tag = f"usq{w}"
    rtl = l.smt(src, "qsag_usq32", tag, f"W={w}")
    n = lambda x: f"(|{tag}_n {x}| s)"
    xv = l.zx(n("x"), w, 2 * w)
    q = f"(declare-fun s () |{tag}_s|)\n(assert (not (= {n('sq')} (bvmul {xv} {xv}))))"
    l.check(f"qsag_usq32 W={w} == x*x exact", "unsat", rtl + q)

    tag = f"umul{w}"
    rtl = l.smt(src, "qsag_umul32", tag, f"W={w}")
    n = lambda x: f"(|{tag}_n {x}| s)"
    av, bv_ = l.zx(n("a"), w, 2 * w), l.zx(n("b"), w, 2 * w)
    q = f"(declare-fun s () |{tag}_s|)\n(assert (not (= {n('p')} (bvmul {av} {bv_}))))"
    l.check(f"qsag_umul32 W={w} == a*b exact", "unsat", rtl + q)

# Full W=32 compositional proof of 5-row Goldilocks squarer qsag_gl64_sq_comb:
W, GB = 32, 12
LW, AW = 64, 76
P = (1 << LW) - (1 << W) + 1
t_sq = l.smt(src, "qsag_gl64_sq_comb", "sq64",
             passes="cutpoint w:z0 w:z2 w:p01 w:y;")
n = lambda x: f"(|sq64_n {x}| s)"
E = 132
q_sq = f"""(declare-fun s () |sq64_s|)
(assert (= {l.zx(n('z0'), 64, E)}  (bvmul {l.zx(n('x0'), 32, E)} {l.zx(n('x0'), 32, E)})))
(assert (= {l.zx(n('z2'), 64, E)}  (bvmul {l.zx(n('x1'), 32, E)} {l.zx(n('x1'), 32, E)})))
(assert (= {l.zx(n('p01'), 64, E)} (bvmul {l.zx(n('x0'), 32, E)} {l.zx(n('x1'), 32, E)})))
(define-fun x_full () (_ BitVec {E}) {l.zx(n('x'), 64, E)})
(define-fun sum5 () (_ BitVec {E}) (bvadd {l.zx(n('s'), AW, E)} {l.zx(n('c'), AW, E)}))
(assert (not (and (bvult sum5 {l.bv(1 << AW, E)})
                  (= (bvurem sum5 {l.bv(P, E)}) (bvurem (bvmul x_full x_full) {l.bv(P, E)})))))
"""
l.check("qsag_gl64_sq_comb W=32 full-width 5-row congruence == x^2 mod p", "unsat", t_sq + q_sq)

text = open(src).read()
old_sq = "m2 ? 3'd3 : 3'd4"
assert text.count(old_sq) == 1
mut_sq = f"{l.B}/sq_mutant.sv"
open(mut_sq, "w").write(text.replace(old_sq, "m2 ? 3'd2 : 3'd3"))
t_mut = l.smt(mut_sq, "qsag_gl64_sq_comb", "sq64m",
              passes="cutpoint w:z0 w:z2 w:p01 w:y;")
l.check("qsag_gl64_sq_comb negative control: 3-m2 offset bug", "sat",
        t_mut + q_sq.replace("|sq64_", "|sq64m_"))

print(f"{sum(l.results)}/{len(l.results)} prefix + squarer queries as expected")
sys.exit(0 if all(l.results) else 1)
