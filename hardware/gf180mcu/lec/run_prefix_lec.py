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

# Full W=32 compositional proof of 5-row Goldilocks squarer qsag_gl64_sqrows:
W, GB = 32, 12
LW, AW = 64, 76
PHI, P = 1 << W, (1 << LW) - (1 << W) + 1


def sqrows_query(sfile, tag):
    t_sq = l.smt(sfile, "qsag_gl64_sqrows", tag)
    n = lambda x: f"(|{tag}_n {x}| s)"
    m = f"(concat {n('p01')} #b0)"
    m0 = f"((_ extract 31 0) {m})"
    m1 = f"((_ extract 63 32) {m})"
    m2 = f"((_ extract 64 64) {m})"
    l2 = f"((_ extract 31 0) {n('z2')})"
    h2 = f"((_ extract 63 32) {n('z2')})"
    er1 = l.zx(n("z0"), 64, AW)
    er2 = l.zx(f"(concat {m0} (bvnot {m1}))", 64, AW)
    er3 = l.zx(f"(concat {m1} (_ bv0 29) (ite (= {m2} #b1) #b011 #b100))", 64, AW)
    er4 = l.zx(f"(concat {l2} (bvnot {l2}))", 64, AW)
    er5 = l.zx(f"(concat #xfffffffc (bvnot {h2}))", 64, AW)
    # Check each row's exact integer value without chaining five 76-bit ripple-add miters
    return (t_sq + f"(declare-fun s () |{tag}_s|)\n"
            f"(assert (not (and (= {n('r1')} {er1}) (= {n('r2')} {er2}) (= {n('r3')} {er3}) "
            f"(= {n('r4')} {er4}) (= {n('r5')} {er5}))))")


l.check("qsag_gl64_sqrows W=32 RTL 5-row exact bitvectors", "unsat", sqrows_query(src, "sq64"))
l.check("qsag_gl64_sqrows W=32 integer congruence == z0 + m*phi + z2*(phi-1) mod p", "unsat", f"""
(declare-const z0 Int) (declare-const l2 Int) (declare-const h2 Int)
(declare-const m0 Int) (declare-const m1 Int) (declare-const m2 Int)
(define-fun phi () Int {PHI}) (define-fun p () Int {P})
(assert (and (<= 0 z0) (< z0 (* phi phi)) (<= 0 l2) (< l2 phi) (<= 0 h2) (< h2 phi)))
(assert (and (<= 0 m0) (< m0 phi) (<= 0 m1) (< m1 phi) (<= 0 m2) (< m2 2)))
(define-fun z2 () Int (+ l2 (* h2 phi)))
(define-fun m  () Int (+ m0 (* m1 phi) (* m2 phi phi)))
(define-fun r1 () Int z0)
(define-fun r2 () Int (+ (* m0 phi) (- phi 1 m1)))
(define-fun r3 () Int (+ (* m1 phi) (- 4 m2)))
(define-fun r4 () Int (+ (* l2 phi) (- phi 1 l2)))
(define-fun r5 () Int (+ (* (- phi 4) phi) (- phi 1 h2)))
(define-fun T  () Int (+ r1 r2 r3 r4 r5))
(define-fun V  () Int (+ z0 (* m phi) (* z2 phi phi)))
(assert (not (and (<= 0 T) (< T {1 << AW})
                  (= V (+ T (* (- (+ l2 (* h2 (+ phi 1)) m1 (* m2 (+ phi 1))) 1) p))))))
""")

text = open(src).read()
old_sq = "m2 ? 3'd3 : 3'd4"
assert text.count(old_sq) == 1
mut_sq = f"{l.B}/sq_mutant.sv"
open(mut_sq, "w").write(text.replace(old_sq, "m2 ? 3'd2 : 3'd3"))
l.check("qsag_gl64_sqrows negative control: 3-m2 offset bug", "sat", sqrows_query(mut_sq, "sq64m"))

print(f"{sum(l.results)}/{len(l.results)} prefix + squarer queries as expected")
sys.exit(0 if all(l.results) else 1)
