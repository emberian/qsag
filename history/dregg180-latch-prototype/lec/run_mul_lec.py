#!/usr/bin/env python3
"""Full-width compositional Z3 proof of the 64x64 -> 128 iterative multiplier (`qsag_mul_step1`):
  M1: 65-bit `qsag_mul_step1` (`qsag_prefix_add(65)`) == `acc_hi + (bit_in ? a : 0)` for ALL
      64-bit unsigned `acc_hi, a` and 1-bit `bit_in`.
  M2: QF_LIA exact integer & non-overflow proof of the 64-step shift-accumulate recurrence:
      every intermediate `sum_k < 2^65` (zero modular wrap) and `p_64 == a * b` for ALL 64-bit `a, b`!
  N:  negative mutant control (`bit_in ? a : '0` -> `bit_in ? {a[LW-2:0], 1'b0} : '0`) produces `sat`.
"""
import os
import sys

os.environ["LEC_BUILD"] = "build/lec_mul"
sys.argv = [sys.argv[0], "mul", "75"]
import run_lec as l  # noqa: E402

LW, SW = 64, 65


def step_query(src):
    t = l.smt(src, "qsag_mul_step1", "mstep",
              passes="setattr -set keep 1 w:addend w:sum; cutpoint w:sum;")
    n = lambda x: f"(|mstep_n {x}| s)"
    acc_zx = l.zx(n("acc_hi"), LW, SW)
    add_zx = l.zx(n("addend"), LW, SW)
    a_zx = l.zx(n("a"), LW, SW)
    q = "(declare-fun s () |mstep_s|)\n"
    q += f"(assert (= {n('sum')} (bvadd {acc_zx} {add_zx})))\n"
    q += f"(assert (not (= {n('sum')} (bvadd {acc_zx} (ite {n('bit_in')} {a_zx} {l.bv(0, SW)})))))\n"
    return t + q


l.check("M1: 64x1 shift-add step (prefix_add N=65) == acc_hi + bit_in * a", "unsat", step_query(l.GL))

q64 = "(set-logic QF_LIA)\n(declare-const a Int)\n"
q64 += f"(assert (and (<= 0 a) (< a {1 << 64})))\n"
for j in range(64):
    q64 += f"(declare-const b_{j} Bool)\n"
q64 += "(define-fun hi0 () Int 0)\n(define-fun lo0 () Int 0)\n"
ab_terms = []
ovf_checks = []
for k in range(64):
    prod_k = f"(ite b_{k} a 0)"
    ab_terms.append(f"(* {1 << k} {prod_k})")
    q64 += f"(declare-const q{k} Int)\n(declare-const r{k} Int)\n"
    q64 += f"(define-fun sum{k} () Int (+ hi{k} {prod_k}))\n"
    q64 += f"(assert (and (<= 0 r{k}) (< r{k} 2) (= sum{k} (+ (* 2 q{k}) r{k}))))\n"
    q64 += f"(define-fun hi{k+1} () Int q{k})\n"
    q64 += f"(define-fun lo{k+1} () Int (+ lo{k} (* {1 << k} r{k})))\n"
    ovf_checks.append(f"(< sum{k} {1 << 65})")
q64 += f"(define-fun p64 () Int (+ (* {1 << 64} hi64) lo64))\n"
q64 += f"(define-fun ab_exact () Int (+ {' '.join(ab_terms)}))\n"
q64 += f"(assert (not (and {' '.join(ovf_checks)} (= p64 ab_exact))))\n"
l.check("M2: 64-step 64x64->128 shift-add recurrence < 2^65 & == exact a * b", "unsat", q64)

text = open(l.GL).read()
old = "wire [LW-1:0] addend = bit_in ? a : '0;"
assert text.count(old) == 1
mut = f"{l.B}/mul_step_mutant.sv"
open(mut, "w").write(text.replace(old, "wire [LW-1:0] addend = bit_in ? {a[LW-2:0], 1'b0} : '0;"))
l.check("M1 negative control: shifted addend bug", "sat", step_query(mut))

print(f"{sum(l.results)}/{len(l.results)} multiplier queries as expected")
sys.exit(0 if all(l.results) else 1)
