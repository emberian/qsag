#!/usr/bin/env python3
"""Z3 SMT-LIB2 equivalence proofs for pipelined qsag_gl64_karatsuba_csa and qsag_gf128_clmul.

Run remotely from the project root:  python3 lec/run_lec.py [gl64|gl64e|gf128|all] [timeout_s]
"""
import os
import subprocess
import sys

what = sys.argv[1] if len(sys.argv) > 1 else "all"
TO = int(sys.argv[2]) if len(sys.argv[2:]) else 120
B = os.environ.get("LEC_BUILD", "build/lec")
os.makedirs(B, exist_ok=True)
CELLS = "rtl/qsag_cells.sv "
GL = "rtl/qsag_gl64_karatsuba_csa.sv"
GF = "rtl/qsag_gf128_clmul.sv"
results = []


def sh(cmd):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if r.returncode:
        sys.exit(f"FAILED: {cmd}\n{r.stdout[-600:]}{r.stderr[-600:]}")
    return r.stdout


def mutant(src, name):
    dst = f"{B}/mut_{name}.sv"
    sh(f"python3 lec/mutate.py {src} {dst} {name}")
    return dst


def smt(srcs, top, tag, params="", passes="", use_cells=True):
    chp = " ".join(f"-chparam {k} {v}" for k, v in (p.split("=") for p in params.split()))
    out = f"{B}/{tag}.smt2"
    cells_arg = CELLS if use_cells else ""
    sh(f'yosys -q -p "read_verilog -sv {cells_arg}{srcs}; hierarchy -check -top {top} {chp}; proc; opt_clean; flatten; '
       f'{passes} opt -fast; async2sync; opt -fast; dffunmap; write_smt2 -wires {out}"')
    text = open(out).read()
    name = [l.split(None, 2)[2] for l in text.splitlines() if l.startswith("; yosys-smt2-topmod")][0]
    return text.replace(name, tag)


def check(name, expect, text):
    path = f"{B}/q_{len(results):02d}.smt2"
    open(path, "w").write(text + "\n(check-sat)\n")
    try:
        r = subprocess.run(["z3", "-smt2", f"-T:{TO}", path], capture_output=True, text=True, timeout=TO + 20)
        got = (r.stdout.strip().splitlines() or ["?"])[0]
    except subprocess.TimeoutExpired:
        got = "timeout"
    ok = got == expect
    results.append(ok)
    print(f"{name:<66} {got:<8} expected {expect:<6} {'OK' if ok else 'MISMATCH'}", flush=True)


def bv(v, w):
    return f"(_ bv{v % (1 << w)} {w})"


def zx(e, frm, to):
    return f"((_ zero_extend {to - frm}) {e})"


def gl64(lemmas=True):
    W, GB = 32, 12
    LW, AW = 2 * W, 2 * W + GB
    PHI, P = 1 << W, (1 << LW) - (1 << W) + 1

    def rows_query(src, tag):
        t = smt(src, "qsag_gl64_mrows", tag)
        n = lambda w: f"(|{tag}_n {w}| s)"
        plo = f"((_ extract {LW-1} 0) {n('p')})"
        p2  = f"((_ extract {LW+W-1} {LW}) {n('p')})"
        p3  = f"((_ extract {2*LW-1} {LW+W}) {n('p')})"
        PLO, P2, P3 = zx(plo, LW, AW), zx(p2, W, AW), zx(p3, W, AW)
        rs = f"(bvadd {n('r0')} {n('r1')} {n('r2')} {n('r3')})"
        exp = f"(bvadd {PLO} (bvsub (bvshl {P2} {bv(W, AW)}) {P2}) (bvneg {P3}) {bv(2 * P, AW)})"
        return t + f"(declare-fun s () |{tag}_s|)\n(assert (not (= {rs} {exp})))"

    def canon_query(src, tag):
        t = smt(src, "qsag_gl64_canon", tag,
                passes="setattr -set keep 1 w:t w:us w:uc w:u w:vs w:vc w:v_raw; cutpoint w:t w:u w:v_raw;")
        n = lambda w: f"(|{tag}_n {w}| s)"
        tt = f"(bvadd {n('x')} {n('y')})"
        q = f"((_ extract {AW-1} {LW}) {tt})"
        E = AW + 4
        lhs = lambda c: f"(bvadd {zx(n('r'), LW, E)} (bvmul (bvadd {zx(q, GB, E)} {bv(c, E)}) {bv(P, E)}))"
        lemmas_s = (
            f"(assert (= {n('t')} (bvadd {n('x')} {n('y')})))\n"
            f"(assert (= {n('u')} (bvadd {n('us')} {n('uc')} {bv(1, LW + 2)})))\n"
            f"(assert (= {n('v_raw')} (bvadd {n('vs')} {n('vc')})))\n"
        )
        return (t + f"(declare-fun s () |{tag}_s|)\n" + lemmas_s + f"(assert (not (and (bvult {n('r')} {bv(P, LW)})\n"
                f"  (or (= {lhs(0)} {zx(tt, AW, E)}) (= {lhs(1)} {zx(tt, AW, E)})))))")

    def e2e_query(src, tag, w):
        gb = 4
        lw = 2 * w
        steps = lw
        last_s = steps + 2
        stub = f"{B}/ereg_stub.sv"
        open(stub, "w").write(
            "module qsag_ereg #(parameter int W=8)(input wire clk,rst_n,en,input wire [W-1:0] d,output reg [W-1:0] q);\n"
            "  always @(posedge clk or negedge rst_n) if(!rst_n) q<='0; else if(en) q<=d;\nendmodule\n"
            "module qsag_ereg_nr #(parameter int W=8)(input wire clk,en,input wire [W-1:0] d,output reg [W-1:0] q);\n"
            "  always @(posedge clk) if(en) q<=d;\nendmodule\n"
        )
        t = smt(f"{stub} {src}", "qsag_gl64_karatsuba_csa", tag, f"W={w} GB={gb}", use_cells=False)
        p = (1 << lw) - (1 << w) + 1
        n = lambda wn, st: f"(|{tag}_n {wn}| {st})"
        o = t + "".join(f"(declare-fun s{i} () |{tag}_s|)\n" for i in range(last_s + 1))
        o += "".join(f"(assert (|{tag}_t| s{i} s{i+1}))\n" for i in range(last_s))
        o += "".join(f"(assert {n('rst_n', f's{i}')})\n" for i in range(last_s + 1))
        o += f"(assert (= {n('ms', 's0')} {bv(0, 7)}))\n(assert {n('mul_start', 's0')})\n"
        o += f"(assert (not {n('mul_asel', 's0')}))\n(assert (not {n('mul_bsel', 's0')}))\n"
        o += "".join(f"(assert (not {n(r, f's{i}')}))\n" for i in range(last_s) for r in ("ld_opa", "ld_opb"))
        a, b = n("opa", "s0"), f"((_ extract {lw-1} 0) {n('acc_c', 's0')})"
        slast = f"s{last_s}"
        o += (f"(assert (not (and {n('mul_last', slast)} (= {zx(n('cv', slast), lw, 2 * lw)} "
              f"(bvurem (bvmul {zx(a, lw, 2 * lw)} {zx(b, lw, 2 * lw)}) {bv(p, 2 * lw)})))))")
        return o

    if not lemmas:
        return e2e_query, tuple(mutant(GL, m) for m in ("kmul", "m2", "canon"))

    seq = smt(GL, "qsag_gl64_karatsuba_csa", "seq",
              passes="setattr -set keep 1 w:m_step_sum; cutpoint w:m_step_sum;")
    n = lambda w, st="s0": f"(|seq_n {w}| {st})"
    z = bv(0, AW)
    wiring = (
        f"(=> (= {n('ms')} {bv(65, 7)}) (and (= {n('u_mrows.p')} {n('p_sr')})"
        f" (= {n('u_csa.x')} {n('u_mrows.r0')}) (= {n('u_csa.y')} {z})"
        f" (= {n('u_csa.r1')} {n('u_mrows.r1')}) (= {n('u_csa.r2')} {n('u_mrows.r2')}) (= {n('u_csa.r3')} {n('u_mrows.r3')})))"
        f" (=> (= {n('ms')} {bv(66, 7)}) (and (= {n('u_canon.x')} {n('acc_s')}) (= {n('u_canon.y')} {n('acc_c')}) (= {n('cv')} {n('u_canon.r')})))"
    )
    check("W  W=32 unit wiring: mrows <- p_sr, csa <- mrows, cv <- reg canon", "unsat",
          seq + f"(declare-fun s0 () |seq_s|)\n(assert (not (and {wiring})))")

    n1 = lambda w: n(w, "s1")
    xfer = (f"(=> (and (= {n('ms')} {bv(0, 7)}) {n('mul_start')}) (= {n1('ms')} {bv(1, 7)}))"
            f" (=> (and (= {n('ms')} {bv(0, 7)}) (not {n('mul_start')})) (= {n1('ms')} {bv(0, 7)}))")
    for st_i in range(1, 66):
        xfer += f" (=> (= {n('ms')} {bv(st_i, 7)}) (= {n1('ms')} {bv(st_i + 1, 7)}))"
    xfer += (f" (=> (= {n('ms')} {bv(65, 7)}) (and (= {n1('acc_s')} {n('u_csa.s')}) (= {n1('acc_c')} {n('u_csa.c')})))"
             f" (=> (= {n('ms')} {bv(66, 7)}) (and {n('mul_last')} (= {n1('ms')} {bv(0, 7)})))")
    check("T  W=32 unit sequencing: ms 0..66, shared-adder p_sr & 1-clk fold->cv", "unsat",
          seq + f"(declare-fun s0 () |seq_s|) (declare-fun s1 () |seq_s|)\n(assert (|seq_t| s0 s1))\n"
          f"(assert {n('rst_n')})\n(assert {n1('rst_n')})\n(assert (not (and {xfer})))")

    check("R  W=32 128-bit Goldilocks fold rows: r0+r1+r2+r3 == plo + p2*(phi-1) - p3 + 2*p",
          "unsat", rows_query(GL, "rows"))
    t = smt(GL, "qsag_csa52", "csa")
    n = lambda w: f"(|csa_n {w}| s)"
    check("C  W=32 compressor: s + c == x + y + r1 + r2 + r3 (mod 2^76)", "unsat",
          t + f"(declare-fun s () |csa_s|)\n(assert (not (= (bvadd {n('s')} {n('c')}) (bvadd {n('x')} {n('y')} {n('r1')} {n('r2')} {n('r3')}))))")
    check("K  W=32 canonicalizer: r < p and x + y == r + k*p", "unsat", canon_query(GL, "canon"))
    rng = lambda v, hi: f"(<= 0 {v}) (< {v} {hi})"
    check("A  integers: 0 <= T < 2^76 and P == T + (p2 + p3*(phi+1) - 2) p", "unsat", f"""
(declare-const plo Int) (declare-const p2 Int) (declare-const p3 Int)
(define-fun phi () Int {PHI}) (define-fun p () Int {P})
(assert (and {rng('plo', '(* phi phi)')} {rng('p2', 'phi')} {rng('p3', 'phi')}))
(define-fun T () Int (+ plo (* p2 (- phi 1)) (- p3) (* 2 p)))
(define-fun Pval () Int (+ plo (* p2 phi phi) (* p3 phi phi phi)))
(assert (not (and (<= 0 T) (< T {1 << AW})
  (= Pval (+ T (* (+ p2 (* p3 (+ phi 1)) -2) p))))))""")
    mk, mm, mc = mutant(GL, "kmul"), mutant(GL, "m2"), mutant(GL, "canon")
    check("N  mutant K_FOLD + 1: Goldilocks fold rows", "sat", rows_query(mk, "nrows_k"))
    check("N  mutant ~p3 -> p3: Goldilocks fold rows", "sat", rows_query(mm, "nrows_m"))
    check("N  mutant canonicalizer without the >= p case", "sat", canon_query(mc, "ncanon"))
    return e2e_query, (mk, mm, mc)


def gl64e():
    e2e_query, (mk, mm, mc) = E2E
    for w in (4,):
        check(f"E  W={w} end to end, shared-adder real multiplier: cv == (a*b) mod p_W", "unsat", e2e_query(GL, f"e2e{w}", w))
    for nm, src in (("K_FOLD + 1", mk), ("~p3 -> p3", mm), ("canonicalizer", mc)):
        check(f"N  mutant {nm}: W=4 end to end", "sat", e2e_query(src, "ne2e", 4))


def gf128():
    D = 1
    steps = 128 // D

    def miter(src, top, tag, d):
        t = smt(f"{src} lec/lec_gf128.sv", top, tag, f"D={d}")
        return t + f"(declare-fun s () |{tag}_s|)\n(assert (not (|{tag}_n ok| s)))"

    for d in (1, 2, 4):
        check(f"G1 digit step D={d} == r*z^{d} + h*d (mod g)", "unsat", miter(GF, "lec_gf128_step", f"g1d{d}", d))
    u = smt(GF, "qsag_gf128_clmul", "unit", f"D={D}")
    st = smt(GF, "qsag_gf128_step", "step", f"D={D}")
    n = lambda w, s: f"(|unit_n {w}| {s})"
    step_d = "(ite (|step_n d| q) #b1 #b0)" if D == 1 else "(|step_n d| q)"
    q = u + st + "(declare-fun s0 () |unit_s|) (declare-fun s1 () |unit_s|) (declare-fun q () |step_s|)\n"
    q += f"(assert (|unit_t| s0 s1))\n(assert (and {n('rst_n', 's0')} {n('srst_n', 's0')} (not {n('clr', 's0')})))\n"
    q += f"(assert (and {n('rst_n', 's1')} {n('srst_n', 's1')}))\n"
    q += f"(assert (= (|step_n r| q) {n('r', 's0')}))\n(assert (= (|step_n h| q) {n('h', 's0')}))\n"
    q += f"(assert (= {step_d} ((_ extract 127 {128 - D}) {n('x', 's0')})))\n"
    q += f"""(assert (not (and
  (=> {n('run', 's0')} (and (= {n('r', 's1')} (|step_n o| q))
                            (= {n('x', 's1')} (concat ((_ extract {127 - D} 0) {n('x', 's0')}) {bv(0, D)}))))
  (=> (and (not {n('run', 's0')}) {n('start', 's0')})
      (and (= {n('x', 's1')} (bvxor {n('r', 's0')} {n('in', 's0')})) (= {n('r', 's1')} (_ bv0 128))
           {n('run', 's1')} (= {n('cnt', 's1')} #x00)))
  (=> {n('run', 's0')} (= {n('run', 's1')} (not (= {n('cnt', 's0')} {bv(steps - 1, 8)}))))
  (=> (and {n('run', 's0')} {n('run', 's1')}) (= {n('cnt', 's1')} (bvadd {n('cnt', 's0')} #x01))))))"""
    check(f"G3 sequential unit: load, {steps} x (step on top digit, shift)", "unsat", q)
    mp, md = mutant(GF, "poly"), mutant(GF, "digit")
    check("N  mutant reduction polynomial 0x86: digit step", "sat", miter(mp, "lec_gf128_step", "ng1p", 2))
    check("N  mutant digit bit order: digit step", "sat", miter(md, "lec_gf128_step", "ng1d", 2))


if __name__ == "__main__":
    print(sh("z3 --version").strip(), "|", sh("yosys -V").strip()[:10], f"| per-query limit {TO} s")
    if what in ("gl64", "all"):
        gl64()
    if what in ("gl64e", "all"):
        E2E = gl64(lemmas=False)
        gl64e()
    if what in ("gf128", "all"):
        gf128()
    print(f"{sum(results)}/{len(results)} queries as expected")
    sys.exit(0 if all(results) else 1)
