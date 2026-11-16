#!/usr/bin/env python3
"""Z3 SMT-LIB2 equivalence proofs for qsag_gl64_karatsuba_csa and qsag_gf128_clmul.

Run remotely from the project root:  python3 lec/run_lec.py [gl64|gl64e|gf128|all] [timeout_s]

Every query is the negation of a claim about a transition system or circuit that Yosys wrote
from the RTL (`write_smt2`), so `unsat` proves the claim for all inputs. Each claim is also run
against mutated RTL (lec/mutate.py), where the solver must answer `sat`.

Goldilocks unit, W = 32 (the chip), p = 2^64 - 2^32 + 1, phi = 2^32
  W   wiring of the sequential unit in multiply phase k = 1, 2, 3: the row generator sees
      (preg, k), the compressor sees the rows and the accumulator (zero in phase 1), the
      canonicalizer sees the compressor outputs and drives cv
  T   sequencing: phases 0 -> 1 -> 2 -> 3 -> 0; preg takes the multiplier output in phases
      0, 1, 2 (z0, z2, zm); the accumulator takes the compressor outputs in phases 1, 2
  R1..R3  row generator, as exact integers (z = lo + hi*phi + m2*phi^2):
      phase 1 (z0): r1 + r2 + r3 = lo + hi - lo*phi + 2*phi^2 - 2*phi
      phase 2 (z2): r1 + r2 + r3 = 2p - phi - z2
      phase 3 (zm): r1 + r2 + r3 = (lo + hi)*phi - hi - m2 + phi + 2
  C   compressor: s + c = x + y + r1 + r2 + r3 (mod 2^76)
  K   canonicalizer: r < p and x + y = r + k*p with k = q or q + 1, q = (x + y) >> 64
  A   integers: with T the sum of the seven rows, 0 <= T < 2^76 and
      z0 + (zm - z0 - z2)*phi + z2*phi^2 = (T - k*p) + (k + z2 - h0 - 4 + m1 + m2*(phi + 1))*p
  I   integers: for a = a1*phi + a0, b = b1*phi + b0 the three products satisfy the Karatsuba
      identity z0 + (zm - z0 - z2)*phi + z2*phi^2 = a*b and fit the multiplier
  W + T + R + C + K + A + I: the unit returns the canonical (a * b) mod p for all 64-bit a, b.
  E   end to end with the real multiplier at reduced width (W = 4, p_W = 241; W = 6 with
      LEC_W6=1, which did not finish within 75 s on the build host):
      the same parametric RTL returns (a * b) mod p_W for all a, b

GF(2^128) unit, g(z) = z^128 + z^7 + z^2 + z + 1, digit D = 2 as built
  G1  one digit step = r*z^D + h*d (mod g) against the bit-serial specification (D = 2, 4)
  G3  the sequential unit applies exactly that step to the top digit, shifts, and runs 128/D
      steps from r = 0 and x = acc ^ in
  G1 + G3 give the product by induction over the digits (Horner): after k steps
  r = sum_{i<k} d_i z^{D(k-1-i)} h (mod g), so after 128/D steps acc = (acc_0 ^ in) * h (mod g).
  (A direct miter of all chained steps against the specification is not run: Yosys 0.69
  aborts on it with an internal assertion in rtlil_bufnorm.)
"""
import os
import subprocess
import sys

what = sys.argv[1] if len(sys.argv) > 1 else "all"
TO = int(sys.argv[2]) if len(sys.argv) > 2 else 120
B = "build/lec"
os.makedirs(B, exist_ok=True)
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


def smt(srcs, top, tag, params="", passes=""):
    """Yosys -> SMT-LIB2 for module `top`, renamed to `tag`; returns the text."""
    chp = " ".join(f"-chparam {k} {v}" for k, v in (p.split("=") for p in params.split()))
    out = f"{B}/{tag}.smt2"
    sh(f'yosys -q -p "read_verilog -sv {srcs}; hierarchy -top {top} {chp}; proc; flatten; '
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


# ------------------------------------------------------------------------------------ Goldilocks
def gl64(lemmas=True):
    W, GB = 32, 12
    LW, AW = 2 * W, 2 * W + GB
    PHI, P = 1 << W, (1 << LW) - (1 << W) + 1

    def rows_query(src, tag, ph):
        t = smt(src, "qsag_gl64_mrows", tag)
        n = lambda w: f"(|{tag}_n {w}| s)"
        lo, hi, m2 = f"((_ extract {W-1} 0) {n('p')})", f"((_ extract {LW-1} {W}) {n('p')})", f"((_ extract {LW+1} {LW}) {n('p')})"
        L, H, M2 = zx(lo, W, AW), zx(hi, W, AW), zx(m2, 2, AW)
        rs = f"(bvadd {n('r1')} {n('r2')} {n('r3')})"
        if ph == 1:
            exp = f"(bvadd {L} {H} (bvneg (bvshl {L} {bv(W, AW)})) {bv(2 * PHI * PHI - 2 * PHI, AW)})"
            pre = f"(= {m2} #b00)"
        elif ph == 2:
            exp = f"(bvsub {bv(2 * P - PHI, AW)} (bvadd {L} (bvshl {H} {bv(W, AW)})))"
            pre = f"(= {m2} #b00)"
        else:
            exp = f"(bvadd (bvshl (bvadd {L} {H}) {bv(W, AW)}) (bvneg {H}) (bvneg {M2}) {bv(PHI + 2, AW)})"
            pre = "true"
        return (t + f"(declare-fun s () |{tag}_s|)\n(assert (= {n('ph')} {bv(ph, 2)}))\n(assert {pre})\n"
                f"(assert (not (= {rs} {exp})))")

    def canon_query(src, tag):
        # Compositional proof: each prefix instance is proved separately by
        # run_prefix_lec.py at its exact width. Cut only those result nets and
        # constrain them to addition of the *actual instance input nets*.
        t = smt(src, "qsag_gl64_canon", tag,
                passes="cutpoint w:u_t.sum w:u_fold.sum w:u_v.sum;")
        n = lambda w: f"(|{tag}_n {w}| s)"
        tt = f"(bvadd {n('x')} {n('y')})"
        q = f"((_ extract {AW-1} {LW}) {tt})"
        E = AW + 4
        lhs = lambda c: f"(bvadd {zx(n('r'), LW, E)} (bvmul (bvadd {zx(q, GB, E)} {bv(c, E)}) {bv(P, E)}))"
        lemmas = ""
        for inst, width in (("u_t", AW), ("u_fold", LW+2), ("u_v", LW+1)):
            cin = f"(ite {n(inst+'.cin')} {bv(1,width)} {bv(0,width)})"
            lemmas += f"(assert (= {n(inst+'.sum')} (bvadd {n(inst+'.a')} {n(inst+'.b')} {cin})))\n"
        return (t + f"(declare-fun s () |{tag}_s|)\n" + lemmas + f"(assert (not (and (bvult {n('r')} {bv(P, LW)})\n"
                f"  (or (= {lhs(0)} {zx(tt, AW, E)}) (= {lhs(1)} {zx(tt, AW, E)})))))")

    def e2e_query(src, tag, w):
        gb = 3
        t = smt(src, "qsag_gl64_karatsuba_csa", tag, f"W={w} GB={gb}")
        lw, p = 2 * w, (1 << (2 * w)) - (1 << w) + 1
        n = lambda wn, st: f"(|{tag}_n {wn}| {st})"
        o = t + "".join(f"(declare-fun s{i} () |{tag}_s|)\n" for i in range(4))
        o += "".join(f"(assert (|{tag}_t| s{i} s{i+1}))\n" for i in range(3))
        o += "".join(f"(assert {n('rst_n', f's{i}')})\n" for i in range(4))
        o += f"(assert (= {n('mph', 's0')} #b00))\n(assert {n('mul_start', 's0')})\n"
        o += f"(assert (not {n('mul_asel', 's0')}))\n(assert (not {n('mul_bsel', 's0')}))\n"
        # the sequencer never loads an operand register during a multiply
        o += "".join(f"(assert (not {n(r, f's{i}')}))\n" for i in range(3) for r in ("ld_opa", "ld_opb"))
        a, b = n("opa", "s0"), n("opb", "s0")
        o += (f"(assert (not (= {zx(n('cv', 's3'), lw, 2 * lw)} "
              f"(bvurem (bvmul {zx(a, lw, 2 * lw)} {zx(b, lw, 2 * lw)}) {bv(p, 2 * lw)}))))")
        return o

    if not lemmas:
        return e2e_query, tuple(mutant(GL, m) for m in ("kmul", "m2", "canon"))

    # W, T: wiring and sequencing of the sequential unit around its three proven blocks
    seq = smt(GL, "qsag_gl64_karatsuba_csa", "seq", passes="cutpoint w:m_p;")
    n = lambda w, st="s0": f"(|seq_n {w}| {st})"
    z = bv(0, AW)
    wiring = " ".join(
        f"(=> (= {n('mph')} {bv(k, 2)}) (and (= {n('u_mrows.p')} {n('preg')}) (= {n('u_mrows.ph')} {bv(k, 2)})"
        f" (= {n('u_csa.x')} {z if k == 1 else n('acc_s')}) (= {n('u_csa.y')} {z if k == 1 else n('acc_c')})))" for k in (1, 2, 3))
    wiring += "".join(f" (=> (not (= {n('mph')} #b00)) (= {n('u_csa.' + r)} {n('u_mrows.' + r)}))" for r in ("r1", "r2", "r3"))
    wiring += f" (= {n('u_canon.x')} {n('u_csa.s')}) (= {n('u_canon.y')} {n('u_csa.c')}) (= {n('cv')} {n('u_canon.r')})"
    check("W  W=32 unit wiring: rows <- preg, compressor <- acc, cv <- canon", "unsat",
          seq + f"(declare-fun s0 () |seq_s|)\n(assert (not (and {wiring})))")
    n1 = lambda w: n(w, "s1")
    xfer = (f"(=> (and (= {n('mph')} #b00) {n('mul_start')}) (and (= {n1('mph')} #b01) (= {n1('preg')} {n('m_p')})))"
            f" (=> (and (= {n('mph')} #b00) (not {n('mul_start')})) (= {n1('mph')} #b00))")
    for k in (1, 2):
        xfer += (f" (=> (= {n('mph')} {bv(k, 2)}) (and (= {n1('mph')} {bv(k + 1, 2)}) (= {n1('preg')} {n('m_p')})"
                 f" (= {n1('acc_s')} {n('u_csa.s')}) (= {n1('acc_c')} {n('u_csa.c')})))")
    xfer += f" (=> (= {n('mph')} #b11) (= {n1('mph')} #b00))"
    check("T  W=32 unit sequencing: phases 0..3, preg and accumulator updates", "unsat",
          seq + f"(declare-fun s0 () |seq_s|) (declare-fun s1 () |seq_s|)\n(assert (|seq_t| s0 s1))\n"
          f"(assert {n('rst_n')})\n(assert {n1('rst_n')})\n(assert (not (and {xfer})))")
    for ph in (1, 2, 3):
        check(f"R{ph} W=32 row generator phase {ph}: exact row sum", "unsat", rows_query(GL, f"rows{ph}", ph))
    t = smt(GL, "qsag_csa52", "csa")
    n = lambda w: f"(|csa_n {w}| s)"
    check("C  W=32 compressor: s + c == x + y + r1 + r2 + r3 (mod 2^76)", "unsat",
          t + f"(declare-fun s () |csa_s|)\n(assert (not (= (bvadd {n('s')} {n('c')}) (bvadd {n('x')} {n('y')} {n('r1')} {n('r2')} {n('r3')}))))")
    check("K  W=32 canonicalizer: r < p and x + y == r + k*p", "unsat", canon_query(GL, "canon"))
    # A, I: integer algebra
    rng = lambda v, hi: f"(<= 0 {v}) (< {v} {hi})"
    check("A  integers: 0 <= T < 2^76 and V == (T - k p) + (...) p", "unsat", f"""
(declare-const l0 Int) (declare-const h0 Int) (declare-const z2 Int) (declare-const m0 Int)
(declare-const m1 Int) (declare-const m2 Int) (declare-const k Int)
(define-fun phi () Int {PHI}) (define-fun p () Int {P})
(assert (and {rng('l0', 'phi')} {rng('h0', 'phi')} {rng('z2', '(* phi phi)')} {rng('m0', 'phi')} {rng('m1', 'phi')} {rng('m2', 4)}))
(define-fun z0 () Int (+ l0 (* h0 phi)))
(define-fun zm () Int (+ m0 (* m1 phi) (* m2 phi phi)))
(define-fun T () Int (+ (+ l0 h0 (* -1 l0 phi) (* 2 phi phi) (* -2 phi)) (- (- (* 2 p) phi) z2)
                        (+ (* (+ m0 m1) phi) (- m1) (- m2) phi 2)))
(define-fun V () Int (+ z0 (* (- zm z0 z2) phi) (* z2 phi phi)))
(assert (not (and (<= 0 T) (< T {1 << AW})
  (= V (+ (- T (* k p)) (* (+ k z2 (- h0) -4 m1 (* m2 (+ phi 1))) p))))))""")
    check("I  integers: Karatsuba identity and product ranges", "unsat", f"""
(declare-const a0 Int) (declare-const a1 Int) (declare-const b0 Int) (declare-const b1 Int)
(define-fun phi () Int {PHI})
(assert (and {rng('a0', 'phi')} {rng('a1', 'phi')} {rng('b0', 'phi')} {rng('b1', 'phi')}))
(define-fun z0 () Int (* a0 b0)) (define-fun z2 () Int (* a1 b1)) (define-fun zm () Int (* (+ a0 a1) (+ b0 b1)))
(assert (not (and (= (+ z0 (* (- zm z0 z2) phi) (* z2 phi phi)) (* (+ (* a1 phi) a0) (+ (* b1 phi) b0)))
  (< z0 (* phi phi)) (< z2 (* phi phi)) (< zm (* 4 phi phi)) (<= 0 z0) (<= 0 z2) (<= 0 zm))))""")
    # mutants of the lemmas
    mk, mm, mc = mutant(GL, "kmul"), mutant(GL, "m2"), mutant(GL, "canon")
    check("N  mutant K_MUL + 1: row phase 2", "sat", rows_query(mk, "nrows2", 2))
    check("N  mutant ~m2 -> m2: row phase 3", "sat", rows_query(mm, "nrows3", 3))
    check("N  mutant canonicalizer without the >= p case", "sat", canon_query(mc, "ncanon"))
    return e2e_query, (mk, mm, mc)


def gl64e():
    """End to end with the real multiplier at reduced width, and the mutants."""
    e2e_query, (mk, mm, mc) = E2E
    for w in (4, 6) if os.environ.get("LEC_W6") else (4,):
        check(f"E  W={w} end to end, real multiplier: cv == (a*b) mod p_W", "unsat", e2e_query(GL, f"e2e{w}", w))
    for nm, src in (("K_MUL + 1", mk), ("~m2 -> m2", mm), ("canonicalizer", mc)):
        check(f"N  mutant {nm}: W=4 end to end", "sat", e2e_query(src, "ne2e", 4))


# ------------------------------------------------------------------------------------ GF(2^128)
def gf128():
    D = 2                      # digit width as built
    steps = 128 // D

    def miter(src, top, tag, d):
        t = smt(f"{src} lec/lec_gf128.sv", top, tag, f"D={d}")
        return t + f"(declare-fun s () |{tag}_s|)\n(assert (not (|{tag}_n ok| s)))"

    for d in (2, 4):
        check(f"G1 digit step D={d} == r*z^{d} + h*d (mod g)", "unsat", miter(GF, "lec_gf128_step", f"g1d{d}", d))
    u = smt(GF, "qsag_gf128_clmul", "unit", f"D={D}")
    st = smt(GF, "qsag_gf128_step", "step", f"D={D}")
    n = lambda w, s: f"(|unit_n {w}| {s})"
    q = u + st + "(declare-fun s0 () |unit_s|) (declare-fun s1 () |unit_s|) (declare-fun q () |step_s|)\n"
    q += f"(assert (|unit_t| s0 s1))\n(assert (and {n('rst_n', 's0')} {n('srst_n', 's0')} (not {n('clr', 's0')})))\n"
    q += f"(assert (and {n('rst_n', 's1')} {n('srst_n', 's1')}))\n"
    q += f"(assert (= (|step_n r| q) {n('r', 's0')}))\n(assert (= (|step_n h| q) {n('h', 's0')}))\n"
    q += f"(assert (= (|step_n d| q) ((_ extract 127 {128 - D}) {n('x', 's0')})))\n"
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
    check("N  mutant reduction polynomial 0x86: digit step", "sat", miter(mp, "lec_gf128_step", "ng1p", D))
    check("N  mutant digit bit order: digit step", "sat", miter(md, "lec_gf128_step", "ng1d", D))


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
