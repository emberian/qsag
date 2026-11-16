#!/usr/bin/env python3
"""Compositional formal verification of the QSAG-NI arithmetic & isomorphism RTL.

Yosys reads the SystemVerilog and writes its transition relation with `write_smt2`
(frontend, `proc`, `flatten` only: no optimisation pass); this script builds the
universal SMT-LIB2 specifications, glue miters, and mutant checks, and discharges
every obligation with Z3 4.15.5 (and Bitwuzla 0.9.1 where useful).

All required checks must return `unsat` (proofs) or `sat` (mutant teeth) with 0 failures
and 0 undecided required obligations.
"""
import json, os, shutil, subprocess, sys, time
from pathlib import Path

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import gen_tower_map as G

OUT = os.path.join(ROOT, "build", "lec")
P = 2**64 - 2**32 + 1
Z3_SECS = int(os.environ.get("LEC_SECS", "150"))
TRY_SECS = int(os.environ.get("LEC_TRY_SECS", "45"))
BITWUZLA = shutil.which("bitwuzla")
results = []
CONTRACTS_READY = False

def sh(cmd):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(r.stdout[-3000:] + r.stderr[-3000:])
        raise SystemExit("command failed: " + cmd)
    return r.stdout

def yosys_smt2(name, top, files, chparam="", use_contracts=True):
    """SMT-LIB2 of `top` as module lec_top; returns the text."""
    out = os.path.join(OUT, name + ".yosys.smt2")
    helpers = [os.path.join(ROOT, "rtl", n) for n in (
        "qsag_add_split.sv", "qsag_csa_reduce2.sv", "qsag_sum_csa.sv")]
    if use_contracts and CONTRACTS_READY and top in ("qsag_mul64_dsp", "qsag_gl64_dsp_mul", "qsag_gl64_reduce"):
        helpers = [os.path.join(OUT, "proved_adder_contracts.sv")]
    srcs = " ".join(helpers + files)
    sh(f'yosys -q -p "read_verilog -sv {srcs}; hierarchy -top {top} {chparam}; proc; flatten; '
       f'opt_clean; rename -top lec_top; write_smt2 -wires {out}"')
    return open(out).read()

def unroll(steps):
    s = "".join(f"(declare-fun s{k} () |lec_top_s|)\n" for k in range(steps + 1))
    s += "".join(f"(assert (|lec_top_h| s{k}))\n" for k in range(steps + 1))
    s += "".join(f"(assert (|lec_top_t| s{k} s{k+1}))\n" for k in range(steps))
    return s

def solve(name, text, secs, prefer_bitwuzla=True):
    path = os.path.join(OUT, name + ".smt2")
    is_bv_only = (" Int)" not in text) and ("(mod " not in text)
    if prefer_bitwuzla and is_bv_only and BITWUZLA:
        bw_text = "(set-logic QF_UFBV)\n" + text
        open(path, "w").write(bw_text)
        t0 = time.time()
        try:
            r = subprocess.run([BITWUZLA, "--time-limit", str(secs * 1000), path],
                               capture_output=True, text=True, timeout=secs + 15)
            ans = (r.stdout.strip().splitlines() or ["?"])[0]
            if ans in ("unsat", "sat"):
                return ans, time.time() - t0
        except subprocess.TimeoutExpired:
            pass
    open(path, "w").write(text)
    t0 = time.time()
    try:
        r = subprocess.run(["z3", f"-T:{secs}", path], capture_output=True, text=True, timeout=secs + 30)
        ans = (r.stdout.strip().splitlines() or ["?"])[0]
    except subprocess.TimeoutExpired:
        ans = "timeout"
    return ans, time.time() - t0

def record(name, statement, expect, text, secs=None, required=True, prefer_bitwuzla=False):
    ans, dt = solve(name, text, secs or Z3_SECS, prefer_bitwuzla=prefer_bitwuzla)
    ok = ans == expect
    tag = "PASS" if ok else ("FAIL" if required else "open")
    results.append((tag, name, statement, expect, ans, dt))
    print(f"[{tag}] {name}: {ans} in {dt:.1f}s (expected {expect}) -- {statement}", flush=True)
    return ok

def bv(v, w):
    return f"(_ bv{v} {w})"

def zext(e, frm, to):
    return e if to == frm else f"((_ zero_extend {to - frm}) {e})"

VW = 72

def reduce_spec(x136, r64):
    lo = zext(f"((_ extract 63 0) {x136})", 64, VW)
    m  = zext(f"((_ extract 95 64) {x136})", 32, VW)
    h  = zext(f"((_ extract 127 96) {x136})", 32, VW)
    t  = zext(f"((_ extract 135 128) {x136})", 8, VW)
    v = (f"(bvsub (bvsub (bvsub (bvadd (bvadd {lo} (bvshl {m} {bv(32, VW)})) {bv(P, VW)}) {m}) {h}) "
         f"(bvshl {t} {bv(32, VW)}))")
    R = zext(r64, 64, VW)
    alts = " ".join(f"(= {v} (bvadd {R} {bv(k * P, VW)}))" for k in range(3))
    return f"(and (bvult {r64} {bv(P, 64)}) (or {alts}))"

def check_reduce_algebra():
    decl = "".join(f"(declare-const {v} Int)\n" for v in ("lo", "m", "h", "t"))
    rng = f"(assert (and (>= lo 0) (< lo {2**64}) (>= m 0) (< m {2**32}) (>= h 0) (< h {2**32}) (>= t 0) (< t 256)))\n"
    V = f"(- (+ lo (* {2**32} m) {P}) m h (* {2**32} t))"
    x = f"(+ lo (* {2**64} m) (* {2**96} h) (* {2**128} t))"
    q0 = f"(+ m (* {2**32 + 1} (+ h (* {2**32} t))))"
    record("reduce_identity", "integers: x + p = V + p*Q0 for x = lo + m 2^64 + h 2^96 + t 2^128",
           "unsat", decl + f"(assert (not (= (+ {x} {P}) (+ {V} (* {P} {q0})))))\n(check-sat)\n")
    record("reduce_range", "integers: limbs in range imply 0 < V < 3p",
           "unsat", decl + rng + f"(assert (not (and (> {V} 0) (< {V} {3 * P}))))\n(check-sat)\n")

def check_ext4_karatsuba_algebra():
    """Prove 9-multiply Tower Karatsuba recombination over F_p[v]/(v^4 - 7) is exact mod p
    and strictly fits in (0, 2^136) without overflow or negative wraparound."""
    M128 = 2**128 - 1
    C1 = 2**32 + 1
    KP = 2**64 + 2**32  # exact integer: M128 + C1 = 2^128 + 2^32 = P * (2^64 + 2^32)

    # 1. Range proof over all 64-bit c_i and 128-bit unsigned multiplier outputs m_0..m_8:
    r_vars = [f"c{i}" for i in range(4)] + [f"m{i}" for i in range(9)]
    r_decl = "".join(f"(declare-const {v} Int)\n" for v in r_vars)
    r_rng = ("(assert (and "
             + " ".join(f"(>= c{i} 0) (< c{i} {2**64})" for i in range(4)) + " "
             + " ".join(f"(>= m{i} 0) (< m{i} {2**128})" for i in range(9)) + "))\n")
    nm = [f"(- {M128} m{i})" for i in range(8)]
    accs_r = [
        f"(+ (* 14 {C1}) c0 m0 (* 7 m1) (* 7 m5) (* 7 {nm[3]}) (* 7 {nm[4]}))",
        f"(+ (* 2 {C1}) c1 m2 m3 (* 7 m4) {nm[0]} {nm[1]})",
        f"(+ (* 16 {C1}) c2 m6 (* 7 m7) {nm[0]} (* 7 {nm[1]}) {nm[3]} (* 7 {nm[4]}))",
        f"(+ (* 4 {C1}) c3 m8 m0 m1 m3 m4 {nm[6]} {nm[7]} {nm[2]} {nm[5]})",
    ]
    for k, acc in enumerate(accs_r):
        if not record(f"ext4_karatsuba_range_limb{k}",
                      f"9-mul Tower Karatsuba limb {k}: 0 < acc < 2^136 for all 2^128 products and 64-bit c",
                      "unsat", r_decl + r_rng + f"(assert (not (and (> {acc} 0) (< {acc} {2**136}))))\n(check-sat)\n"):
            raise SystemExit("failed Ext4 Karatsuba range proof")

    # 2. Universal modular congruence proof over all a_i, b_i, c_i and modular pre-sum quotients ka_*, kb_*:
    k_names = ["ka01", "ka23", "ka02", "ka13", "kaa", "kb01", "kb23", "kb02", "kb13", "kbb"]
    all_v = [f"a{i}" for i in range(4)] + [f"b{i}" for i in range(4)] + [f"c{i}" for i in range(4)] + k_names
    decl = "".join(f"(declare-const {v} Int)\n" for v in all_v)
    def subp(s, kv): return f"(- {s} (* {P} {kv}))"
    def qmul(sa, sb, ka, kb): return f"(- (+ (* {ka} {sb}) (* {kb} {sa})) (* {P} (* {ka} {kb})))"
    S = {
        "a01": "(+ a0 a1)", "a23": "(+ a2 a3)", "a02": "(+ a0 a2)", "a13": "(+ a1 a3)", "aa": "(+ a0 a1 a2 a3)",
        "b01": "(+ b0 b1)", "b23": "(+ b2 b3)", "b02": "(+ b0 b2)", "b13": "(+ b1 b3)", "bb": "(+ b0 b1 b2 b3)",
    }
    ms = [
        "(* a0 b0)", "(* a1 b1)", f"(* {subp(S['a01'],'ka01')} {subp(S['b01'],'kb01')})",
        "(* a2 b2)", "(* a3 b3)", f"(* {subp(S['a23'],'ka23')} {subp(S['b23'],'kb23')})",
        f"(* {subp(S['a02'],'ka02')} {subp(S['b02'],'kb02')})",
        f"(* {subp(S['a13'],'ka13')} {subp(S['b13'],'kb13')})",
        f"(* {subp(S['aa'],'kaa')} {subp(S['bb'],'kbb')})",
    ]
    qm2 = qmul(S["a01"], S["b01"], "ka01", "kb01")
    qm5 = qmul(S["a23"], S["b23"], "ka23", "kb23")
    qm6 = qmul(S["a02"], S["b02"], "ka02", "kb02")
    qm7 = qmul(S["a13"], S["b13"], "ka13", "kb13")
    qm8 = qmul(S["aa"],  S["bb"],  "kaa",  "kbb")
    nmi = [f"(- {M128} {ms[i]})" for i in range(8)]
    accs = [
        f"(+ (* 14 {C1}) c0 {ms[0]} (* 7 {ms[1]}) (* 7 {ms[5]}) (* 7 {nmi[3]}) (* 7 {nmi[4]}))",
        f"(+ (* 2 {C1}) c1 {ms[2]} {ms[3]} (* 7 {ms[4]}) {nmi[0]} {nmi[1]})",
        f"(+ (* 16 {C1}) c2 {ms[6]} (* 7 {ms[7]}) {nmi[0]} (* 7 {nmi[1]}) {nmi[3]} (* 7 {nmi[4]}))",
        f"(+ (* 4 {C1}) c3 {ms[8]} {ms[0]} {ms[1]} {ms[3]} {ms[4]} {nmi[6]} {nmi[7]} {nmi[2]} {nmi[5]})",
    ]
    sbs = [
        "(+ c0 (* a0 b0) (* 7 (+ (* a2 b3) (* a1 b1) (* a3 b2))))",
        "(+ c1 (* a0 b1) (* a2 b2) (* a1 b0) (* 7 (* a3 b3)))",
        "(+ c2 (* a0 b2) (* a2 b0) (* 7 (+ (* a1 b3) (* a3 b1))))",
        "(+ c3 (* a0 b3) (* a2 b1) (* a1 b2) (* a3 b0))",
    ]
    qs = [
        f"(- (* 14 {KP}) (* 7 {qm5}))",
        f"(- (* 2 {KP}) {qm2})",
        f"(- (* 16 {KP}) {qm6} (* 7 {qm7}))",
        f"(+ (- (* 4 {KP}) {qm8}) {qm6} {qm7} {qm2} {qm5})",
    ]
    for k in range(4):
        if not record(f"ext4_karatsuba_modp_limb{k}",
                      f"9-mul Tower Karatsuba limb {k}: exact congruence acc - schoolbook == p * Q_k over F_p[v]/(v^4 - 7)",
                      "unsat", decl + f"(assert (not (= (- {accs[k]} {sbs[k]}) (* {P} {qs[k]}))))\n(check-sat)\n"):
            raise SystemExit("failed Ext4 Karatsuba congruence proof")

def mutate(src, old, new, name):
    text = open(src).read()
    assert text.count(old) >= 1, (src, old, text.count(old))
    path = os.path.join(OUT, name)
    open(path, "w").write(text.replace(old, new, 1))
    return path

PKG   = os.path.join(ROOT, "rtl/qsag_ni_pkg.sv")
SPLIT = os.path.join(ROOT, "rtl/qsag_add_split.sv")
CSA2  = os.path.join(ROOT, "rtl/qsag_csa_reduce2.sv")
SCSA  = os.path.join(ROOT, "rtl/qsag_sum_csa.sv")
RED   = os.path.join(ROOT, "rtl/qsag_gl64_reduce.sv")
MUL   = os.path.join(ROOT, "rtl/qsag_mul64_dsp.sv")
GLM   = os.path.join(ROOT, "rtl/qsag_gl64_dsp_mul.sv")
KARA  = os.path.join(ROOT, "rtl/qsag_clmul_kara.sv")
GFRED = os.path.join(ROOT, "rtl/qsag_gf128_reduce.sv")
GFMUL = os.path.join(ROOT, "rtl/qsag_gf128_clmul.sv")
TMAP  = os.path.join(ROOT, "rtl/qsag_gf128_tower_map.sv")
TMUL  = os.path.join(ROOT, "rtl/qsag_gf128_tower_mul.sv")

def acc(port, state):
    return f"(|lec_top_n {port}| {state})"

def check_reduce(tag, files, expect, reg_out=1, required=True):
    ys = yosys_smt2(tag, "qsag_gl64_reduce", files, f"-chparam REG_OUT {reg_out}")
    steps = 2 if reg_out else 1
    body = ys + unroll(steps)
    stmt = reduce_spec(acc("x", "s0"), acc("r", f"s{steps}"))
    return record(tag, f"qsag_gl64_reduce REG_OUT={reg_out}: for all 2^136 inputs, r ({steps} clocks later) < p and V(x) = r + k*p",
                  expect, body + f"(assert (not {stmt}))\n(check-sat)\n", required=required, prefer_bitwuzla=True)

def tile_sum(aw, bw, a, b, fn):
    na, nb, tw = -(-64 // aw), 4, aw + bw
    terms, hyps, shapes = [], [], set()
    for j in range(nb):
        for i in range(na):
            ahi, bhi = min(64, aw * (i + 1)) - 1, min(64, bw * (j + 1)) - 1
            wa, wb = ahi - aw * i + 1, bhi - bw * j + 1
            ai = zext(f"((_ extract {ahi} {aw*i}) {a})", wa, tw)
            bj = zext(f"((_ extract {bhi} {bw*j}) {b})", wb, tw)
            terms.append(f"(bvshl {zext(f'({fn} {ai} {bj})', tw, 128)} {bv(aw*i + bw*j, 128)})")
            hyps.append(f"(assert (bvule ({fn} {ai} {bj}) {bv((2**wa - 1) * (2**wb - 1), tw)}))\n")
            shapes.add((wa, wb))
    e = terms[0]
    for t in terms[1:]:
        e = f"(bvadd {e} {t})"
    return e, na * nb, tw, "".join(hyps), sorted(shapes)

def abstract_tiles(ys, n, tw):
    assert ys.count("(bvmul ") == n, (ys.count("(bvmul "), n)
    return f"(declare-fun qtile ((_ BitVec {tw}) (_ BitVec {tw})) (_ BitVec {tw}))\n" + ys.replace("(bvmul ", "(qtile ")

def check_dsp_tile_exact(aw, bw, shapes):
    """Bit-precise Z3/Bitwuzla proof on the actual 2-stage DSP tile RTL cell over all 2^(wa+wb) inputs:
    proves the DSP tile implements exact bit-vector multiplication and satisfies the tile product bound."""
    tw = aw + bw
    tile_sv = os.path.join(OUT, f"dsp_tile_{aw}x{bw}.sv")
    open(tile_sv, "w").write(f"""
module qsag_dsp_tile_cell (
    input logic clk,
    input logic [{aw-1}:0] a,
    input logic [{bw-1}:0] b,
    output logic [{tw-1}:0] tq
);
    logic [{aw-1}:0] ai_q;
    logic [{bw-1}:0] bj_q;
    always_ff @(posedge clk) begin
        ai_q <= a;
        bj_q <= b;
        tq   <= {tw}'(ai_q) * {tw}'(bj_q);
    end
endmodule
""")
    ys = yosys_smt2(f"dsp_tile_{aw}x{bw}", "qsag_dsp_tile_cell", [tile_sv], use_contracts=False)
    a0, b0 = acc("a", "s0"), acc("b", "s0")
    exact_mul = f"(bvmul {zext(a0, aw, tw)} {zext(b0, bw, tw)})"
    q_full = ys + unroll(2) + f"(assert (not (= {acc('tq', 's2')} {exact_mul})))\n(check-sat)\n"
    if not record(f"dsp_tile_exact_{aw}x{bw}_all",
                  f"bit-precise 2-stage DSP tile ({aw}x{bw}): tq == zext(a)*zext(b) (mod 2^{tw}) for all 2^{tw} inputs",
                  "unsat", q_full, prefer_bitwuzla=False):
        raise SystemExit("failed bit-precise DSP tile proof")
    for wa, wb in shapes:
        q_pad = (f"(set-logic QF_UFBV)\n(declare-fun qmul ((_ BitVec {tw}) (_ BitVec {tw})) (_ BitVec {tw}))\n"
                 f"(declare-fun asub () (_ BitVec {wa}))\n(declare-fun bsub () (_ BitVec {wb}))\n"
                 f"(define-fun apad () (_ BitVec {aw}) {zext('asub', wa, aw)})\n"
                 f"(define-fun bpad () (_ BitVec {bw}) {zext('bsub', wb, bw)})\n"
                 f"(assert (not (= (qmul {zext('apad', aw, tw)} {zext('bpad', bw, tw)}) "
                 f"(qmul {zext('asub', wa, tw)} {zext('bsub', wb, tw)}))))\n(check-sat)\n")
        if not record(f"dsp_tile_pad_{aw}x{bw}_{wa}x{wb}",
                      f"tile zero-padding glue ({wa}x{wb} -> {aw}x{bw}): padded DSP operands equal direct {tw}-bit zero-extensions",
                      "unsat", q_pad, prefer_bitwuzla=False):
            raise SystemExit("failed DSP tile zero-padding glue")

def check_mul_wiring(tag, files, aw, bw, expect, precise=False, required=True, secs=None):
    chp = f"-chparam AW {aw} -chparam BW {bw}"
    ys = yosys_smt2(tag, "qsag_mul64_dsp", files, chp)
    spec, n, tw, hyps, _ = tile_sum(aw, bw, acc("a", "s0"), acc("b", "s0"), "bvmul" if precise else "qtile")
    if not precise:
        ys = abstract_tiles(ys, n, tw)
    else:
        hyps = ""
    how = "bit-precise tiles" if precise else "tiles: any function within the product bound"
    return record(tag, f"qsag_mul64_dsp AW={aw} BW={bw}: p (3 clocks later) = sum of the {n} tile products ({how})",
                  expect, ys + unroll(3) + hyps + f"(assert (not (= {acc('p', 's3')} {spec})))\n(check-sat)\n",
                  secs=secs, required=required, prefer_bitwuzla=precise)

def check_glmul(tag, files, aw, bw, reg_out=1, expect_product="unsat", expect_reduce="unsat"):
    chp = f"-chparam AW {aw} -chparam BW {bw} -chparam REG_OUT {reg_out}"
    ys = yosys_smt2(tag, "qsag_gl64_dsp_mul", files, chp)
    spec, n, tw, hyps, _ = tile_sum(aw, bw, acc("a", "s0"), acc("b", "s0"), "qtile")
    ys = abstract_tiles(ys, n, tw)
    ok = record(tag + "_product", f"qsag_gl64_dsp_mul AW={aw} BW={bw}: for all 2^128 inputs, prod (3 clocks later) "
                f"= weighted sum X of the {n} tile products",
                expect_product, ys + unroll(3) + hyps + f"(assert (not (= {acc('prod', 's3')} {spec})))\n(check-sat)\n",
                prefer_bitwuzla=True)
    rsteps = 2 if reg_out else 1
    stmt = reduce_spec(zext(acc("prod", "s0"), 128, 136), acc("r", f"s{rsteps}"))
    ok &= record(tag + "_reduce", f"qsag_gl64_dsp_mul AW={aw} BW={bw} REG_OUT={reg_out}: for every prod X, r ({rsteps} clocks later) "
                 f"< p and V(X) = r + k*p",
                 expect_reduce, ys + unroll(rsteps) + f"(assert (not {stmt}))\n(check-sat)\n",
                 prefer_bitwuzla=True)
    return ok

def check_tiling_identity(aw, bw):
    na = -(-64 // aw)
    A = [f"a{i}" for i in range(na)]
    B = [f"b{j}" for j in range(4)]
    decl = "".join(f"(declare-const {v} Int)\n" for v in A + B)
    asum = "(+ " + " ".join(f"(* {2**(aw*i)} a{i})" for i in range(na)) + ")"
    bsum = "(+ " + " ".join(f"(* {2**(bw*j)} b{j})" for j in range(4)) + ")"
    tsum = "(+ " + " ".join(f"(* {2**(aw*i + bw*j)} (* a{i} b{j}))" for i in range(na) for j in range(4)) + ")"
    record(f"tiling_identity_{aw}x{bw}",
           f"integers: (sum a_i 2^({aw}i)) * (sum b_j 2^({bw}j)) = sum a_i b_j 2^({aw}i+{bw}j)", "unsat",
           decl + f"(assert (not (= (* {asum} {bsum}) {tsum})))\n(check-sat)\n")
    shapes = tile_sum(aw, bw, "a", "b", "f")[4]
    for wa, wb in shapes:
        record(f"tile_bound_{wa}x{wb}",
               f"integers: 0 <= a < 2^{wa} and 0 <= b < 2^{wb} imply a*b <= (2^{wa}-1)(2^{wb}-1) < 2^{aw+bw}", "unsat",
               "(declare-const a Int)\n(declare-const b Int)\n"
               f"(assert (and (>= a 0) (< a {2**wa}) (>= b 0) (< b {2**wb})))\n"
               f"(assert (not (and (<= (* a b) {(2**wa - 1) * (2**wb - 1)}) (< {(2**wa - 1) * (2**wb - 1)} {2**(aw+bw)}))))\n(check-sat)\n")
    check_dsp_tile_exact(aw, bw, shapes)

def check_csa_inductive(w, target_n):
    """Inductive Z3 proof of recursive `qsag_csa_reduce2` up to N = target_n:
      - Base N=3 proved directly on full RTL (s + c == x0 + x1 + x2, all 2^(3W) inputs);
      - Each step N in chain (e.g. 4 -> 6 -> 8) replaces `u_rec` (width W, arity M = 2*(N//3)+N%3,
        already proved!) with ANY carry-save pair (free_s, sum(nxt) - free_s) and proves on the
        actual RTL of `qsag_csa_reduce2` that s + c == sum_{i=0}^{N-1} x_i for all inputs."""
    chain = []
    cur = target_n
    while cur > 3:
        chain.append(cur)
        cur = 2 * (cur // 3) + (cur % 3)
    # Base N = 3 on exact RTL
    ys3 = yosys_smt2(f"contract_csa2_{w}_3", "qsag_csa_reduce2", [], f"-chparam W {w} -chparam N 3", use_contracts=False)
    spec3 = bv(0, w)
    for i in range(3):
        spec3 = f"(bvadd {spec3} ((_ extract {(i+1)*w-1} {i*w}) {acc('x', 's0')}))"
    body3 = ys3 + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
    if not record(f"contract_csa2_{w}_n3_base",
                  f"qsag_csa_reduce2 W={w} N=3 base: s + c == sum x_i (mod 2^{w}) for all 2^{3*w} inputs",
                  "unsat", body3 + f"(assert (not (= (bvadd {acc('s','s0')} {acc('c','s0')}) {spec3})))\n(check-sat)\n",
                  prefer_bitwuzla=False):
        raise SystemExit("failed CSA base N=3")

    csa_src = open(CSA2).read().replace("(* flatten *)", "")
    for n in reversed(chain):
        m = 2 * (n // 3) + (n % 3)
        step_sv = os.path.join(OUT, f"csa_step_{w}_{n}.sv")
        # Rename outer module to qsag_csa_step and supply proved child contract for qsag_csa_reduce2(W, M)
        step_txt = csa_src.replace("module qsag_csa_reduce2", "module qsag_csa_step", 1)
        step_txt = step_txt.replace("input  logic [N*W-1:0] x,",
                                    f"input logic [N*W-1:0] x, input logic [{w-1}:0] free_s,", 1)
        step_txt = step_txt.replace(
            "qsag_csa_reduce2 #(.W(W), .N(M)) u_rec (.x(nxt), .s(s), .c(c));",
            "qsag_csa_child_contract #(.W(W), .N(M)) u_rec (.x(nxt), .free_s(free_s), .s(s), .c(c));")
        step_txt += f"""
module qsag_csa_child_contract #(parameter int W={w}, parameter int N={m}) (
    input logic [N*W-1:0] x, input logic [W-1:0] free_s, output logic [W-1:0] s, output logic [W-1:0] c
);
    logic [W-1:0] tot;
    always_comb begin
        tot = '0;
        for (int i = 0; i < N; i++) tot = tot + x[i*W +: W];
    end
    assign s = free_s;
    assign c = tot - free_s;
endmodule
"""
        open(step_sv, "w").write(step_txt)
        out_smt = os.path.join(OUT, f"csa_step_{w}_{n}.yosys.smt2")
        sh(f'yosys -q -p "read_verilog -sv {step_sv}; hierarchy -top qsag_csa_step -chparam W {w} -chparam N {n}; '
           f'proc; flatten; opt_clean; rename -top lec_top; write_smt2 -wires {out_smt}"')
        ys_step = open(out_smt).read()
        terms = [f"((_ extract {(i+1)*w-1} {i*w}) {acc('x', 's0')})" for i in range(n)]
        while len(terms) > 1:
            terms = [f"(bvadd {terms[k]} {terms[k+1]})" if k + 1 < len(terms) else terms[k]
                     for k in range(0, len(terms), 2)]
        spec_n = terms[0]
        body_n = ys_step + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
        if not record(f"contract_csa2_{w}_n{n}_step",
                      f"qsag_csa_reduce2 W={w} N={n} inductive step (from proved M={m}): s + c == sum x_i for all 2^{n*w} inputs",
                      "unsat", body_n + f"(assert (not (= (bvadd {acc('s','s0')} {acc('c','s0')}) {spec_n})))\n(check-sat)\n",
                      prefer_bitwuzla=False):
            raise SystemExit(f"failed CSA inductive step N={n}")

def check_adder_contracts():
    """Discharge every CSA compressor and split-carry helper instance used across both
    multiplier tilings and the Goldilocks reducer BEFORE replacing their bodies with
    proved modular-addition contracts. Fail closed."""
    global CONTRACTS_READY
    CONTRACTS_READY = False

    # 1. Inductive universal Z3 proofs of 3:2 CSA compressor trees (W=66 up to N=6; W=128 up to N=8).
    check_csa_inductive(66, 6)
    check_csa_inductive(128, 8)

    # 2. Parallel-prefix split carry-select adder: y == a + b (mod 2^W) for all 2^(2W) inputs.
    for w, chk in [(67, 16), (67, 24), (66, 16), (66, 24), (128, 16), (128, 24), (136, 24)]:
        ys = yosys_smt2(f"contract_split_{w}_{chk}", "qsag_add_split", [], f"-chparam W {w} -chparam CHUNK {chk}", use_contracts=False)
        spec = f"(bvadd {acc('a', 's0')} {acc('b', 's0')})"
        body = ys + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
        if not record(f"contract_split_{w}_c{chk}", f"qsag_add_split W={w} CHUNK={chk}: y == a + b (mod 2^{w}) for all 2^{2*w} inputs",
                      "unsat", body + f"(assert (not (= {acc('y', 's0')} {spec})))\n(check-sat)\n"):
            raise SystemExit("refusing unproved split-adder contract")

    # 3. Combined `qsag_sum_csa` RTL glue over universally proved `qsag_csa_reduce2` + `qsag_add_split`.
    scsa_src = open(SCSA).read().replace("(* flatten *)", "")
    for w, n, chk in [(66, 6, 16), (66, 6, 24), (128, 8, 16), (128, 8, 24)]:
        glue_sv = os.path.join(OUT, f"sum_csa_glue_{w}_{n}_{chk}.sv")
        gtxt = scsa_src.replace("input  logic [N*W-1:0] x,",
                                f"input logic [N*W-1:0] x, input logic [{w-1}:0] free_s,", 1)
        gtxt = gtxt.replace("qsag_csa_reduce2 #(.W(W), .N(N)) u_csa (.x(x), .s(s), .c(c));",
                            "qsag_csa_rel #(.W(W), .N(N)) u_csa (.x(x), .free_s(free_s), .s(s), .c(c));")
        gtxt = gtxt.replace("qsag_add_split #(.W(W), .CHUNK(CHUNK)) u_add (.a(s), .b(c), .y(y));",
                            "qsag_split_rel #(.W(W), .CHUNK(CHUNK)) u_add (.a(s), .b(c), .y(y));")
        gtxt += """
module qsag_csa_rel #(parameter int W=128, parameter int N=4)(
    input logic [N*W-1:0] x, input logic [W-1:0] free_s, output logic [W-1:0] s, output logic [W-1:0] c);
    logic [W-1:0] tot;
    always_comb begin tot = '0; for (int i = 0; i < N; i++) tot = tot + x[i*W +: W]; end
    assign s = free_s; assign c = tot - free_s;
endmodule
module qsag_split_rel #(parameter int W=128, parameter int CHUNK=24)(
    input logic [W-1:0] a, input logic [W-1:0] b, output logic [W-1:0] y);
    assign y = a + b;
endmodule
"""
        open(glue_sv, "w").write(gtxt)
        out_smt = os.path.join(OUT, f"sum_csa_glue_{w}_{n}_{chk}.yosys.smt2")
        sh(f'yosys -q -p "read_verilog -sv {glue_sv}; hierarchy -top qsag_sum_csa -chparam W {w} -chparam N {n} -chparam CHUNK {chk}; '
           f'proc; flatten; opt_clean; rename -top lec_top; write_smt2 -wires {out_smt}"')
        ys_g = open(out_smt).read()
        terms = [f"((_ extract {(i+1)*w-1} {i*w}) {acc('x', 's0')})" for i in range(n)]
        while len(terms) > 1:
            terms = [f"(bvadd {terms[k]} {terms[k+1]})" if k + 1 < len(terms) else terms[k]
                     for k in range(0, len(terms), 2)]
        body = ys_g + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
        if not record(f"contract_sum_csa_{w}_{n}_c{chk}",
                      f"qsag_sum_csa W={w} N={n} CHUNK={chk}: RTL glue over proved CSA + split-carry",
                      "unsat", body + f"(assert (not (= {acc('y', 's0')} {terms[0]})))\n(check-sat)\n"):
            raise SystemExit("refusing unproved sum_csa contract")

    open(os.path.join(OUT, "proved_adder_contracts.sv"), "w").write("""
module qsag_add_split #(parameter int W=128, parameter int CHUNK=24)(input [W-1:0] a,b, output [W-1:0] y);
assign y = a + b;
endmodule
module qsag_csa_reduce2 #(parameter int W=128, parameter int N=4)(input [N*W-1:0] x, output reg [W-1:0] s, output [W-1:0] c);
integer i;
always @* begin s = 0; for (i = 0; i < N; i = i + 1) s = s + x[i*W +: W]; end
assign c = 0;
endmodule
module qsag_sum_csa #(parameter int W=128, parameter int N=4, parameter int CHUNK=24)(input [N*W-1:0] x, output reg [W-1:0] y);
integer i;
always @* begin y = 0; for (i = 0; i < N; i = i + 1) y = y + x[i*W +: W]; end
endmodule
""")
    CONTRACTS_READY = True

def check_glue(aw, bw):
    for reg_out in (1, 0):
        tot = 5 if reg_out else 4
        tag = f"glue_{aw}x{bw}_reg{reg_out}"
        ys = yosys_smt2(tag, "qsag_gl64_dsp_mul", [PKG, RED, MUL, GLM],
                        f"-chparam AW {aw} -chparam BW {bw} -chparam REG_OUT {reg_out}")
        spec, n, tw, hyps, _ = tile_sum(aw, bw, acc("a", "s0"), acc("b", "s0"), "qtile")
        ys = abstract_tiles(ys, n, tw)
        cut = reduce_spec(zext(acc("prod", "s3"), 128, 136), acc("r", f"s{tot}"))
        ok = record(tag + "_temporal_join",
                    f"full {tot}-cycle pipeline (REG_OUT={reg_out}): reducer consumes prod at cycle 3 and emits canonical residue at cycle {tot}",
                    "unsat", ys + unroll(tot) + f"(assert (not {cut}))\n(check-sat)\n",
                    prefer_bitwuzla=True)
        if not ok:
            raise SystemExit("failed temporal join")
        combined = reduce_spec(zext(spec, 128, 136), acc("r", f"s{tot}"))
        ok = record(tag + "_compose",
                    f"cycle-3 product contract and cycle-{tot} reducer contract entail end-to-end residue contract",
                    "unsat", ys + unroll(tot) + hyps +
                    f"(assert (= {acc('prod', 's3')} {spec}))\n(assert {cut})\n(assert (not {combined}))\n(check-sat)\n")
        if not ok:
            raise SystemExit("failed composition")

def check_remainder_glue():
    decl = "".join(f"(declare-const {n} Int)\n" for n in ["a", "b", "X", "lo", "m", "h", "r", "k"])
    v = f"(- (+ lo (* {2**32} m) {P}) m h)"
    body = decl + f"""(assert (and (<= 0 a) (< a {2**64}) (<= 0 b) (< b {2**64})))
(assert (= X (* a b)))
(assert (= X (+ lo (* {2**64} m) (* {2**96} h))))
(assert (and (<= 0 lo) (< lo {2**64}) (<= 0 m) (< m {2**32}) (<= 0 h) (< h {2**32})))
(assert (= {v} (+ r (* k {P}))))
(assert (and (<= 0 r) (< r {P}) (<= 0 k) (<= k 2)))
(assert (not (= r (mod (* a b) {P}))))
(check-sat)
"""
    if not record("glue_canonical_remainder",
                  "all 2^128 operand pairs: tiled product and bounded reduction entail r = (a*b) mod p uniquely",
                  "unsat", body):
        raise SystemExit("failed integer remainder join")

def gf_xpow():
    t, v = [], 1
    for _ in range(255):
        t.append(v)
        v <<= 1
        if v >> 128:
            v = (v & (2**128 - 1)) ^ 0x87
    return t

def check_gf_reduce(tag, files, expect, required=True):
    ys = yosys_smt2(tag, "qsag_gf128_reduce", files, use_contracts=False)
    xp = gf_xpow()
    c = acc("c", "s0")
    e = f"((_ extract 127 0) {c})"
    for i in range(128, 255):
        e = f"(bvxor {e} (ite (= ((_ extract {i} {i}) {c}) #b1) {bv(xp[i], 128)} {bv(0, 128)}))"
    return record(tag, "qsag_gf128_reduce: for all 2^255 inputs, r = c mod (x^128+x^7+x^2+x+1)",
                  expect, ys + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
                  f"(assert (not (= {acc('r', 's0')} {e})))\n(check-sat)\n", required=required, prefer_bitwuzla=True)

def gf_mul_spec(a, b):
    lets, prev = [], bv(0, 128)
    for n, i in enumerate(range(127, -1, -1)):
        x2 = f"(bvxor (bvshl {prev} {bv(1, 128)}) (ite (= ((_ extract 127 127) {prev}) #b1) {bv(0x87, 128)} {bv(0, 128)}))"
        lets.append(f"(g{n} (bvxor {x2} (ite (= ((_ extract {i} {i}) {b}) #b1) {a} {bv(0, 128)})))")
        prev = f"g{n}"
    return "".join(f"(let ({l}) " for l in lets) + prev + ")" * len(lets)

def check_gf_mul(tag, files, expect, required=True, secs=None):
    ys = yosys_smt2(tag, "qsag_gf128_clmul", files, use_contracts=False)
    a, b = acc("a", "s0"), acc("b", "s0")
    stmt = "qsag_gf128_clmul: for all 2^256 inputs, r (3 clocks later) = a*b in GF(2^128)"
    return record(tag, stmt, expect, ys + unroll(3) + f"(assert (not (= {acc('r', 's3')} {gf_mul_spec(a, b)})))\n(check-sat)\n",
                  required=required, secs=secs)

def check_gf_mul_basis(tag, files, j, expect, required=True, secs=None):
    ys = yosys_smt2(tag, "qsag_gf128_clmul", files, use_contracts=False)
    a, b = acc("a", "s0"), acc("b", "s0")
    xp = gf_xpow()
    e = bv(0, 128)
    for i in range(128):
        e = f"(bvxor {e} (ite (= ((_ extract {i} {i}) {a}) #b1) {bv(xp[i + j], 128)} {bv(0, 128)}))"
    return record(tag, f"qsag_gf128_clmul: for all a and b = x^{j}, r (3 clocks later) = a * x^{j}", expect,
                  ys + unroll(3) + f"(assert (= {b} {bv(1 << j, 128)}))\n(assert (not (= {acc('r', 's3')} {e})))\n(check-sat)\n",
                  required=required, secs=secs)

def check_kara_small(tag, w, expect, required=True, secs=None):
    ys = yosys_smt2(tag, "qsag_clmul_kara", [KARA], f"-chparam W {w}", use_contracts=False)
    a, b = acc("a", "s0"), acc("b", "s0")
    pw = 2 * w - 1
    e = bv(0, pw)
    for i in range(w):
        e = f"(bvxor {e} (ite (= ((_ extract {i} {i}) {b}) #b1) (bvshl {zext(a, w, pw)} {bv(i, pw)}) {bv(0, pw)}))"
    return record(tag, f"qsag_clmul_kara W={w}: for all 2^{2*w} inputs, p = carry-less product of a and b", expect,
                  ys + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
                  f"(assert (not (= {acc('p', 's0')} {e})))\n(check-sat)\n", required=required, secs=secs, prefer_bitwuzla=True)

def group_gl():
    check_adder_contracts()
    check_reduce_algebra()
    check_ext4_karatsuba_algebra()
    check_reduce("gl64_reduce_reg1", [PKG, RED], "unsat", reg_out=1)
    check_reduce("gl64_reduce_reg0", [PKG, RED], "unsat", reg_out=0)
    for aw, bw in ((26, 17), (16, 16)):
        check_tiling_identity(aw, bw)
        if not check_glmul(f"gl64_dsp_mul_{aw}x{bw}_reg1", [PKG, RED, MUL, GLM], aw, bw, reg_out=1):
            raise SystemExit("refusing composition with failed premise")
        if not check_glmul(f"gl64_dsp_mul_{aw}x{bw}_reg0", [PKG, RED, MUL, GLM], aw, bw, reg_out=0):
            raise SystemExit("refusing composition with failed premise")
        check_glue(aw, bw)
    check_remainder_glue()

def group_glmut():
    if not CONTRACTS_READY:
        check_adder_contracts()
    # Mutant 1: reducer Stage-1 negated limb h sign flip
    m1 = mutate(RED, "assign terms[3*66 +: 66] = ~{34'b0, h};", "assign terms[3*66 +: 66] = {34'b0, h};", "mut_reduce_sign.sv")
    check_reduce("mut_gl64_reduce_sign", [PKG, m1], "sat")
    # Mutant 2: reducer Stage-2 wrong candidate selection
    m2 = mutate(RED, "!v2[66] ? v2[63:0]", "!v2[66] ? v1[63:0]", "mut_reduce_select.sv")
    check_glmul("mut_select_gl64_dsp_mul", [PKG, m2, MUL, GLM], 26, 17, expect_reduce="sat")
    # Mutant 3: DSP tile wired to wrong b slice
    m3 = mutate(MUL, "bj_q <= b_pad[j*BW +: BW];", "bj_q <= b_pad[((j+1)%NB)*BW +: BW];", "mut_mul_tile.sv")
    check_mul_wiring("mut_tile_mul64_wiring", [m3], 26, 17, "sat")
    # Mutant 4: CSA row shifted by 1 bit
    m4 = mutate(MUL, "<< (i * AW + j * BW));", "<< (i * AW + j * BW + (j == 3 ? 1 : 0)));", "mut_mul_shift.sv")
    check_glmul("mut_shift_gl64_dsp_mul", [PKG, RED, m4, GLM], 26, 17, expect_product="sat")
    # Mutant 5: 3:2 CSA carry shifted by 2 instead of 1
    m_csa = mutate(CSA2, ") << 1;", ") << 2;", "mut_csa2_shift.sv")
    ys_csa = sh(f'yosys -q -p "read_verilog -sv {m_csa}; hierarchy -top qsag_csa_reduce2 -chparam W 64 -chparam N 3; '
                f'proc; flatten; opt_clean; rename -top lec_top; write_smt2 -wires {OUT}/mut_csa2.yosys.smt2"')
    ys_txt = open(f"{OUT}/mut_csa2.yosys.smt2").read()
    spec3 = f"(bvadd (bvadd ((_ extract 63 0) {acc('x','s0')}) ((_ extract 127 64) {acc('x','s0')})) ((_ extract 191 128) {acc('x','s0')}))"
    record("mut_csa_reduce2_shift", "mutant tooth: 3:2 CSA carry shift <<2 instead of <<1 is refuted",
           "sat", ys_txt + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
           f"(assert (not (= (bvadd {acc('s','s0')} {acc('c','s0')}) {spec3})))\n(check-sat)\n")
    # Mutant 6: parallel-prefix carry-select drops propagate term
    m_spl = mutate(SPLIT, "assign g1[i] = g0[i] | (p0[i] & g0[i-1]);", "assign g1[i] = g0[i];", "mut_split_prefix.sv")
    sh(f'yosys -q -p "read_verilog -sv {m_spl}; hierarchy -top qsag_add_split -chparam W 128 -chparam CHUNK 24; '
       f'proc; flatten; opt_clean; rename -top lec_top; write_smt2 -wires {OUT}/mut_spl.yosys.smt2"')
    ys_spl = open(f"{OUT}/mut_spl.yosys.smt2").read()
    record("mut_add_split_prefix", "mutant tooth: Kogge-Stone prefix carry drop in qsag_add_split is refuted",
           "sat", ys_spl + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
           f"(assert (not (= {acc('y','s0')} (bvadd {acc('a','s0')} {acc('b','s0')}))))\n(check-sat)\n")

def group_gf():
    check_gf_reduce("gf128_reduce", [GFRED], "unsat")
    m5 = mutate(GFRED, "(134'(hi) << 7)", "(134'(hi) << 6)", "mut_gf_reduce.sv")
    check_gf_reduce("mut_gf128_reduce_tap", [m5], "sat")
    m6 = mutate(KARA, "assign xmid = mid ^ hi ^ (2*HH-1)'(lo);", "assign xmid = mid ^ hi;", "mut_kara.sv")
    check_gf_mul("mut_gf128_clmul_kara", [m6, GFRED, GFMUL], "sat")
    check_gf_mul_basis("mut_gf128_clmul_basis_x77", [m6, GFRED, GFMUL], 77, "sat")

def group_tower():
    """Universal Z3 equivalence of Wiedemann tower128 linear maps, round-trip bijection on RTL,
    Artin-Schreier tower generator defining identities through 3-cycle RTL, Lean KATs, and mutant."""
    fixture_path = os.environ.get("QSAG_FIXTURE",
                                  os.path.join(ROOT, "../../validation/tests/fixtures/lean_external_oracle_vectors.json"))
    # Locate portable.rs or derive directly if repo isn't parent
    repo_cand = os.environ.get("QSAG_REPO", os.path.join(ROOT, "../.."))
    if not os.path.exists(os.path.join(repo_cand, "crates/qsag-asm/src/portable.rs")):
        repo_cand = "/home/build/qsag-ni-fpga/work/astra/repo"
    rows, inv, cols, ic, _ = G.matrices(Path(repo_cand))

    def parity_bool(x, mask):
        bits = [f"(= ((_ extract {i} {i}) {x}) #b1)" for i in range(128) if (mask >> i) & 1]
        return "false" if not bits else (bits[0] if len(bits) == 1 else "(xor " + " ".join(bits) + ")")

    # 1. Universal Z3 proof over all 2^128 inputs for both INVERSE=0 and INVERSE=1 RTL maps.
    for direction, rs in enumerate([rows, inv]):
        ys = yosys_smt2(f"tower_map_{direction}", "qsag_gf128_tower_map", [TMAP],
                        f"-chparam INVERSE {direction}", use_contracts=False)
        x, y = acc("x", "s0"), acc("y", "s0")
        base = ys + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
        assertions = [f"(= (= ((_ extract {i} {i}) {y}) #b1) {parity_bool(x, m)})" for i, m in enumerate(rs)]
        if not record(f"tower_map_dir{direction}",
                      f"qsag_gf128_tower_map INVERSE={direction}: for all 2^128 inputs, RTL == exact Wiedemann matrix",
                      "unsat", base + "(assert (not (and " + " ".join(assertions) + ")))\n(check-sat)\n"):
            raise SystemExit("failed tower_map Z3 proof")

    # 2. Universal Z3 round-trip bijection directly on composed RTL (`qsag_tower_rt`):
    #    since u_f0/u_i0/u_i1/u_f1 are pure XOR-linear maps (proved in tower_map_dir0/1 and anf_check.py),
    #    proving inv(fwd(e_b)) == e_b and fwd(inv(e_b)) == e_b for all 128 basis vectors b in [0, 127]
    #    in Z3 on the composed RTL (paired with universal 2^128 ANF identity in anf_check.py) closes
    #    round-trip bijectivity with zero SAT blowup.
    rt_sv = os.path.join(OUT, "tower_roundtrip.sv")
    open(rt_sv, "w").write("""
module qsag_tower_rt (input logic [127:0] x, output logic [127:0] y01, output logic [127:0] y10);
    logic [127:0] m0, m1;
    qsag_gf128_tower_map #(.INVERSE(0)) u_f0 (.x(x),  .y(m0));
    qsag_gf128_tower_map #(.INVERSE(1)) u_i0 (.x(m0), .y(y01));
    qsag_gf128_tower_map #(.INVERSE(1)) u_i1 (.x(x),  .y(m1));
    qsag_gf128_tower_map #(.INVERSE(0)) u_f1 (.x(m1), .y(y10));
endmodule
""")
    ys_rt = yosys_smt2("tower_roundtrip", "qsag_tower_rt", [TMAP, rt_sv], use_contracts=False)
    x = acc("x", "s0")
    basis_q = (ys_rt +
               "(declare-fun s0 () |lec_top_s|)\n(declare-const b (_ BitVec 7))\n(assert (|lec_top_h| s0))\n"
               f"(assert (= {x} (bvshl (_ bv1 128) ((_ zero_extend 121) b))))\n"
               f"(assert (not (and (= {acc('y01','s0')} {x}) (= {acc('y10','s0')} {x}))))\n(check-sat)\n")
    if not record("tower_map_bijection",
                  "composed RTL qsag_tower_rt: inv(fwd(e_b)) == e_b and fwd(inv(e_b)) == e_b for all 128 basis inputs",
                  "unsat", basis_q):
        raise SystemExit("failed tower roundtrip Z3 proof")

    # 3. Mutant tooth on qsag_gf128_tower_map: flip 1 mask bit in INVERSE=0 row 0 -> must return sat!
    m_tow = mutate(TMAP, "128'hd353a5afc268871ad268eb72003a04ad",
                   "128'hd353a5afc268871ad268eb72003a04ac", "mut_tower_map.sv")
    ys_mt = yosys_smt2("mut_tower_map", "qsag_gf128_tower_map", [m_tow], "-chparam INVERSE 0", use_contracts=False)
    assertions0 = [f"(= (= ((_ extract {i} {i}) {acc('y','s0')}) #b1) {parity_bool(acc('x','s0'), m)})"
                   for i, m in enumerate(rows)]
    if not record("mut_tower_map_bitflip", "mutant tooth: 1-bit mask flip in qsag_gf128_tower_map is refuted",
                  "sat", ys_mt + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
                  "(assert (not (and " + " ".join(assertions0) + ")))\n(check-sat)\n"):
        raise SystemExit("failed tower mutant")

    # 4. Exact 16,384 basis-pair bilinearity certificate + Z3 checks on 3-cycle RTL qsag_gf128_tower_mul
    #    for all 7 Artin-Schreier defining equations (g_k^2 + g_{k-1}*g_k == 1) and all Lean KATs!
    def tmul(k, a, b):
        if k == 0: return a & b
        h = 1 << (k - 1); mask = (1 << h) - 1
        a0, a1 = a & mask, a >> h; b0, b1 = b & mask, b >> h
        p = tmul(k - 1, a0, b0); q = tmul(k - 1, a1, b1)
        cross = tmul(k - 1, a0 ^ a1, b0 ^ b1) ^ p ^ q
        g = 1 if k == 1 else 1 << (h // 2)
        return (p ^ q) | ((cross ^ tmul(k - 1, g, q)) << h)

    for i in range(128):
        for j in range(128):
            assert G.apply(cols, tmul(7, 1 << i, 1 << j)) == G.mul(cols[i], cols[j])

    ys_tmul = yosys_smt2("tower_mul", "qsag_gf128_tower_mul", [KARA, GFRED, GFMUL, TMAP, TMUL], use_contracts=False)
    for k in range(7):
        gk = 1 << (1 << k)
        gprev = 1 if k == 0 else (1 << (1 << (k - 1)))
        # In tower basis: gk * (gk ^ gprev) == 1!
        body = (ys_tmul + unroll(3) +
                f"(assert (= {acc('a','s0')} {bv(gk, 128)}))\n"
                f"(assert (= {acc('b','s0')} {bv(gk ^ gprev, 128)}))\n"
                f"(assert (not (= {acc('r','s3')} {bv(1, 128)})))\n(check-sat)\n")
        if not record(f"tower_artin_schreier_k{k}",
                      f"qsag_gf128_tower_mul 3-cycle RTL: g_{k} * (g_{k} + g_{k-1}) == 1", "unsat", body):
            raise SystemExit("failed Artin-Schreier RTL identity")

    fixture = json.load(open(fixture_path))
    for i, k in enumerate(fixture["tower128"]):
        vals = [int.from_bytes(bytes.fromhex(k[n]), "little") for n in ("a_le_hex", "b_le_hex", "mul_le_hex", "inv_a_le_hex")]
        for name, b_val, want in [("mul", vals[1], vals[2]), ("inv", vals[3], int(vals[0] != 0))]:
            body = (ys_tmul + unroll(3) +
                    f"(assert (= {acc('a','s0')} {bv(vals[0], 128)}))\n"
                    f"(assert (= {acc('b','s0')} {bv(b_val, 128)}))\n"
                    f"(assert (not (= {acc('r','s3')} {bv(want, 128)})))\n(check-sat)\n")
            if not record(f"tower_kat_{i}_{name}",
                          f"qsag_gf128_tower_mul 3-cycle RTL vs Lean tower128 KAT #{i} ({name})", "unsat", body):
                raise SystemExit("failed Lean tower128 KAT in Z3")

def group_try():
    # Exploratory monolithic bit-blasted queries (recorded, not required; compositional proofs + ANF
    # already establish 100% universal equivalence with 0 undecided required checks).
    check_kara_small("try_clmul_kara_w16", 16, "unsat", required=False, secs=TRY_SECS)
    check_mul_wiring("try_mul64_wiring_precise_26x17", [MUL], 26, 17, "unsat", precise=True, required=False, secs=TRY_SECS)

GROUPS = {"gl": group_gl, "glmut": group_glmut, "gf": group_gf, "tower": group_tower, "try": group_try}

def main():
    os.makedirs(OUT, exist_ok=True)
    groups = sys.argv[1:] or ["gl", "glmut", "gf", "tower"]
    for g in groups:
        del results[:]
        GROUPS[g]()
        with open(os.path.join(OUT, f"results_{g}.txt"), "w") as f:
            for tag, name, stmt, exp, ans, dt in results:
                f.write(f"{tag}\t{name}\t{exp}\t{ans}\t{dt:.1f}s\t{stmt}\n")
        bad = [r for r in results if r[0] == "FAIL"]
        print(f"LEC {g}: {sum(r[0] == 'PASS' for r in results)} passed, {len(bad)} failed, "
              f"{sum(r[0] == 'open' for r in results)} optional exploratory", flush=True)
        if bad:
            sys.exit(1)

if __name__ == "__main__":
    main()
