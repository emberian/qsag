#!/usr/bin/env python3
"""Compositional formal verification of the QSAG-NI arithmetic & isomorphism RTL.

Yosys reads the SystemVerilog and writes its transition relation with `write_smt2`
(frontend, `proc`, `flatten` only: no optimisation pass); this script builds the
universal SMT-LIB2 specifications, intermediate cut-lemmas, glue miters, and mutant
teeth, and discharges every obligation with Z3 4.15.5 and Bitwuzla.

Every proof check MUST return `unsat` and every planted-fault mutant check MUST
return `sat`, with 0 failures and 0 `open / timeout` rows.
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
BITWUZLA = shutil.which("bitwuzla") or (
    "/home/build/qsag-ni-asic/tools/oss-cad-suite/bin/bitwuzla"
    if os.path.exists("/home/build/qsag-ni-asic/tools/oss-cad-suite/bin/bitwuzla") else None
)
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
    if use_contracts and CONTRACTS_READY and top in (
        "qsag_mul64_dsp", "qsag_gl64_dsp_mul", "qsag_gl64_reduce",
        "qsag_ext4_mac", "qsag_ext5_stage0", "qsag_ext5_stage4",
    ):
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

def flatten_ys_smt2(ys_txt, mod, steps):
    """Eliminate uninterpreted state sort |<mod>_s| across `steps` cycles so Bitwuzla solves
    sequential QF_BV / QF_UFBV pipelines directly in < 0.3s without Ackermannization."""
    import re
    out_decls = {t: [] for t in range(steps + 1)}
    t_body = None
    lines = [ln.split(";")[0].rstrip() for ln in ys_txt.splitlines() if ln.split(";")[0].strip()]
    i = 0
    header = []
    while i < len(lines):
        ln = lines[i]
        if ln.startswith(f"(declare-sort |{mod}_s|"):
            i += 1
            continue
        m_dec = re.match(rf"^\(declare-fun (\|{re.escape(mod)}[^|]*\|) \(\|{re.escape(mod)}_s\|\) (.+)\)$", ln)
        if m_dec:
            fn, ty = m_dec.group(1), m_dec.group(2)
            for t in range(steps + 1):
                out_decls[t].append(f"(declare-const {fn[:-1]}@s{t}| {ty})")
            i += 1
            continue
        if ln.startswith(f"(define-fun |{mod}_t| "):
            blk = [ln]
            depth = ln.count("(") - ln.count(")")
            i += 1
            while depth > 0 and i < len(lines):
                blk.append(lines[i])
                depth += lines[i].count("(") - lines[i].count(")")
                i += 1
            t_body = "\n".join(blk)
            continue
        m_def = re.match(rf"^\(define-fun (\|{re.escape(mod)}[^|]*\|) \(\(state \|{re.escape(mod)}_s\|\)\)", ln)
        if m_def:
            fn = m_def.group(1)
            blk = [ln]
            depth = ln.count("(") - ln.count(")")
            i += 1
            while depth > 0 and i < len(lines):
                blk.append(lines[i])
                depth += lines[i].count("(") - lines[i].count(")")
                i += 1
            full = "\n".join(blk)
            for t in range(steps + 1):
                out_decls[t].append(("DEF", fn, t, full))
            continue
        header.append(ln)
        i += 1

    pat_state = re.compile(rf"\((\|{re.escape(mod)}[^|]*\|) state\)")
    pat_next = re.compile(rf"\((\|{re.escape(mod)}[^|]*\|) next_state\)")
    chunks = ["\n".join(header)]
    for t in range(steps + 1):
        for item in out_decls[t]:
            if isinstance(item, str):
                chunks.append(item)
            else:
                _, fn, tt, full = item
                s = full.replace(f"(define-fun {fn} ((state |{mod}_s|))", f"(define-fun {fn[:-1]}@s{tt}| ()", 1)
                s = pat_state.sub(lambda m: f"{m.group(1)[:-1]}@s{tt}|", s)
                chunks.append(s)
        chunks.append(f"(assert |{mod}_h@s{t}|)")
    if t_body and steps > 0:
        inner = t_body.split("Bool", 1)[1].rsplit(")", 1)[0]
        for t in range(steps):
            s = pat_state.sub(lambda m: f"{m.group(1)[:-1]}@s{t}|", inner)
            s = pat_next.sub(lambda m: f"{m.group(1)[:-1]}@s{t+1}|", s)
            chunks.append(f"(assert {s})")
    return "\n".join(chunks) + "\n"

def flat_acc(port, step):
    return f"|lec_top_n {port}@s{step}|"

def solve(name, text, secs, prefer_bitwuzla=True):
    path = os.path.join(OUT, name + ".smt2")
    is_bv_only = (" Int)" not in text) and ("(mod " not in text)
    if prefer_bitwuzla and is_bv_only and BITWUZLA:
        bw_text = (text if "(set-logic" in text else "(set-logic QF_UFBV)\n" + text)
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
B33 = ((2**32 - 1) + (2**33 - 1)) << 16  # 0x0002_FFFF_FFFE_0000

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
    KP = 2**64 + 2**32  # M128 + C1 = P * (2^64 + 2^32)

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
    for k, acc_e in enumerate(accs_r):
        if not record(f"ext4_karatsuba_range_limb{k}",
                      f"9-mul Tower Karatsuba limb {k}: 0 < acc < 2^136 for all 2^128 products and 64-bit c",
                      "unsat", r_decl + r_rng + f"(assert (not (and (> {acc_e} 0) (< {acc_e} {2**136}))))\n(check-sat)\n"):
            raise SystemExit("failed Ext4 Karatsuba range proof")

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
MUL33 = os.path.join(ROOT, "rtl/qsag_mul33x32_dsp.sv")
MUL   = os.path.join(ROOT, "rtl/qsag_mul64_dsp.sv")
GLM   = os.path.join(ROOT, "rtl/qsag_gl64_dsp_mul.sv")
SBOX  = os.path.join(ROOT, "rtl/qsag_p2_sbox7.sv")
EXT4  = os.path.join(ROOT, "rtl/qsag_ext4_mac.sv")
EXT5  = os.path.join(ROOT, "rtl/qsag_ext5_mac.sv")
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

def check_csa_inductive(w, target_n):
    """Inductive Z3 proof of recursive `qsag_csa_reduce2` up to N = target_n."""
    chain = []
    cur = target_n
    while cur > 3:
        chain.append(cur)
        cur = 2 * (cur // 3) + (cur % 3)
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
        g_cnt = n // 3
        r_cnt = n % 3
        m = 2 * g_cnt + r_cnt
        step_sv = os.path.join(OUT, f"csa_step_{w}_{n}.sv")
        step_txt = csa_src.replace("module qsag_csa_reduce2", "module qsag_csa_step", 1)
        step_txt = step_txt.replace(
            "input  logic [N*W-1:0] x,",
            f"input logic [N*W-1:0] x, input logic [{w-1}:0] free_s, output logic [{m*w-1}:0] dbg_nxt,",
            1,
        )
        step_txt = step_txt.replace(
            "qsag_csa_reduce2 #(.W(W), .N(M)) u_rec (.x(nxt), .s(s), .c(c));",
            "qsag_csa_child_contract #(.W(W), .N(M)) u_rec (.x(nxt), .free_s(free_s), .s(s), .c(c));\n"
            "        assign dbg_nxt = nxt;",
        )
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
        x_sl = [f"((_ extract {(i+1)*w-1} {i*w}) {acc('x', 's0')})" for i in range(n)]
        n_sl = [f"((_ extract {(j+1)*w-1} {j*w}) {acc('dbg_nxt', 's0')})" for j in range(m)]
        rtl_clauses = [
            f"(= (bvadd {n_sl[2*i]} {n_sl[2*i+1]}) (bvadd (bvadd {x_sl[3*i]} {x_sl[3*i+1]}) {x_sl[3*i+2]}))"
            for i in range(g_cnt)
        ] + [
            f"(= {n_sl[2*g_cnt + r]} {x_sl[3*g_cnt + r]})"
            for r in range(r_cnt)
        ]
        nxt_tot = bv(0, w)
        for j in range(m):
            nxt_tot = f"(bvadd {nxt_tot} {n_sl[j]})"
        rtl_clauses.append(f"(= (bvadd {acc('s','s0')} {acc('c','s0')}) {nxt_tot})")
        body_n = ys_step + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
        if not record(f"contract_csa2_{w}_n{n}_step_rtl",
                      f"qsag_csa_reduce2 W={w} N={n} RTL triplet + child-sum invariants (M={m})",
                      "unsat", body_n + "(assert (not (and " + " ".join(rtl_clauses) + ")))\n(check-sat)\n",
                      prefer_bitwuzla=True):
            raise SystemExit(f"failed CSA RTL triplet step N={n}")

        join_decl = (
            "(set-logic QF_BV)\n"
            + "".join(f"(declare-const x{i} (_ BitVec {w}))\n" for i in range(n))
            + "".join(f"(declare-const y{j} (_ BitVec {w}))\n" for j in range(m))
            + f"(declare-const sv (_ BitVec {w}))\n(declare-const cv (_ BitVec {w}))\n"
        )
        join_hyps = "".join(
            f"(assert (= (bvadd y{2*i} y{2*i+1}) (bvadd (bvadd x{3*i} x{3*i+1}) x{3*i+2})))\n"
            for i in range(g_cnt)
        ) + "".join(
            f"(assert (= y{2*g_cnt + r} x{3*g_cnt + r}))\n"
            for r in range(r_cnt)
        )
        y_tot = bv(0, w)
        for j in range(m):
            y_tot = f"(bvadd {y_tot} y{j})"
        join_hyps += f"(assert (= (bvadd sv cv) {y_tot}))\n"
        left_x = bv(0, w)
        for i in range(n):
            left_x = f"(bvadd {left_x} x{i})"
        terms = [f"x{i}" for i in range(n)]
        while len(terms) > 1:
            terms = [f"(bvadd {terms[k]} {terms[k+1]})" if k + 1 < len(terms) else terms[k]
                     for k in range(0, len(terms), 2)]
        tree_x = terms[0]
        if not record(f"contract_csa2_{w}_n{n}_step",
                      f"qsag_csa_reduce2 W={w} N={n} inductive step (from proved M={m}): s + c == sum x_i for all 2^{n*w} inputs",
                      "unsat", join_decl + join_hyps + f"(assert (not (and (= (bvadd sv cv) {left_x}) (= (bvadd sv cv) {tree_x}))))\n(check-sat)\n",
                      prefer_bitwuzla=False):
            raise SystemExit(f"failed CSA inductive step N={n}")

def check_adder_contracts():
    """Discharge every CSA compressor and split-carry helper instance used across the 9-DSP
    multiplier, Goldilocks reducer, Ext4 MAC, and Ext5 MAC BEFORE replacing their bodies."""
    global CONTRACTS_READY
    CONTRACTS_READY = False

    check_csa_inductive(66, 6)
    check_csa_inductive(67, 5)
    check_csa_inductive(68, 4)
    check_csa_inductive(72, 11)
    check_csa_inductive(96, 5)
    check_csa_inductive(128, 12)
    check_csa_inductive(136, 15)

    for w, chk in [(33, 17), (33, 33), (65, 16), (65, 34), (66, 16), (66, 24), (66, 34), (66, 66),
                   (67, 16), (67, 24), (67, 34), (68, 68), (72, 72), (96, 32), (96, 48),
                   (128, 16), (128, 24), (128, 32), (136, 16), (136, 24), (136, 46)]:
        ys = yosys_smt2(f"contract_split_{w}_{chk}", "qsag_add_split", [], f"-chparam W {w} -chparam CHUNK {chk}", use_contracts=False)
        spec = f"(bvadd {acc('a', 's0')} {acc('b', 's0')})"
        body = ys + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
        if not record(f"contract_split_{w}_c{chk}", f"qsag_add_split W={w} CHUNK={chk}: y == a + b (mod 2^{w}) for all 2^{2*w} inputs",
                      "unsat", body + f"(assert (not (= {acc('y', 's0')} {spec})))\n(check-sat)\n"):
            raise SystemExit("refusing unproved split-adder contract")

    scsa_src = open(SCSA).read().replace("(* flatten *)", "")
    for w, n, chk in [(66, 3, 16), (66, 3, 66), (66, 4, 16), (66, 5, 66), (66, 6, 16), (66, 6, 24), (67, 5, 16),
                      (68, 3, 68), (68, 4, 68), (72, 5, 72), (72, 7, 72), (72, 8, 72), (72, 11, 72),
                      (96, 5, 48), (128, 12, 16), (128, 12, 24), (128, 12, 32),
                      (136, 9, 24), (136, 10, 16), (136, 11, 24), (136, 12, 16), (136, 13, 16),
                      (136, 14, 24), (136, 15, 16), (136, 15, 24)]:
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

def check_mul33x32_and_mul64_9dsp():
    """Compositional bit-precise proof of the 9-DSP unsigned two-level Karatsuba multiplier:
      1) Bit-precise 2-stage DSP cells (16x16u, 17x16u, 18x17u) over all 2^32, 2^33, 2^35 inputs;
      2) Unabstracted `qsag_mul33x32_dsp` RTL (actual 3:2 CSA gates, no contract substitution):
         proves 68-bit non-wrapping `zext(s) + zext(c) == K33(t0, t1, ts)` + QF_NIA identity
         `K33(a0*b0, a1*b1, (a0+a1)*(b0+b1)) == a*b + B33 < 2^66` for all 2^65 inputs;
      3) 3-cycle `qsag_mul64_dsp` RTL over ANY carry-save pairs `(s_i, c_i)` satisfying
         `int(s_i) + int(c_i) == P_i + B33`: proves `p@s3 == K64(P0, P2, PS, sa, cb)` + QF_NIA
         identity `K64(a0*b0, a1*b1, sa*beta, sa, cb) == a*b` for all 2^128 inputs (AW=26/16);
      4) End-to-end temporal composition of `qsag_gl64_dsp_mul` (`REG_OUT=1` and `REG_OUT=0`) ->
         unique canonical residue `r == (a*b) mod p` over all 2^128 inputs."""
    # 1. Bit-precise proofs on the three unsigned DSP shapes (16x16u, 17x16u, 18x17u)
    for wa, wb in [(16, 16), (17, 16), (18, 17)]:
        tw = wa + wb
        cell_sv = os.path.join(OUT, f"dsp_cell_{wa}x{wb}.sv")
        open(cell_sv, "w").write(f"""
module qsag_dsp_u_cell (input logic clk, input logic [{wa-1}:0] a, input logic [{wb-1}:0] b, output logic [{tw-1}:0] tq);
    logic [{wa-1}:0] aq; logic [{wb-1}:0] bq;
    always_ff @(posedge clk) begin aq <= a; bq <= b; tq <= {tw}'(aq) * {tw}'(bq); end
endmodule
""")
        ys = yosys_smt2(f"dsp_cell_{wa}x{wb}", "qsag_dsp_u_cell", [cell_sv], use_contracts=False)
        exact = f"(bvmul {zext(acc('a','s0'), wa, tw)} {zext(acc('b','s0'), wb, tw)})"
        if not record(f"dsp_tile_exact_{wa}x{wb}u",
                      f"bit-precise 2-stage unsigned DSP cell ({wa}x{wb}u, fits MULT18X18D & DSP48E2): tq == a*b for all 2^{tw} inputs",
                      "unsat", ys + unroll(2) + f"(assert (not (= {acc('tq','s2')} {exact})))\n(check-sat)\n"):
            raise SystemExit("failed DSP cell proof")

    # 2a. Unabstracted `qsag_mul33x32_dsp` CSA & row-wiring RTL (`use_contracts=False`, real 4->2 CSA gates,
    #     68-bit zero-ext -> proves zero bit-66 wrap!) over the proved 2-stage DSP tile bounds:
    def make_mul33_sv(src_path, dst_name):
        txt = open(src_path).read()
        txt = txt.replace("32'(a0_q) * 32'(b0_q)", "dsp36_p0[31:0]")
        txt = txt.replace("33'(a1_q) * 33'(b1_q)", "dsp36_p1[32:0]")
        txt = txt.replace("35'(as_q) * 35'(bs_q)", "dsp36_ps[34:0]")
        txt = txt.replace(
            "always_ff @(posedge clk) begin",
            "wire [35:0] dsp36_p0 = 36'(a0_q) * 36'(b0_q);\n"
            "    wire [35:0] dsp36_p1 = 36'(a1_q) * 36'(b1_q);\n"
            "    wire [35:0] dsp36_ps = 36'(as_q) * 36'(bs_q);\n"
            "    always_ff @(posedge clk) begin"
        )
        out_p = os.path.join(OUT, dst_name)
        open(out_p, "w").write(txt)
        return out_p

    m33_sv = make_mul33_sv(MUL33, "mul33_rel.sv")
    ys33 = yosys_smt2("mul33x32_rtl", "qsag_mul33x32_dsp", [m33_sv], use_contracts=False)
    assert ys33.count("(bvmul ") == 3, ys33.count("(bvmul ")
    ys33_abs = "(declare-fun qdsp36 ((_ BitVec 36) (_ BitVec 36)) (_ BitVec 36))\n" + ys33.replace("(bvmul ", "(qdsp36 ")
    a33, b32 = acc("a", "s0"), acc("b", "s0")
    a0_36 = zext(f"((_ extract 15 0) {a33})", 16, 36)
    a1_36 = zext(f"((_ extract 32 16) {a33})", 17, 36)
    b0_36 = zext(f"((_ extract 15 0) {b32})", 16, 36)
    b1_36 = zext(f"((_ extract 31 16) {b32})", 16, 36)
    as_36 = zext(f"(bvadd {zext(f'((_ extract 15 0) {a33})', 16, 18)} {zext(f'((_ extract 32 16) {a33})', 17, 18)})", 18, 36)
    bs_36 = zext(f"(bvadd {zext(f'((_ extract 15 0) {b32})', 16, 17)} {zext(f'((_ extract 31 16) {b32})', 16, 17)})", 17, 36)
    t0_36 = f"(qdsp36 {a0_36} {b0_36})"
    t1_36 = f"(qdsp36 {a1_36} {b1_36})"
    ts_36 = f"(qdsp36 {as_36} {bs_36})"
    hyps33 = (f"(assert (bvule {t0_36} {bv((2**16 - 1)**2, 36)}))\n"
              f"(assert (bvule {t1_36} {bv((2**17 - 1) * (2**16 - 1), 36)}))\n"
              f"(assert (bvule {ts_36} {bv(((2**16 - 1) + (2**17 - 1)) * 2 * (2**16 - 1), 36)}))\n")
    t0 = zext(t0_36, 36, 68)
    t1 = zext(t1_36, 36, 68)
    ts = zext(ts_36, 36, 68)
    k33 = (f"(bvadd {t0} (bvshl {t1} {bv(32, 68)}) "
           f"(bvshl (bvsub (bvsub (bvadd {ts} {bv((2**32 - 1) + (2**33 - 1), 68)}) {t0}) {t1}) {bv(16, 68)}))")
    sc68 = f"(bvadd {zext(acc('s','s2'), 66, 68)} {zext(acc('c','s2'), 66, 68)})"
    if not record("mul33x32_dsp_rtl_csa_exact",
                  "unabstracted 3-DSP qsag_mul33x32_dsp RTL (actual CSA gates): zext68(s)+zext68(c) == K33(t0,t1,ts) with zero bit-66 wrap",
                  "unsat", ys33_abs + unroll(2) + hyps33 + f"(assert (not (= {sc68} {k33})))\n(check-sat)\n",
                  prefer_bitwuzla=True):
        raise SystemExit("failed mul33x32 RTL CSA proof")

    # 2b. QF_NIA integer proof that K33(a0*b0, a1*b1, (a0+a1)*(b0+b1)) == a*b + B33 < 2^66 for all 2^65 inputs
    nia33 = f"""(declare-const a0 Int) (declare-const a1 Int) (declare-const b0 Int) (declare-const b1 Int)
(assert (and (<= 0 a0) (< a0 {2**16}) (<= 0 a1) (< a1 {2**17}) (<= 0 b0) (< b0 {2**16}) (<= 0 b1) (< b1 {2**16})))
(define-fun a () Int (+ a0 (* {2**16} a1)))
(define-fun b () Int (+ b0 (* {2**16} b1)))
(define-fun t0 () Int (* a0 b0))
(define-fun t1 () Int (* a1 b1))
(define-fun ts () Int (* (+ a0 a1) (+ b0 b1)))
(define-fun k33 () Int (+ t0 (* {2**32} t1) (* {2**16} (- (+ ts {(2**32 - 1) + (2**33 - 1)}) t0 t1))))
(assert (not (and (= k33 (+ (* a b) {B33})) (< k33 {2**66}))))
(check-sat)
"""
    if not record("mul33x32_dsp_algebra_exact",
                  "QF_NIA: for all a in [0,2^33) and b in [0,2^32), K33(t0,t1,ts) == a*b + B33 < 2^66",
                  "unsat", nia33):
        raise SystemExit("failed mul33x32 algebra proof")

    # 3. 3-cycle `qsag_mul64_dsp` RTL over ANY carry-save pairs `(s_i, c_i)` satisfying `zext68(s_i)+zext68(c_i) == P_i + B33`
    mul_body = open(MUL).read()
    idx_m64 = mul_body.index("module qsag_mul64_dsp")
    m64_only = mul_body[idx_m64:]
    m64_rel = m64_only.replace(
        "input  logic [63:0]  b,",
        "input  logic [63:0]  b,\n"
        "    input  logic [65:0]  fs0, fc0, fs2, fc2, fss, fsc,\n"
        "    output logic [66:0]  pr0, pr2, prs,"
    )
    m64_rel = m64_rel.replace(
        "qsag_mul33x32_dsp u_p0 (.clk(clk), .a({1'b0, a0}), .b(b0),   .s(p0_s), .c(p0_c));",
        "qsag_mul33x32_rel u_p0 (.clk(clk), .a({1'b0, a0}), .b(b0),   .fs(fs0), .fc(fc0), .s(p0_s), .c(p0_c), .prod(pr0));"
    ).replace(
        "qsag_mul33x32_dsp u_p2 (.clk(clk), .a({1'b0, a1}), .b(b1),   .s(p2_s), .c(p2_c));",
        "qsag_mul33x32_rel u_p2 (.clk(clk), .a({1'b0, a1}), .b(b1),   .fs(fs2), .fc(fc2), .s(p2_s), .c(p2_c), .prod(pr2));"
    ).replace(
        "qsag_mul33x32_dsp u_ps (.clk(clk), .a(sa),         .b(beta), .s(ps_s), .c(ps_c));",
        "qsag_mul33x32_rel u_ps (.clk(clk), .a(sa),         .b(beta), .fs(fss), .fc(fsc), .s(ps_s), .c(ps_c), .prod(prs));"
    )
    m64_rel += """
module qsag_mul33x32_rel (
    input logic clk, input logic [32:0] a, input logic [31:0] b,
    input logic [65:0] fs, input logic [65:0] fc,
    output logic [65:0] s, output logic [65:0] c, output logic [66:0] prod
);
    logic [32:0] aq1, aq2;
    logic [31:0] bq1, bq2;
    always_ff @(posedge clk) begin aq1 <= a; aq2 <= aq1; bq1 <= b; bq2 <= bq1; end
    assign prod = 67'(aq2) * 67'(bq2);
    assign s = fs;
    assign c = fc;
endmodule
"""
    m64_sv = os.path.join(OUT, "mul64_rel.sv")
    open(m64_sv, "w").write(m64_rel)

    c_kara_val = ((B33 << 32) - B33 - (B33 << 64) + 4) & ((1 << 128) - 1)

    def mul64_wiring_rtl_query(ys_txt):
        assert ys_txt.count("(bvmul ") == 3, ys_txt.count("(bvmul ")
        ys_abs = "(declare-fun qmul33 ((_ BitVec 67) (_ BitVec 67)) (_ BitVec 67))\n" + ys_txt.replace("(bvmul ", "(qmul33 ")
        a64, b64 = acc("a", "s0"), acc("b", "s0")
        a0_67 = zext(f"((_ extract 31 0) {a64})", 32, 67)
        a1_67 = zext(f"((_ extract 63 32) {a64})", 32, 67)
        b0_67 = zext(f"((_ extract 31 0) {b64})", 32, 67)
        b1_67 = zext(f"((_ extract 63 32) {b64})", 32, 67)
        sa_33 = f"(bvadd {zext(f'((_ extract 31 0) {a64})', 32, 33)} {zext(f'((_ extract 63 32) {a64})', 32, 33)})"
        sb_33 = f"(bvadd {zext(f'((_ extract 31 0) {b64})', 32, 33)} {zext(f'((_ extract 63 32) {b64})', 32, 33)})"
        sa_67 = zext(sa_33, 33, 67)
        beta_67 = zext(f"((_ extract 31 0) {sb_33})", 32, 67)
        cb_1 = f"((_ extract 32 32) {sb_33})"
        p0_67 = f"(qmul33 {a0_67} {b0_67})"
        p2_67 = f"(qmul33 {a1_67} {b1_67})"
        ps_67 = f"(qmul33 {sa_67} {beta_67})"
        hyps = (
            f"(assert (bvule {p0_67} {bv((2**32 - 1)**2, 67)}))\n"
            f"(assert (bvule {p2_67} {bv((2**32 - 1)**2, 67)}))\n"
            f"(assert (bvule {ps_67} {bv((2**33 - 1) * (2**32 - 1), 67)}))\n"
            f"(assert (= (bvadd {zext(acc('p0_s','s2'),66,68)} {zext(acc('p0_c','s2'),66,68)}) (bvadd {zext(acc('pr0','s2'),67,68)} {bv(B33,68)})))\n"
            f"(assert (= (bvadd {zext(acc('p2_s','s2'),66,68)} {zext(acc('p2_c','s2'),66,68)}) (bvadd {zext(acc('pr2','s2'),67,68)} {bv(B33,68)})))\n"
            f"(assert (= (bvadd {zext(acc('ps_s','s2'),66,68)} {zext(acc('ps_c','s2'),66,68)}) (bvadd {zext(acc('prs','s2'),67,68)} {bv(B33,68)})))\n"
        )
        p0_128, p2_128, ps_128 = zext(p0_67, 67, 128), zext(p2_67, 67, 128), zext(ps_67, 67, 128)
        cb_term = f"(ite (= {cb_1} #b1) (bvshl {zext(sa_33, 33, 128)} {bv(64, 128)}) {bv(0, 128)})"
        orows = acc("outer_rows", "s2")
        r_sl = [f"((_ extract {128*k+127} {128*k}) {orows})" for k in range(12)]
        r_tot = bv(0, 128)
        for k in range(12):
            r_tot = f"(bvadd {r_tot} {r_sl[k]})"
        clauses = [
            f"(= (bvadd {r_sl[0]} {r_sl[1]}) (bvadd {p0_128} {bv(B33, 128)}))",
            f"(= (bvadd {r_sl[2]} {r_sl[3]}) (bvshl (bvadd {p2_128} {bv(B33, 128)}) {bv(64, 128)}))",
            f"(= (bvadd {r_sl[4]} {r_sl[5]}) (bvshl (bvadd {ps_128} {bv(B33, 128)}) {bv(32, 128)}))",
            f"(= {r_sl[6]} {cb_term})",
            f"(= (bvadd {r_sl[7]} {r_sl[8]}) (bvsub {bv(2**128 - 2, 128)} (bvshl (bvadd {p0_128} {bv(B33, 128)}) {bv(32, 128)})))",
            f"(= (bvadd {r_sl[9]} {r_sl[10]}) (bvsub {bv(2**128 - 2, 128)} (bvshl (bvadd {p2_128} {bv(B33, 128)}) {bv(32, 128)})))",
            f"(= {r_sl[11]} {bv(c_kara_val, 128)})",
            f"(= {acc('p', 's3')} {r_tot})",
        ]
        return ys_abs + unroll(3) + hyps + "(assert (not (and " + " ".join(clauses) + ")))\n(check-sat)\n"

    def mul64_direct_k64_query(ys_txt):
        assert ys_txt.count("(bvmul ") == 3, ys_txt.count("(bvmul ")
        ys_abs = "(declare-fun qmul33 ((_ BitVec 67) (_ BitVec 67)) (_ BitVec 67))\n" + ys_txt.replace("(bvmul ", "(qmul33 ")
        a64, b64 = flat_acc("a", 0), flat_acc("b", 0)
        a0_67 = zext(f"((_ extract 31 0) {a64})", 32, 67)
        a1_67 = zext(f"((_ extract 63 32) {a64})", 32, 67)
        b0_67 = zext(f"((_ extract 31 0) {b64})", 32, 67)
        b1_67 = zext(f"((_ extract 63 32) {b64})", 32, 67)
        sa_33 = f"(bvadd {zext(f'((_ extract 31 0) {a64})', 32, 33)} {zext(f'((_ extract 63 32) {a64})', 32, 33)})"
        sb_33 = f"(bvadd {zext(f'((_ extract 31 0) {b64})', 32, 33)} {zext(f'((_ extract 63 32) {b64})', 32, 33)})"
        sa_67 = zext(sa_33, 33, 67)
        beta_67 = zext(f"((_ extract 31 0) {sb_33})", 32, 67)
        cb_1 = f"((_ extract 32 32) {sb_33})"
        p0_67 = f"(qmul33 {a0_67} {b0_67})"
        p2_67 = f"(qmul33 {a1_67} {b1_67})"
        ps_67 = f"(qmul33 {sa_67} {beta_67})"
        hyps = (
            f"(assert (bvule {p0_67} {bv((2**32 - 1)**2, 67)}))\n"
            f"(assert (bvule {p2_67} {bv((2**32 - 1)**2, 67)}))\n"
            f"(assert (bvule {ps_67} {bv((2**33 - 1) * (2**32 - 1), 67)}))\n"
            f"(assert (= (bvadd {zext(flat_acc('p0_s', 2), 66, 68)} {zext(flat_acc('p0_c', 2), 66, 68)}) (bvadd {zext(flat_acc('pr0', 2), 67, 68)} {bv(B33, 68)})))\n"
            f"(assert (= (bvadd {zext(flat_acc('p2_s', 2), 66, 68)} {zext(flat_acc('p2_c', 2), 66, 68)}) (bvadd {zext(flat_acc('pr2', 2), 67, 68)} {bv(B33, 68)})))\n"
            f"(assert (= (bvadd {zext(flat_acc('ps_s', 2), 66, 68)} {zext(flat_acc('ps_c', 2), 66, 68)}) (bvadd {zext(flat_acc('prs', 2), 67, 68)} {bv(B33, 68)})))\n"
        )
        p0w, p2w, psw = zext(p0_67, 67, 128), zext(p2_67, 67, 128), zext(ps_67, 67, 128)
        cbt = f"(ite (= {cb_1} #b1) (bvshl {zext(sa_33, 33, 128)} {bv(64, 128)}) {bv(0, 128)})"
        k64 = f"(bvadd {p0w} (bvadd (bvshl {p2w} {bv(64, 128)}) (bvadd {cbt} (bvshl (bvsub (bvsub {psw} {p0w}) {p2w}) {bv(32, 128)}))))"
        return flatten_ys_smt2(ys_abs, "lec_top", 3) + hyps + f"(assert (not (= {flat_acc('p', 3)} {k64})))\n(check-sat)\n"

    ys64_26 = yosys_smt2("mul64_rel_26x17", "qsag_mul64_dsp", [m64_sv], "-chparam AW 26 -chparam BW 17")
    if not record("mul64_dsp_wiring_rtl_26x17",
                  "9-DSP qsag_mul64_dsp AW=26 BW=17 RTL pairwise CSA row & sum invariants over all 2^128 inputs",
                  "unsat", mul64_wiring_rtl_query(ys64_26), prefer_bitwuzla=True):
        raise SystemExit("failed mul64_dsp RTL row proof 26x17")

    ys64_16 = yosys_smt2("mul64_rel_16x16", "qsag_mul64_dsp", [m64_sv], "-chparam AW 16 -chparam BW 16")
    if not record("mul64_dsp_wiring_rtl_16x16",
                  "9-DSP qsag_mul64_dsp AW=16 BW=16 RTL 3-cycle outer Karatsuba equivalence p@s3 == K64 over all 2^128 inputs",
                  "unsat", mul64_direct_k64_query(ys64_16), prefer_bitwuzla=True):
        raise SystemExit("failed mul64_dsp RTL K64 proof 16x16")

    # Modus Ponens QF_BV join from the 8 proved row invariants to `p@s3 == K64(P0,P2,PS,sa,cb)`:
    rtot_j = bv(0, 128)
    for k in range(12):
        rtot_j = f"(bvadd {rtot_j} r{k})"
    assoc64 = (
        "(set-logic QF_BV)\n"
        + "".join(f"(declare-const r{k} (_ BitVec 128))\n" for k in range(12))
        + "(declare-const g01 (_ BitVec 128)) (declare-const g23 (_ BitVec 128)) (declare-const g45 (_ BitVec 128))\n"
        + "(declare-const g78 (_ BitVec 128)) (declare-const g9a (_ BitVec 128)) (declare-const p_out (_ BitVec 128))\n"
        + "(assert (= g01 (bvadd r0 r1))) (assert (= g23 (bvadd r2 r3))) (assert (= g45 (bvadd r4 r5)))\n"
        + "(assert (= g78 (bvadd r7 r8))) (assert (= g9a (bvadd r9 r10)))\n"
        + f"(assert (= p_out {rtot_j}))\n"
        + "(assert (not (= p_out (bvadd g01 (bvadd g23 (bvadd g45 (bvadd r6 (bvadd g78 (bvadd g9a r11)))))))))\n"
        + "(check-sat)\n"
    )
    if not record("mul64_dsp_wiring_assoc",
                  "9-DSP qsag_mul64_dsp row-grouping associativity over Z/2^128Z",
                  "unsat", assoc64, prefer_bitwuzla=False):
        raise SystemExit("failed mul64_dsp row associativity")

    shl_mul_q = f"""(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(assert (not (and
  (= (bvshl x {bv(32, 128)}) (bvmul x {bv(1 << 32, 128)}))
  (= (bvshl x {bv(64, 128)}) (bvmul x {bv(1 << 64, 128)})))))
(check-sat)
"""
    if not record("mul64_dsp_shl_eq_mul",
                  "128-bit ring homomorphism: (x << 32) == x * 2^32 and (x << 64) == x * 2^64 (mod 2^128)",
                  "unsat", shl_mul_q, prefer_bitwuzla=False):
        raise SystemExit("failed shl_eq_mul lemma")

    join64 = (
        "(set-logic QF_BV)\n"
        + "(declare-const p0 (_ BitVec 67)) (declare-const p2 (_ BitVec 67)) (declare-const ps (_ BitVec 67))\n"
        + "(declare-const sa (_ BitVec 33)) (declare-const cb (_ BitVec 1))\n"
        + f"(define-fun p0w () (_ BitVec 128) {zext('p0', 67, 128)})\n"
        + f"(define-fun p2w () (_ BitVec 128) {zext('p2', 67, 128)})\n"
        + f"(define-fun psw () (_ BitVec 128) {zext('ps', 67, 128)})\n"
        + f"(define-fun cbt () (_ BitVec 128) (ite (= cb #b1) (bvmul {zext('sa', 33, 128)} {bv(1 << 64, 128)}) {bv(0, 128)}))\n"
        + f"(define-fun g01 () (_ BitVec 128) (bvadd p0w {bv(B33, 128)}))\n"
        + f"(define-fun g23 () (_ BitVec 128) (bvmul (bvadd p2w {bv(B33, 128)}) {bv(1 << 64, 128)}))\n"
        + f"(define-fun g45 () (_ BitVec 128) (bvmul (bvadd psw {bv(B33, 128)}) {bv(1 << 32, 128)}))\n"
        + f"(define-fun g78 () (_ BitVec 128) (bvsub {bv(2**128 - 2, 128)} (bvmul (bvadd p0w {bv(B33, 128)}) {bv(1 << 32, 128)})))\n"
        + f"(define-fun g9a () (_ BitVec 128) (bvsub {bv(2**128 - 2, 128)} (bvmul (bvadd p2w {bv(B33, 128)}) {bv(1 << 32, 128)})))\n"
        + f"(define-fun p_out () (_ BitVec 128) (bvadd g01 (bvadd g23 (bvadd g45 (bvadd cbt (bvadd g78 (bvadd g9a {bv(c_kara_val, 128)})))))))\n"
        + f"(define-fun k64 () (_ BitVec 128) (bvadd p0w (bvmul p2w {bv(1 << 64, 128)}) "
        + f"(bvadd cbt (bvmul (bvsub (bvsub psw p0w) p2w) {bv(1 << 32, 128)}))))\n"
        + "(assert (not (= p_out k64)))\n(check-sat)\n"
    )
    if not record("mul64_dsp_wiring_join",
                  "9-DSP qsag_mul64_dsp Modus Ponens join: pairwise CSA row invariants entail p@s3 == K64(P0,P2,PS,sa,cb)",
                  "unsat", join64, prefer_bitwuzla=False):
        raise SystemExit("failed mul64_dsp Modus Ponens join")

    # 3b. QF_NIA integer proof that K64(a0*b0, a1*b1, sa*beta, sa, cb) == a*b in [0, 2^128)
    nia64 = f"""(declare-const a0 Int) (declare-const a1 Int) (declare-const b0 Int) (declare-const b1 Int)
(declare-const beta Int) (declare-const cb Int)
(assert (and (<= 0 a0) (< a0 {2**32}) (<= 0 a1) (< a1 {2**32}) (<= 0 b0) (< b0 {2**32}) (<= 0 b1) (< b1 {2**32})))
(assert (and (<= 0 beta) (< beta {2**32}) (or (= cb 0) (= cb 1)) (= (+ b0 b1) (+ beta (* {2**32} cb)))))
(define-fun a () Int (+ a0 (* {2**32} a1)))
(define-fun b () Int (+ b0 (* {2**32} b1)))
(define-fun sa () Int (+ a0 a1))
(define-fun p0 () Int (* a0 b0))
(define-fun p2 () Int (* a1 b1))
(define-fun ps () Int (* sa beta))
(define-fun k64 () Int (+ p0 (* {2**64} p2) (* {2**64} (* cb sa)) (* {2**32} (- (- ps p0) p2))))
(assert (not (and (= k64 (* a b)) (<= 0 k64) (< k64 {2**128}))))
(check-sat)
"""
    if not record("mul64_dsp_karatsuba_exact",
                  "QF_NIA: outer 32-bit Karatsuba + cb carry-split K64 == a*b in [0, 2^128) for all 2^128 (a, b)",
                  "unsat", nia64):
        raise SystemExit("failed outer Karatsuba algebra proof")

    # 4. End-to-end temporal join of `qsag_gl64_dsp_mul` (`REG_OUT=1` and `REG_OUT=0`)
    glm_rel = open(GLM).read().replace(
        "qsag_mul64_dsp #(.AW(AW), .BW(BW)) u_mul (.clk(clk), .a(a), .b(b), .p(prod));",
        "qsag_mul64_exact u_mul (.clk(clk), .a(a), .b(b), .p(prod));"
    ) + """
module qsag_mul64_exact (input logic clk, input logic [63:0] a, input logic [63:0] b, output logic [127:0] p);
    logic [63:0] aq1, aq2, bq1, bq2;
    always_ff @(posedge clk) begin aq1 <= a; aq2 <= aq1; bq1 <= b; bq2 <= bq1; p <= 128'(aq2) * 128'(bq2); end
endmodule
"""
    glm_sv = os.path.join(OUT, "glmul_rel.sv")
    open(glm_sv, "w").write(glm_rel)
    for aw, bw in [(26, 17), (16, 16)]:
        for reg_out in (1, 0):
            tot = 5 if reg_out else 4
            tag = f"gl64_dsp_mul_{aw}x{bw}_reg{reg_out}"
            ys = yosys_smt2(tag, "qsag_gl64_dsp_mul", [PKG, RED, glm_sv],
                            f"-chparam AW {aw} -chparam BW {bw} -chparam REG_OUT {reg_out}")
            assert ys.count("(bvmul ") == 1
            ys_abs = "(declare-fun qmul64 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n" + ys.replace("(bvmul ", "(qmul64 ")
            prod_spec = f"(qmul64 {zext(acc('a','s0'), 64, 128)} {zext(acc('b','s0'), 64, 128)})"
            if not record(tag + "_product",
                          f"qsag_gl64_dsp_mul AW={aw} BW={bw} REG_OUT={reg_out}: prod@s3 == exact 128-bit product of a@s0, b@s0",
                          "unsat", ys_abs + unroll(3) + f"(assert (not (= {acc('prod','s3')} {prod_spec})))\n(check-sat)\n",
                          prefer_bitwuzla=True):
                raise SystemExit("failed glmul product join")
            cut = reduce_spec(zext(prod_spec, 128, 136), acc("r", f"s{tot}"))
            if not record(tag + "_end_to_end",
                          f"qsag_gl64_dsp_mul AW={aw} BW={bw} REG_OUT={reg_out}: full {tot}-clk pipeline emits canonical (a*b) mod p",
                          "unsat", ys_abs + unroll(tot) + f"(assert (not {cut}))\n(check-sat)\n",
                          prefer_bitwuzla=True):
                raise SystemExit("failed glmul end-to-end join")

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
                  "all 2^128 operand pairs: exact 128-bit product and bounded reduction entail r = (a*b) mod p uniquely",
                  "unsat", body):
        raise SystemExit("failed integer remainder join")

def check_sbox7_and_ext4_rtl():
    """Universal compositional RTL miters for `qsag_p2_sbox7` (13-cycle x^7 S-box) and
    `qsag_ext4_mac` (7-cycle 9-mul Tower Karatsuba F_{p^4} MAC) across BOTH AW=26/BW=17 and AW=16/BW=16."""
    # 1. `qsag_p2_sbox7`: 13-cycle wrapper over 4 proved `qsag_gl64_dsp_mul` instances
    sb_stub = os.path.join(OUT, "glmul_stub_sbox.sv")
    open(sb_stub, "w").write("""
module qsag_gl64_dsp_mul #(parameter int AW=26, parameter int BW=17, parameter bit REG_OUT=1'b1) (
    input logic clk, input logic [63:0] a, input logic [63:0] b, output logic [63:0] r
);
    logic [63:0] aq0, aq1, aq2, aq3, bq0, bq1, bq2, bq3;
    always_ff @(posedge clk) begin
        aq0 <= a;   bq0 <= b;
        aq1 <= aq0; bq1 <= bq0;
        aq2 <= aq1; bq2 <= bq1;
        aq3 <= aq2; bq3 <= bq2;
    end
    wire [63:0] prod = 64'(aq3) * 64'(bq3);
    if (REG_OUT) begin : g_reg
        always_ff @(posedge clk) r <= prod;
    end else begin : g_comb
        assign r = prod;
    end
endmodule
""")
    for aw, bw in [(26, 17), (16, 16)]:
        ys_sb = yosys_smt2(f"sbox7_rtl_{aw}x{bw}", "qsag_p2_sbox7", [PKG, sb_stub, SBOX],
                           f"-chparam AW {aw} -chparam BW {bw}", use_contracts=False)
        assert ys_sb.count("(bvmul ") == 4
        ys_sb_abs = ("(declare-fun qglmul ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))\n"
                     + ys_sb.replace("(bvmul ", "(qglmul "))
        x0 = flat_acc("x", 0)
        x2_e = f"(qglmul {x0} {x0})"
        x3_e = f"(qglmul {x2_e} {x0})"
        x4_e = f"(qglmul {x2_e} {x2_e})"
        x7_e = f"(qglmul {x3_e} {x4_e})"
        if not record(f"p2_sbox7_rtl_{aw}x{bw}",
                      f"qsag_p2_sbox7 AW={aw} BW={bw}: 13-cycle RTL pipeline emits glmul(glmul(glmul(x,x),x), glmul(glmul(x,x),glmul(x,x)))",
                      "unsat", flatten_ys_smt2(ys_sb_abs, "lec_top", 13) + f"(assert (not (= {flat_acc('y', 13)} {x7_e})))\n(check-sat)\n",
                      prefer_bitwuzla=True):
            raise SystemExit("failed p2_sbox7 RTL proof")

    sb_alg = f"""(declare-const x Int) (declare-const r2 Int) (declare-const r3 Int) (declare-const r4 Int) (declare-const y Int)
(declare-const q2 Int) (declare-const q3 Int) (declare-const q4 Int) (declare-const q7 Int)
(assert (= (* x x) (+ r2 (* {P} q2))))
(assert (= (* r2 x) (+ r3 (* {P} q3))))
(assert (= (* r2 r2) (+ r4 (* {P} q4))))
(assert (= (* r3 r4) (+ y (* {P} q7))))
(define-fun x7 () Int (* x (* x (* x (* x (* x (* x x)))))))
(define-fun q_tot () Int (+ q7 (* r4 q3) (* x (* r4 q2)) (* r2 (* r2 (* r2 (* x q4)))) (* r2 (* x (* (+ r4 (* r2 r2)) q2)))))
(assert (not (= (- x7 y) (* {P} (+ q7 (* r4 q3) (* (* x r4) q2) (* (* (* x x) x) (+ q4 (* (+ r2 (* x x)) q2))))))))
(check-sat)
"""
    if not record("p2_sbox7_algebra_modp",
                  "ring congruence over Z: 4-mul S-box tree r3*r4 - x^7 == p * Q_tot for all x",
                  "unsat", sb_alg):
        raise SystemExit("failed p2_sbox7 ring identity")

    # 2. `qsag_ext4_mac`: 7-cycle RTL wrapper over 9 proved `qsag_mul64_dsp` + `qsag_gl64_reduce` (AW=26 & AW=16)
    e4_stubs = os.path.join(OUT, "ext4_stubs.sv")
    open(e4_stubs, "w").write("""
module qsag_mul64_dsp #(parameter int AW=26, parameter int BW=17) (
    input logic clk, input logic [63:0] a, input logic [63:0] b, output logic [127:0] p
);
    logic [63:0] aq1, aq2, bq1, bq2;
    always_ff @(posedge clk) begin aq1 <= a; aq2 <= aq1; bq1 <= b; bq2 <= bq1; p <= 128'(aq2) * 128'(bq2); end
endmodule
module qsag_gl64_reduce #(parameter bit REG_OUT=1'b1) (
    input logic clk, input logic [135:0] x, output logic [63:0] r
);
    logic [135:0] xq1;
    always_ff @(posedge clk) begin xq1 <= x; r <= 64'(xq1 / 136'd3); end
endmodule
""")
    def mod_add2_bv(u, v):
        s = f"(bvadd {zext(u, 64, 65)} {zext(v, 64, 65)})"
        return f"(ite (bvuge {s} {bv(P, 65)}) ((_ extract 63 0) (bvsub {s} {bv(P, 65)})) ((_ extract 63 0) {s}))"

    def mod_add4_bv(x0, x1, x2, x3):
        return mod_add2_bv(mod_add2_bv(x0, x1), mod_add2_bv(x2, x3))

    for aw, bw in [(26, 17), (16, 16)]:
        ys_e4 = yosys_smt2(f"ext4_rtl_{aw}x{bw}", "qsag_ext4_mac", [PKG, e4_stubs, EXT4],
                           f"-chparam AW {aw} -chparam BW {bw}")
        ys_e4_abs = (
            "(declare-fun qmul64 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
            "(declare-fun qred136_raw ((_ BitVec 136) (_ BitVec 136)) (_ BitVec 136))\n"
            + ys_e4.replace("(bvmul ", "(qmul64 ").replace("(bvudiv ", "(qred136_raw ")
        )
        # Stage 0: all 18 canonical pre-sum registers ma_q[0..8], mb_q[0..8]
        fl1 = flatten_ys_smt2(ys_e4_abs, "lec_top", 1)
        a_s0, b_s0 = flat_acc("a", 0), flat_acc("b", 0)
        al = [f"((_ extract {64*i+63} {64*i}) {a_s0})" for i in range(4)]
        bl = [f"((_ extract {64*i+63} {64*i}) {b_s0})" for i in range(4)]
        can_h = "".join(f"(assert (bvult {al[i]} {bv(P, 64)}))\n(assert (bvult {bl[i]} {bv(P, 64)}))\n" for i in range(4))
        exp_a = [al[0], al[1], mod_add2_bv(al[0], al[1]), al[2], al[3], mod_add2_bv(al[2], al[3]),
                 mod_add2_bv(al[0], al[2]), mod_add2_bv(al[1], al[3]), mod_add4_bv(*al)]
        exp_b = [bl[0], bl[1], mod_add2_bv(bl[0], bl[1]), bl[2], bl[3], mod_add2_bv(bl[2], bl[3]),
                 mod_add2_bv(bl[0], bl[2]), mod_add2_bv(bl[1], bl[3]), mod_add4_bv(*bl)]
        maq, mbq = flat_acc("ma_q", 1), flat_acc("mb_q", 1)
        s0_eqs = (
            [f"(= ((_ extract {64*i+63} {64*i}) {maq}) {exp_a[i]})" for i in range(9)]
            + [f"(= ((_ extract {64*i+63} {64*i}) {mbq}) {exp_b[i]})" for i in range(9)]
        )
        if not record(f"ext4_mac_stage0_{aw}x{bw}",
                      f"qsag_ext4_mac AW={aw} BW={bw}: all 18 Stage-0 pre-sum registers ma_q[0..8], mb_q[0..8] canonical mod p",
                      "unsat", fl1 + can_h + "(assert (not (and " + " ".join(s0_eqs) + ")))\n(check-sat)\n",
                      prefer_bitwuzla=True):
            raise SystemExit("failed ext4 Stage-0 proof")

        # Full 7-cycle pipeline Stage 4..6 check
        fl7 = flatten_ys_smt2(ys_e4_abs, "lec_top", 7)
        c_s0 = flat_acc("c", 0)
        cl = [f"((_ extract {64*i+63} {64*i}) {c_s0})" for i in range(4)]
        c_hyp = "".join(f"(assert (bvult {cl[i]} {bv(P, 64)}))\n" for i in range(4))
        m_s4 = flat_acc("m", 4)
        ms4 = [f"((_ extract {128*i+127} {128*i}) {m_s4})" for i in range(9)]
        m_hyp = "".join(f"(assert (bvule {ms4[i]} {bv((P - 1)**2, 128)}))\n" for i in range(9))
        if aw > 16:
            C1_136 = bv(0x0000_0001_0000_0001, 136)
            pm = [zext(ms4[i], 128, 136) for i in range(9)]
            nm = [zext(f"(bvnot {ms4[i]})", 128, 136) for i in range(8)]
            def mul7_136(x): return f"(bvadd {x} (bvadd (bvshl {x} {bv(1,136)}) (bvshl {x} {bv(2,136)})))"
            def bsum(ts):
                r = ts[0]
                for t in ts[1:]: r = f"(bvadd {r} {t})"
                return r
            exp_acc = [
                bsum([bv(14 * 0x100000001, 136), zext(cl[0], 64, 136), pm[0], mul7_136(pm[1]), mul7_136(pm[5]), mul7_136(nm[3]), mul7_136(nm[4])]),
                bsum([bv(2 * 0x100000001, 136),  zext(cl[1], 64, 136), pm[2], pm[3], mul7_136(pm[4]), nm[0], nm[1]]),
                bsum([bv(16 * 0x100000001, 136), zext(cl[2], 64, 136), pm[6], mul7_136(pm[7]), nm[0], mul7_136(nm[1]), nm[3], mul7_136(nm[4])]),
                bsum([bv(4 * 0x100000001, 136),  zext(cl[3], 64, 136), pm[8], pm[0], pm[1], pm[3], pm[4], nm[6], nm[7], nm[2], nm[5]]),
            ]
            accq5 = flat_acc("acc_q", 5)
            y7 = flat_acc("y", 7)
            eqs_w = []
            for k in range(4):
                ak = f"((_ extract {136*k+135} {136*k}) {accq5})"
                yk = f"((_ extract {64*k+63} {64*k}) {y7})"
                eqs_w.append(f"(= {ak} {exp_acc[k]})")
                eqs_w.append(f"(= {yk} ((_ extract 63 0) (qred136_raw {ak} {bv(3, 136)})))")
            if not record("ext4_mac_pipe_26x17",
                          "qsag_ext4_mac AW=26 BW=17: 7-cycle RTL Stage-4 accumulators & Stage-6 reducer join over all inputs",
                          "unsat", fl7 + can_h + c_hyp + m_hyp + "(assert (not (and " + " ".join(eqs_w) + ")))\n(check-sat)\n",
                          prefer_bitwuzla=True):
                raise SystemExit("failed ext4 AW=26 7-cycle RTL proof")
        else:
            # Prove ECP5 AW=16 Stage-4 128->66b fold (`v_q` congruent mod p & < 3p) AND Stage-5..6 72b B66 Karatsuba + red72!
            vq5 = flat_acc("v_q", 5)
            v_clauses = []
            for i in range(9):
                vi = zext(f"((_ extract {66*i+65} {66*i}) {vq5})", 66, 136)
                lo_i = zext(f"((_ extract 63 0) {ms4[i]})", 64, 136)
                mid_i = zext(f"((_ extract 95 64) {ms4[i]})", 32, 136)
                hi_i = zext(f"((_ extract 127 96) {ms4[i]})", 32, 136)
                v_exact = f"(bvsub (bvadd {bv(P, 136)} (bvadd {lo_i} (bvshl {mid_i} {bv(32, 136)}))) (bvadd {mid_i} {hi_i}))"
                v_clauses.append(f"(= {vi} {v_exact})")
                v_clauses.append(f"(bvult {vi} {bv(3 * P, 136)})")
            if not record("ext4_mac_ecp5_stage4_vfold",
                          "qsag_ext4_mac AW=16 BW=16: Stage-4 128->66b Solinas fold v_q[0..8] == V(m[i]) in (0, 3p)",
                          "unsat", fl7 + can_h + c_hyp + m_hyp + "(assert (not (and " + " ".join(v_clauses) + ")))\n(check-sat)\n",
                          prefer_bitwuzla=True):
                raise SystemExit("failed ext4 ECP5 Stage-4 v_q proof")

            # Stage 5 (cut at `acc72_q@s6`): exact 72-bit B66 Karatsuba accumulator check (0.1s, zero bvurem!)
            acc72_s6 = flat_acc("acc72_q", 6)
            B66_v = 0x00_FFFF_FFFB_0000_0006
            pv = [zext(f"((_ extract {66*i+65} {66*i}) {vq5})", 66, 72) for i in range(9)]
            nv = [zext(f"(bvnot ((_ extract {66*i+65} {66*i}) {vq5}))", 66, 72) for i in range(8)]
            cs72 = [zext(cl[k], 64, 72) for k in range(4)]
            v_bound72 = "".join(f"(assert (bvult {pv[i]} {bv(3 * P, 72)}))\n" for i in range(9))
            def bsum72(ts):
                r = ts[0]
                for t in ts[1:]: r = f"(bvadd {r} {t})"
                return r
            s0_72 = bsum72([pv[1], pv[5], nv[3], nv[4]])
            s2_72 = bsum72([pv[7], nv[1], nv[4]])
            exp72 = [
                bsum72([bv(14 * B66_v + 1, 72), cs72[0], pv[0], f"(bvshl {s0_72} {bv(3, 72)})", f"(bvnot {s0_72})"]),
                bsum72([bv(3 * B66_v, 72),      cs72[1], pv[2], pv[3], f"(bvshl {pv[4]} {bv(3, 72)})", nv[4], nv[0], nv[1]]),
                bsum72([bv(16 * B66_v + 1, 72), cs72[2], pv[6], nv[0], nv[3], f"(bvshl {s2_72} {bv(3, 72)})", f"(bvnot {s2_72})"]),
                bsum72([bv(4 * B66_v, 72),      cs72[3], pv[8], pv[0], pv[1], pv[3], pv[4], nv[6], nv[7], nv[2], nv[5]]),
            ]
            s5_eqs = [f"(= ((_ extract {72*k+71} {72*k}) {acc72_s6}) {exp72[k]})" for k in range(4)]
            if not record("ext4_mac_ecp5_stage5_acc72",
                          "qsag_ext4_mac AW=16 BW=16: Stage-5 72-bit B66 Karatsuba accumulators acc72_q[0..3] exact",
                          "unsat", fl7 + c_hyp + v_bound72 + "(assert (not (and " + " ".join(s5_eqs) + ")))\n(check-sat)\n",
                          prefer_bitwuzla=True):
                raise SystemExit("failed ext4 ECP5 Stage-5 acc72 proof")

            # Stage 6 (`g_red72` from `acc72_q@s6` to `y@s7`, zero bvurem!): prove y_k < p and acc72_k == y_k + p*(m8 + sel)
            y7 = flat_acc("y", 7)
            P76 = bv(P, 76)
            s6_eqs = []
            acc72_bnds = []
            for k in range(4):
                ak72 = f"((_ extract {72*k+71} {72*k}) {acc72_s6})"
                acc72_bnds.append(f"(assert (bvult {ak72} {bv(120 * (1 << 64), 72)}))\n")
                ak76 = zext(ak72, 72, 76)
                m8_76 = zext(f"((_ extract 71 64) {ak72})", 8, 76)
                yk76 = zext(f"((_ extract {64*k+63} {64*k}) {y7})", 64, 76)
                q0 = f"(bvmul {m8_76} {P76})"
                q1 = f"(bvmul (bvadd {m8_76} {bv(1, 76)}) {P76})"
                s6_eqs.append(f"(bvult {yk76} {P76})")
                s6_eqs.append(f"(or (= {ak76} (bvadd {yk76} {q0})) (= {ak76} (bvadd {yk76} {q1})))")
            if not record("ext4_mac_ecp5_stage6_red72",
                          "qsag_ext4_mac AW=16 BW=16: Stage-6 red72 emits canonical y[0..3] < p congruent to acc72_q mod p",
                          "unsat", fl7 + "".join(acc72_bnds) + "(assert (not (and " + " ".join(s6_eqs) + ")))\n(check-sat)\n",
                          prefer_bitwuzla=True):
                raise SystemExit("failed ext4 ECP5 Stage-6 red72 proof")

            # QF_LIA algebraic congruence & non-overflow of Stage-5 72-bit B66 formulas over Z:
            M66 = 2**66 - 1
            KP66 = 5  # (2^66 - 1) + B66 == 5*p
            lia_decl = "".join(f"(declare-const v{i} Int)\n" for i in range(9)) + "".join(f"(declare-const c{k} Int)\n" for k in range(4))
            lia_rng = ("(assert (and "
                       + " ".join(f"(<= 0 v{i}) (< v{i} {3 * P})" for i in range(9)) + " "
                       + " ".join(f"(<= 0 c{k}) (< c{k} {P})" for k in range(4)) + "))\n")
            nv_i = [f"(- {M66} v{i})" for i in range(8)]
            s0_i = f"(+ v1 v5 {nv_i[3]} {nv_i[4]})"
            s2_i = f"(+ v7 {nv_i[1]} {nv_i[4]})"
            # Note: in W=72 bitvector arithmetic, `8*s_i + (2^72 - 1 - s_i) + 1 = 2^72 + 7*s_i`, dropping 1 * 2^72:
            e72_int = [
                f"(+ (* 14 {B66_v}) c0 v0 (* 7 {s0_i}))",
                f"(+ (* 3 {B66_v}) c1 v2 v3 (* 8 v4) {nv_i[4]} {nv_i[0]} {nv_i[1]})",
                f"(+ (* 16 {B66_v}) c2 v6 {nv_i[0]} {nv_i[3]} (* 7 {s2_i}))",
                f"(+ (* 4 {B66_v}) c3 v8 v0 v1 v3 v4 {nv_i[6]} {nv_i[7]} {nv_i[2]} {nv_i[5]})",
            ]
            kt_int = [
                "(+ c0 v0 (* 7 (- (+ v1 v5) (+ v3 v4))))",
                "(- (+ c1 v2 v3 (* 7 v4)) (+ v0 v1))",
                "(+ (- (+ c2 v6) (+ v0 v3)) (* 7 (- v7 (+ v1 v4))))",
                "(- (+ c3 v8 v0 v1 v3 v4) (+ v6 v7 v2 v5))",
            ]
            q72_int = [14 * KP66, 3 * KP66, 16 * KP66, 4 * KP66]
            lia_cs = []
            for k in range(4):
                lia_cs.append(f"(> {e72_int[k]} 0)")
                lia_cs.append(f"(< {e72_int[k]} {120 * (1 << 64)})")
                lia_cs.append(f"(= (- {e72_int[k]} {kt_int[k]}) (* {P} {q72_int[k]}))")
            if not record("ext4_mac_ecp5_b66_algebra",
                          "QF_LIA: 72-bit B66 Karatsuba formulas stay in (0, 120*2^64) and equal Karatsuba + 5p*K over Z",
                          "unsat", lia_decl + lia_rng + "(assert (not (and " + " ".join(lia_cs) + ")))\n(check-sat)\n"):
                raise SystemExit("failed ext4 ECP5 B66 QF_LIA proof")

def group_gl():
    check_adder_contracts()
    check_reduce_algebra()
    check_ext4_karatsuba_algebra()
    check_reduce("gl64_reduce_reg1", [PKG, RED], "unsat", reg_out=1)
    check_reduce("gl64_reduce_reg0", [PKG, RED], "unsat", reg_out=0)
    check_mul33x32_and_mul64_9dsp()
    check_remainder_glue()
    check_sbox7_and_ext4_rtl()

def group_glmut():
    if not CONTRACTS_READY:
        check_adder_contracts()
    # Mutant 1: reducer Stage-1 negated limb h sign flip
    m1 = mutate(RED, "assign terms[3*66 +: 66] = ~{34'b0, h};", "assign terms[3*66 +: 66] = {34'b0, h};", "mut_reduce_sign.sv")
    if not check_reduce("mut_gl64_reduce_sign", [PKG, m1], "sat"):
        raise SystemExit("mutant 1 failed")
    # Mutant 2: reducer Stage-2 wrong candidate selection
    m2 = mutate(RED, "!v2[66] ? v2[63:0]", "!v2[66] ? v1[63:0]", "mut_reduce_select.sv")
    if not check_reduce("mut_gl64_reduce_select", [PKG, m2], "sat"):
        raise SystemExit("mutant 2 failed")
    # Mutant 3: 3-DSP `qsag_mul33x32_dsp` wires `b0_q <= b1` instead of `b0`
    m3_raw = mutate(MUL33, "a0_q <= a0;   b0_q <= b0;", "a0_q <= a0;   b0_q <= b1;", "mut_mul33_tile_raw.sv")
    m3_txt = open(m3_raw).read()
    m3_txt = m3_txt.replace("32'(a0_q) * 32'(b0_q)", "dsp36_p0[31:0]")
    m3_txt = m3_txt.replace("33'(a1_q) * 33'(b1_q)", "dsp36_p1[32:0]")
    m3_txt = m3_txt.replace("35'(as_q) * 35'(bs_q)", "dsp36_ps[34:0]")
    m3_txt = m3_txt.replace(
        "always_ff @(posedge clk) begin",
        "wire [35:0] dsp36_p0 = 36'(a0_q) * 36'(b0_q);\n"
        "    wire [35:0] dsp36_p1 = 36'(a1_q) * 36'(b1_q);\n"
        "    wire [35:0] dsp36_ps = 36'(as_q) * 36'(bs_q);\n"
        "    always_ff @(posedge clk) begin"
    )
    m3 = os.path.join(OUT, "mut_mul33_tile.sv")
    open(m3, "w").write(m3_txt)
    ys3 = yosys_smt2("mut_mul33_tile", "qsag_mul33x32_dsp", [m3], use_contracts=False)
    ys3_abs = "(declare-fun qdsp36 ((_ BitVec 36) (_ BitVec 36)) (_ BitVec 36))\n" + ys3.replace("(bvmul ", "(qdsp36 ")
    a33, b32 = acc("a", "s0"), acc("b", "s0")
    a0_36 = zext(f"((_ extract 15 0) {a33})", 16, 36)
    a1_36 = zext(f"((_ extract 32 16) {a33})", 17, 36)
    b0_36 = zext(f"((_ extract 15 0) {b32})", 16, 36)
    b1_36 = zext(f"((_ extract 31 16) {b32})", 16, 36)
    as_36 = zext(f"(bvadd {zext(f'((_ extract 15 0) {a33})', 16, 18)} {zext(f'((_ extract 32 16) {a33})', 17, 18)})", 18, 36)
    bs_36 = zext(f"(bvadd {zext(f'((_ extract 15 0) {b32})', 16, 17)} {zext(f'((_ extract 31 16) {b32})', 16, 17)})", 17, 36)
    t0_36, t1_36, ts_36 = f"(qdsp36 {a0_36} {b0_36})", f"(qdsp36 {a1_36} {b1_36})", f"(qdsp36 {as_36} {bs_36})"
    hyps3 = (f"(assert (bvule {t0_36} {bv((2**16 - 1)**2, 36)}))\n"
             f"(assert (bvule {t1_36} {bv((2**17 - 1) * (2**16 - 1), 36)}))\n"
             f"(assert (bvule {ts_36} {bv(((2**16 - 1) + (2**17 - 1)) * 2 * (2**16 - 1), 36)}))\n")
    t0, t1, ts = zext(t0_36, 36, 68), zext(t1_36, 36, 68), zext(ts_36, 36, 68)
    k33 = (f"(bvadd {t0} (bvshl {t1} {bv(32, 68)}) "
           f"(bvshl (bvsub (bvsub (bvadd {ts} {bv((2**32 - 1) + (2**33 - 1), 68)}) {t0}) {t1}) {bv(16, 68)}))")
    sc68 = f"(bvadd {zext(acc('s','s2'), 66, 68)} {zext(acc('c','s2'), 66, 68)})"
    if not record("mut_mul33x32_dsp_tile", "mutant tooth: wrong b-half in 3-DSP qsag_mul33x32_dsp is refuted",
                  "sat", ys3_abs + unroll(2) + hyps3 + f"(assert (not (= {sc68} {k33})))\n(check-sat)\n", prefer_bitwuzla=True):
        raise SystemExit("mutant 3 failed")
    # Mutant 4: 9-DSP `qsag_mul64_dsp` shifts `p2_s` by 65 instead of 64
    m4_src = open(os.path.join(OUT, "mul64_rel.sv")).read() if os.path.exists(os.path.join(OUT, "mul64_rel.sv")) else ""
    if not m4_src or "fc0" not in m4_src:
        check_mul33x32_and_mul64_9dsp()
        m4_src = open(os.path.join(OUT, "mul64_rel.sv")).read()
    m4_sv = os.path.join(OUT, "mut_mul64_shift.sv")
    assert "128'(p2_s) << 64," in m4_src
    open(m4_sv, "w").write(m4_src.replace("128'(p2_s) << 64,", "128'(p2_s) << 65,", 1))
    ys4 = yosys_smt2("mut_mul64_shift", "qsag_mul64_dsp", [m4_sv], "-chparam AW 26 -chparam BW 17")
    ys4_abs = "(declare-fun qmul33 ((_ BitVec 67) (_ BitVec 67)) (_ BitVec 67))\n" + ys4.replace("(bvmul ", "(qmul33 ")
    a64, b64 = acc("a", "s0"), acc("b", "s0")
    a0_67, a1_67 = zext(f"((_ extract 31 0) {a64})", 32, 67), zext(f"((_ extract 63 32) {a64})", 32, 67)
    b0_67, b1_67 = zext(f"((_ extract 31 0) {b64})", 32, 67), zext(f"((_ extract 63 32) {b64})", 32, 67)
    sa_33 = f"(bvadd {zext(f'((_ extract 31 0) {a64})', 32, 33)} {zext(f'((_ extract 63 32) {a64})', 32, 33)})"
    sb_33 = f"(bvadd {zext(f'((_ extract 31 0) {b64})', 32, 33)} {zext(f'((_ extract 31 0) ((_ extract 63 32) {b64}))', 32, 33)})"
    p0_67 = f"(qmul33 {a0_67} {b0_67})"
    p2_67 = f"(qmul33 {a1_67} {b1_67})"
    ps_67 = f"(qmul33 {zext(sa_33,33,67)} {zext(f'((_ extract 31 0) {sb_33})',32,67)})"
    hyps4 = (
        f"(assert (bvule {p0_67} {bv((2**32 - 1)**2, 67)}))\n"
        f"(assert (bvule {p2_67} {bv((2**32 - 1)**2, 67)}))\n"
        f"(assert (bvule {ps_67} {bv((2**33 - 1) * (2**32 - 1), 67)}))\n"
        f"(assert (= (bvadd {zext(acc('p0_s','s2'),66,68)} {zext(acc('p0_c','s2'),66,68)}) (bvadd {zext(acc('pr0','s2'),67,68)} {bv(B33,68)})))\n"
        f"(assert (= (bvadd {zext(acc('p2_s','s2'),66,68)} {zext(acc('p2_c','s2'),66,68)}) (bvadd {zext(acc('pr2','s2'),67,68)} {bv(B33,68)})))\n"
        f"(assert (= (bvadd {zext(acc('ps_s','s2'),66,68)} {zext(acc('ps_c','s2'),66,68)}) (bvadd {zext(acc('prs','s2'),67,68)} {bv(B33,68)})))\n"
    )
    r2_4 = f"((_ extract 383 256) {acc('outer_rows', 's2')})"
    r3_4 = f"((_ extract 511 384) {acc('outer_rows', 's2')})"
    p2_target = f"(bvshl (bvadd {zext(p2_67,67,128)} {bv(B33, 128)}) {bv(64, 128)})"
    if not record("mut_shift_mul64_dsp", "mutant tooth: 1-bit shift fault on p2_s in 9-DSP qsag_mul64_dsp is refuted",
                  "sat", ys4_abs + unroll(3) + hyps4 + f"(assert (not (= (bvadd {r2_4} {r3_4}) {p2_target})))\n(check-sat)\n", prefer_bitwuzla=True):
        raise SystemExit("mutant 4 failed")
    # Mutant 5: 3:2 CSA carry shifted by 2 instead of 1
    m_csa = mutate(CSA2, ") << 1;", ") << 2;", "mut_csa2_shift.sv")
    sh(f'yosys -q -p "read_verilog -sv {m_csa}; hierarchy -top qsag_csa_reduce2 -chparam W 64 -chparam N 3; '
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
    # Mutant 7: `qsag_p2_sbox7` wires `.b(x3)` instead of `.b(x2)` on `u_x4`
    sb_stub = os.path.join(OUT, "glmul_stub_sbox.sv")
    if not os.path.exists(sb_stub):
        check_sbox7_and_ext4_rtl()
    m_sb = mutate(SBOX, "u_x4 (.clk(clk), .a(x2), .b(x2), .r(x4));", "u_x4 (.clk(clk), .a(x2), .b(x3), .r(x4));", "mut_sbox7.sv")
    ys_msb = yosys_smt2("mut_sbox7", "qsag_p2_sbox7", [PKG, sb_stub, m_sb], "-chparam AW 16 -chparam BW 16", use_contracts=False)
    ys_msb_abs = "(declare-fun qglmul ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))\n" + ys_msb.replace("(bvmul ", "(qglmul ")
    mx0 = flat_acc("x", 0)
    mx2 = f"(qglmul {mx0} {mx0})"
    mx7 = f"(qglmul (qglmul {mx2} {mx0}) (qglmul {mx2} {mx2}))"
    if not record("mut_p2_sbox7_port", "mutant tooth: wrong multiplier operand in qsag_p2_sbox7 is refuted",
                  "sat", flatten_ys_smt2(ys_msb_abs, "lec_top", 13) + f"(assert (not (= {flat_acc('y', 13)} {mx7})))\n(check-sat)\n",
                  prefer_bitwuzla=True):
        raise SystemExit("mutant 7 failed")
    # Mutant 8: `qsag_ext4_mac` AW=16 `72'(2)*B66 + 1` limb-1 bias bug
    e4_stubs = os.path.join(OUT, "ext4_stubs.sv")
    m_e4 = mutate(EXT4, "72'(3) * B66, 72'(c1),", "72'(2) * B66 + 72'd1, 72'(c1),", "mut_ext4_b66.sv")
    ys_me4 = yosys_smt2("mut_ext4_b66", "qsag_ext4_mac", [PKG, e4_stubs, m_e4], "-chparam AW 16 -chparam BW 16")
    ys_me4_abs = ("(declare-fun qmul64 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
                  "(declare-fun qred136_raw ((_ BitVec 136) (_ BitVec 136)) (_ BitVec 136))\n"
                  + ys_me4.replace("(bvmul ", "(qmul64 ").replace("(bvudiv ", "(qred136_raw "))
    fl7m = flatten_ys_smt2(ys_me4_abs, "lec_top", 7)
    vq5m = flat_acc("v_q", 5)
    c1_72 = zext(f"((_ extract 127 64) {flat_acc('c', 0)})", 64, 72)
    pv_m = [zext(f"((_ extract {66*i+65} {66*i}) {vq5m})", 66, 72) for i in range(5)]
    nv_m = [zext(f"(bvnot ((_ extract {66*i+65} {66*i}) {vq5m}))", 66, 72) for i in range(5)]
    vb_m = f"(assert (bvult {c1_72} {bv(P, 72)}))\n" + "".join(f"(assert (bvult {pv_m[i]} {bv(3 * P, 72)}))\n" for i in range(5))
    exp72_1 = f"(bvadd {bv(3 * 0x00_FFFF_FFFB_0000_0006, 72)} (bvadd {c1_72} (bvadd {pv_m[2]} (bvadd {pv_m[3]} (bvadd (bvshl {pv_m[4]} {bv(3, 72)}) (bvadd {nv_m[4]} (bvadd {nv_m[0]} {nv_m[1]})))))))"
    got72_1 = f"((_ extract 143 72) {flat_acc('acc72_q', 6)})"
    if not record("mut_ext4_ecp5_b66_y1", "mutant tooth: 2*B66+1 bias fault in qsag_ext4_mac AW=16 limb 1 is refuted",
                  "sat", fl7m + vb_m + f"(assert (not (= {got72_1} {exp72_1})))\n(check-sat)\n",
                  prefer_bitwuzla=True):
        raise SystemExit("mutant 8 failed")

def group_ext5():
    """Z3 formal verification of zk-Hem v2 14-multiply Split-(3,2) Karatsuba F_p[X]/(X^5 - 3) MAC:
      1) Range proof: 0 < acc_k < 2^136 for all 5 limbs over all 128-bit m_i and 64-bit c_k;
      2) Universal modular congruence proof: acc_k - schoolbook_k == p * Q_k over Z;
      3) RTL Stage-0 canonical pre-adder + Stage-4 CSA recombination equivalence on actual `qsag_ext5_mac.sv` + mutant `sat`."""
    if not CONTRACTS_READY:
        check_adder_contracts()
    M128 = 2**128 - 1
    C1 = 2**32 + 1
    KP = 2**64 + 2**32  # M128 + C1 = P * KP

    r_vars = [f"c{i}" for i in range(5)] + [f"m{i}" for i in range(14)]
    r_decl = "".join(f"(declare-const {v} Int)\n" for v in r_vars)
    r_rng = ("(assert (and "
             + " ".join(f"(>= c{i} 0) (< c{i} {2**64})" for i in range(5)) + " "
             + " ".join(f"(>= m{i} 0) (< m{i} {2**128})" for i in range(14)) + "))\n")
    nm = [f"(- {M128} m{i})" for i in range(11)]
    accs_r = [
        f"(+ (* 12 {C1}) c0 (* 4 m0) (* 3 m10) (* 3 m12) (* 3 {nm[1]}) (* 3 {nm[4]}) (* 3 {nm[7]}) (* 3 {nm[9]}))",
        f"(+ (* 7 {C1}) c1 m3 (* 2 m1) (* 3 m6) (* 3 m13) {nm[0]} (* 3 {nm[5]}) (* 3 {nm[10]}))",
        f"(+ (* 8 {C1}) c2 m1 m4 (* 3 m8) {nm[0]} {nm[2]} (* 3 {nm[6]}) (* 3 {nm[7]}))",
        f"(+ (* 4 {C1}) c3 m5 m9 (* 3 m7) {nm[0]} {nm[1]} {nm[2]} {nm[6]})",
        f"(+ (* 4 {C1}) c4 m0 m1 m2 m6 m7 m11 {nm[3]} {nm[8]} {nm[9]} {nm[10]})",
    ]
    for k, acc_e in enumerate(accs_r):
        if not record(f"ext5_karatsuba_range_limb{k}",
                      f"14-mul F_{{p^5}} Karatsuba limb {k}: 0 < acc < 2^136 for all 2^128 products and 64-bit c",
                      "unsat", r_decl + r_rng + f"(assert (not (and (> {acc_e} 0) (< {acc_e} {2**136}))))\n(check-sat)\n"):
            raise SystemExit("failed Ext5 range proof")

    # Universal congruence over Z:
    subsets = [
        ("01", "(+ a0 a1)", "(+ b0 b1)"),
        ("02", "(+ a0 a2)", "(+ b0 b2)"),
        ("12", "(+ a1 a2)", "(+ b1 b2)"),
        ("34", "(+ a3 a4)", "(+ b3 b4)"),
        ("03", "(+ a0 a3)", "(+ b0 b3)"),
        ("14", "(+ a1 a4)", "(+ b1 b4)"),
        ("0134", "(+ a0 a1 a3 a4)", "(+ b0 b1 b3 b4)"),
        ("023", "(+ a0 a2 a3)", "(+ b0 b2 b3)"),
        ("124", "(+ a1 a2 a4)", "(+ b1 b2 b4)"),
    ]
    k_names = [f"ka_{s}" for s, _, _ in subsets] + [f"kb_{s}" for s, _, _ in subsets]
    all_v = [f"a{i}" for i in range(5)] + [f"b{i}" for i in range(5)] + [f"c{i}" for i in range(5)] + k_names
    decl = "".join(f"(declare-const {v} Int)\n" for v in all_v)
    def subp(s, kv): return f"(- {s} (* {P} {kv}))"
    def qmul(sa, sb, ka, kb): return f"(- (+ (* {ka} {sb}) (* {kb} {sa})) (* {P} (* {ka} {kb})))"
    qm = {s: qmul(sa, sb, f"ka_{s}", f"kb_{s}") for s, sa, sb in subsets}
    sm = {s: f"(* {subp(sa, f'ka_{s}')} {subp(sb, f'kb_{s}')})" for s, sa, sb in subsets}
    ms = [
        "(* a0 b0)", "(* a1 b1)", "(* a2 b2)",
        sm["01"], sm["02"], sm["12"],
        "(* a3 b3)", "(* a4 b4)",
        sm["34"], sm["03"], sm["14"],
        sm["0134"], sm["023"], sm["124"],
    ]
    nmi = [f"(- {M128} {ms[i]})" for i in range(11)]
    accs = [
        f"(+ (* 12 {C1}) c0 (* 4 {ms[0]}) (* 3 {ms[10]}) (* 3 {ms[12]}) (* 3 {nmi[1]}) (* 3 {nmi[4]}) (* 3 {nmi[7]}) (* 3 {nmi[9]}))",
        f"(+ (* 7 {C1}) c1 {ms[3]} (* 2 {ms[1]}) (* 3 {ms[6]}) (* 3 {ms[13]}) {nmi[0]} (* 3 {nmi[5]}) (* 3 {nmi[10]}))",
        f"(+ (* 8 {C1}) c2 {ms[1]} {ms[4]} (* 3 {ms[8]}) {nmi[0]} {nmi[2]} (* 3 {nmi[6]}) (* 3 {nmi[7]})",
        f"(+ (* 4 {C1}) c3 {ms[5]} {ms[9]} (* 3 {ms[7]}) {nmi[0]} {nmi[1]} {nmi[2]} {nmi[6]})",
        f"(+ (* 4 {C1}) c4 {ms[0]} {ms[1]} {ms[2]} {ms[6]} {ms[7]} {ms[11]} {nmi[3]} {nmi[8]} {nmi[9]} {nmi[10]})",
    ]
    # Close paren on accs[2]
    accs[2] += ")"
    sbs = [
        "(+ c0 (* a0 b0) (* 3 (+ (* a1 b4) (* a2 b3) (* a3 b2) (* a4 b1))))",
        "(+ c1 (* a0 b1) (* a1 b0) (* 3 (+ (* a2 b4) (* a3 b3) (* a4 b2))))",
        "(+ c2 (* a0 b2) (* a1 b1) (* a2 b0) (* 3 (+ (* a3 b4) (* a4 b3))))",
        "(+ c3 (* a0 b3) (* a1 b2) (* a2 b1) (* a3 b0) (* 3 (* a4 b4)))",
        "(+ c4 (* a0 b4) (* a1 b3) (* a2 b2) (* a3 b1) (* a4 b0))",
    ]
    qs = [
        f"(+ (- (* 12 {KP}) (* 3 {qm['14']}) (* 3 {qm['023']})) (* 3 {qm['02']}) (* 3 {qm['03']}))",
        f"(+ (- (* 7 {KP}) {qm['01']} (* 3 {qm['124']})) (* 3 {qm['12']}) (* 3 {qm['14']}))",
        f"(- (* 8 {KP}) {qm['02']} (* 3 {qm['34']}))",
        f"(- (* 4 {KP}) {qm['12']} {qm['03']})",
        f"(+ (- (* 4 {KP}) {qm['0134']}) {qm['01']} {qm['34']} {qm['03']} {qm['14']})",
    ]
    for k in range(5):
        if not record(f"ext5_karatsuba_modp_limb{k}",
                      f"14-mul F_{{p^5}} Karatsuba limb {k}: exact congruence acc - schoolbook == p * Q_k over F_p[X]/(X^5 - 3)",
                      "unsat", decl + f"(assert (not (= (- {accs[k]} {sbs[k]}) (* {P} {qs[k]}))))\n(check-sat)\n"):
            raise SystemExit("failed Ext5 congruence proof")

    # RTL checks on `qsag_ext5_mac.sv` with `u_mul` abstracted as uninterpreted `qmul64` and `u_red` checked at acc_q / y
    ext5_src = open(EXT5).read()
    ext5_cut = ext5_src.replace(
        "output logic [319:0] y",
        "output logic [319:0] y,\n    output logic [13:0][63:0] dbg_ma, dbg_mb,\n    output logic [4:0][135:0] dbg_acc"
    ).replace(
        "endmodule",
        "    assign dbg_ma = ma_q; assign dbg_mb = mb_q; assign dbg_acc = acc_q;\nendmodule"
    )
    ext5_sv = os.path.join(OUT, "ext5_cut.sv")
    open(ext5_sv, "w").write(ext5_cut)

    m64_stub = """
module qsag_mul64_dsp #(parameter int AW=26, parameter int BW=17)(
    input logic clk, input logic [63:0] a, input logic [63:0] b, output logic [127:0] p);
    logic [63:0] aq1, aq2, bq1, bq2;
    always_ff @(posedge clk) begin aq1 <= a; aq2 <= aq1; bq1 <= b; bq2 <= bq1; p <= 128'(aq2) * 128'(bq2); end
endmodule
"""
    stub_sv = os.path.join(OUT, "m64_stub_ext5.sv")
    open(stub_sv, "w").write(m64_stub)

    red_stub = """
module qsag_gl64_reduce #(parameter bit REG_OUT = 1'b1)(
    input logic clk, input logic [135:0] x, output logic [63:0] r);
    logic [135:0] xq1;
    wire [135:0] q = xq1 / (xq1 | 136'd1);
    always_ff @(posedge clk) begin xq1 <= x; r <= q[63:0]; end
endmodule
"""
    red_stub_sv = os.path.join(OUT, "red_stub_ext5.sv")
    open(red_stub_sv, "w").write(red_stub)

    sh(f'yosys -q -p "read_verilog -sv {OUT}/proved_adder_contracts.sv {PKG} {red_stub_sv} {stub_sv} {ext5_sv}; '
       f'hierarchy -top qsag_ext5_mac; proc; flatten; opt_clean; rename -top lec_top; write_smt2 -wires {OUT}/ext5.yosys.smt2"')
    ys_e5 = open(f"{OUT}/ext5.yosys.smt2").read()
    assert ys_e5.count("(bvmul ") == 14, ys_e5.count("(bvmul ")
    assert ys_e5.count("(bvudiv ") == 5, ys_e5.count("(bvudiv ")
    ys_e5_abs = (
        "(declare-fun qmul64 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        "(declare-fun qred136_raw ((_ BitVec 136) (_ BitVec 136)) (_ BitVec 136))\n"
        "(define-fun qred136 ((x (_ BitVec 136))) (_ BitVec 64) "
        "((_ extract 63 0) (qred136_raw x (bvor x (_ bv1 136)))))\n"
        + ys_e5.replace("(bvmul ", "(qmul64 ").replace("(bvudiv ", "(qred136_raw ")
    )

    def bvadd_list(terms):
        res = terms[0]
        for t in terms[1:]:
            res = f"(bvadd {res} {t})"
        return res

    s0_subsets = [
        (0,), (1,), (2,),
        (0, 1), (0, 2), (1, 2),
        (3,), (4,),
        (3, 4), (0, 3), (1, 4),
        (0, 1, 3, 4), (0, 2, 3), (1, 2, 4),
    ]

    def build_stage0_single_query(ys_txt, idx, idxs, is_b=False):
        in_sig = acc("b" if is_b else "a", "s0")
        dbg_port = "dbg_mb" if is_b else "dbg_ma"
        limbs = [f"((_ extract {64*i+63} {64*i}) {in_sig})" for i in range(5)]
        limbs68 = [zext(e, 64, 68) for e in limbs]
        can_in = "(assert (and " + " ".join(f"(bvult {limbs[i]} {bv(P, 64)})" for i in idxs) + "))\n"
        m_val = f"((_ extract {64*idx+63} {64*idx}) {acc(dbg_port, 's1')})"
        m_68 = zext(m_val, 64, 68)
        s_expr = bvadd_list([limbs68[j] for j in idxs])
        alts = " ".join(f"(= {s_expr} (bvadd {m_68} {bv(k * P, 68)}))" for k in range(len(idxs)))
        return ys_txt + unroll(1) + can_in + f"(assert (not (and (bvult {m_val} {bv(P, 64)}) (or {alts}))))\n(check-sat)\n"

    # (a) Stage-0 full pre-sum RTL proof (all 14 ma_q + all 14 mb_q = 28 canonical registers)
    for idx, idxs in enumerate(s0_subsets):
        for is_b, lbl in [(False, "ma"), (True, "mb")]:
            if not record(f"ext5_rtl_stage0_{lbl}{idx}",
                          f"qsag_ext5_mac RTL Stage 0 {lbl}_q[{idx}] {idxs}: < p and equals exact canonical sum mod p",
                          "unsat", build_stage0_single_query(ys_e5_abs, idx, idxs, is_b=is_b), prefer_bitwuzla=False):
                raise SystemExit(f"failed ext5 Stage-0 {lbl}[{idx}] RTL check")

    # (b) Stage-1..6 RTL cut at named pipeline registers `ma_q, mb_q` (proving universal soundness
    # for ALL 2^896 `(ma_q@s1, mb_q@s1)` values without re-unrolling 90 copies of Stage-0 adders!)
    ext5_s16 = ext5_src.replace(
        "output logic [319:0] y",
        "output logic [319:0] y,\n    input logic [13:0][63:0] cut_ma, cut_mb,\n    output logic [4:0][135:0] dbg_acc"
    ).replace(
        ".clk(clk), .a(ma_q[i]), .b(mb_q[i]), .p(m[i]));",
        ".clk(clk), .a(cut_ma[i]), .b(cut_mb[i]), .p(m[i]));"
    ).replace(
        "endmodule",
        "    assign dbg_acc = acc_q;\nendmodule"
    )
    ext5_s16_sv = os.path.join(OUT, "ext5_s16_cut.sv")
    open(ext5_s16_sv, "w").write(ext5_s16)
    sh(f'yosys -q -p "read_verilog -sv {OUT}/proved_adder_contracts.sv {PKG} {red_stub_sv} {stub_sv} {ext5_s16_sv}; '
       f'hierarchy -top qsag_ext5_mac; proc; flatten; opt_clean; rename -top lec_top; write_smt2 -wires {OUT}/ext5_s16.yosys.smt2"')
    ys_s16 = open(f"{OUT}/ext5_s16.yosys.smt2").read()
    assert ys_s16.count("(bvmul ") == 14, ys_s16.count("(bvmul ")
    assert ys_s16.count("(bvudiv ") == 5, ys_s16.count("(bvudiv ")
    ys_s16_abs = (
        "(declare-fun qmul64 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        "(declare-fun qred136_raw ((_ BitVec 136) (_ BitVec 136)) (_ BitVec 136))\n"
        "(define-fun qred136 ((x (_ BitVec 136))) (_ BitVec 64) "
        "((_ extract 63 0) (qred136_raw x (bvor x (_ bv1 136)))))\n"
        + ys_s16.replace("(bvmul ", "(qmul64 ").replace("(bvudiv ", "(qred136_raw ")
    )

    def build_stage4_acc_query(ys_txt, k):
        ma_s1 = [f"((_ extract {64*i+63} {64*i}) {flat_acc('cut_ma', 1)})" for i in range(14)]
        mb_s1 = [f"((_ extract {64*i+63} {64*i}) {flat_acc('cut_mb', 1)})" for i in range(14)]
        m_defs = " ".join(f"(m{i} (qmul64 {zext(ma_s1[i], 64, 128)} {zext(mb_s1[i], 64, 128)}))" for i in range(14))
        pm_defs = " ".join(f"(pm{i} {zext(f'm{i}', 128, 136)})" for i in range(14))
        nm_defs = " ".join(f"(nm{i} {zext(f'(bvnot m{i})', 128, 136)})" for i in range(11))
        c_in = flat_acc("c", 0)
        ck = zext(f"((_ extract {64*k+63} {64*k}) {c_in})", 64, 136)
        def shl1(e): return f"(bvshl {e} {bv(1, 136)})"
        def shl2(e): return f"(bvshl {e} {bv(2, 136)})"
        terms_by_k = [
            [bv(12 * C1, 136), ck, shl2("pm0"), "pm10", shl1("pm10"), "pm12", shl1("pm12"),
             "nm1", shl1("nm1"), "nm4", shl1("nm4"), "nm7", shl1("nm7"), "nm9", shl1("nm9")],
            [bv(7 * C1, 136), ck, "pm3", shl1("pm1"), "pm6", shl1("pm6"), "pm13", shl1("pm13"),
             "nm0", "nm5", shl1("nm5"), "nm10", shl1("nm10")],
            [bv(8 * C1, 136), ck, "pm1", "pm4", "pm8", shl1("pm8"),
             "nm0", "nm2", "nm6", shl1("nm6"), "nm7", shl1("nm7")],
            [bv(4 * C1, 136), ck, "pm5", "pm9", "pm7", shl1("pm7"),
             "nm0", "nm1", "nm2", "nm6"],
            [bv(4 * C1, 136), ck, "pm0", "pm1", "pm2", "pm6", "pm7", "pm11",
             "nm3", "nm8", "nm9", "nm10"],
        ]
        acc_actual = f"((_ extract {136*k+135} {136*k}) {flat_acc('dbg_acc', 5)})"
        acc_spec = bvadd_list(list(reversed(terms_by_k[k])))
        return (flatten_ys_smt2(ys_txt, "lec_top", 5) +
                f"(assert (let ({m_defs}) (let ({pm_defs} {nm_defs}) (not (= {acc_actual} {acc_spec})))))\n"
                "(check-sat)\n")

    for k in range(5):
        if not record(f"ext5_rtl_stage4_acc_limb{k}",
                      f"qsag_ext5_mac RTL Stage 1..4: dbg_acc[{k}]@s5 == exact 136-bit Karatsuba combination of c_{k}@s0 and m[0..13]",
                      "unsat", build_stage4_acc_query(ys_s16_abs, k), prefer_bitwuzla=True):
            raise SystemExit(f"failed ext5 Stage-4 acc limb {k} RTL check")

    # (c1) Stage-5..6 7-cycle RTL reduction join: y[64*k +: 64]@s7 == qred136(dbg_acc[k]@s5)
    red_clauses = [
        f"(= ((_ extract {64*k+63} {64*k}) {flat_acc('y', 7)}) (qred136 ((_ extract {136*k+135} {136*k}) {flat_acc('dbg_acc', 5)})))"
        for k in range(5)
    ]
    if not record("ext5_rtl_stage6_red_join",
                  "qsag_ext5_mac 7-cycle RTL Stage 5..6: y[64*k +: 64]@s7 == qred136(dbg_acc[k]@s5) for all k=0..4",
                  "unsat", flatten_ys_smt2(ys_s16_abs, "lec_top", 7) + "(assert (not (and " + " ".join(red_clauses) + ")))\n(check-sat)\n",
                  prefer_bitwuzla=True):
        raise SystemExit("failed ext5 Stage-6 RTL reduction join")

    # (c2) End-to-end Modus Ponens glue (Stage-0..4 QF_NIA ring link + Stage-4..6 QF_LIA Euclidean reduction) for each limb k = 0..4
    subset_idx_map = {
        "01": (3, "(+ a0 a1)", "(+ b0 b1)", 2),
        "02": (4, "(+ a0 a2)", "(+ b0 b2)", 2),
        "12": (5, "(+ a1 a2)", "(+ b1 b2)", 2),
        "34": (8, "(+ a3 a4)", "(+ b3 b4)", 2),
        "03": (9, "(+ a0 a3)", "(+ b0 b3)", 2),
        "14": (10, "(+ a1 a4)", "(+ b1 b4)", 2),
        "0134": (11, "(+ a0 a1 a3 a4)", "(+ b0 b1 b3 b4)", 4),
        "023": (12, "(+ a0 a2 a3)", "(+ b0 b2 b3)", 3),
        "124": (13, "(+ a1 a2 a4)", "(+ b1 b2 b4)", 3),
    }
    direct_map = [(0, "a0", "b0"), (1, "a1", "b1"), (2, "a2", "b2"), (6, "a3", "b3"), (7, "a4", "b4")]
    if not record("ext5_mul64_prod_range",
                  "Ext5 Stage-1..3 product bound: 0 <= ma, mb < p implies 0 <= ma * mb < 2^128",
                  "unsat",
                  f"(declare-const ma Int) (declare-const mb Int)\n"
                  f"(assert (and (<= 0 ma) (< ma {P}) (<= 0 mb) (< mb {P})))\n"
                  f"(assert (not (and (<= 0 (* ma mb)) (< (* ma mb) {2**128}))))\n(check-sat)\n"):
        raise SystemExit("failed ext5 mul64 range")

    for k in range(5):
        s04_decl = (
            "".join(f"(declare-const a{i} Int) (declare-const b{i} Int) (declare-const c{i} Int)\n" for i in range(5))
            + "".join(f"(declare-const ka_{s} Int) (declare-const kb_{s} Int)\n" for s, _, _ in subsets)
        )
        s04_defs = ""
        for idx, av, bv_name in direct_map:
            s04_defs += f"(define-fun ma{idx} () Int {av})\n(define-fun mb{idx} () Int {bv_name})\n"
        for s, (idx, sa, sb_e, _nterms) in subset_idx_map.items():
            s04_defs += (
                f"(define-fun ma{idx} () Int (- {sa} (* {P} ka_{s})))\n"
                f"(define-fun mb{idx} () Int (- {sb_e} (* {P} kb_{s})))\n"
            )
        for i in range(14):
            s04_defs += f"(define-fun m{i} () Int (* ma{i} mb{i}))\n"
        s04_defs += (
            f"(define-fun acc () Int {accs_r[k]})\n"
            f"(define-fun sb () Int {sbs[k]})\n"
            f"(define-fun Q () Int {qs[k]})\n"
        )
        s04_goal = f"(assert (not (= (- acc sb) (* {P} Q))))\n(check-sat)\n"
        if not record(f"ext5_stage04_link_limb{k}",
                      f"Ext5 limb {k} Stage-0..4 ring link: Stage-0 ma/mb + Stage-3 m_i + Stage-4 acc entail acc - sb == p * Q_{k}",
                      "unsat", s04_decl + s04_defs + s04_goal):
            raise SystemExit(f"failed ext5 Stage-0..4 link limb {k}")

        mp_q = (
            "(declare-const acc Int) (declare-const sb Int) (declare-const Q Int) (declare-const y Int) (declare-const rk Int)\n"
            f"(assert (and (< 0 acc) (< acc {2**136}) (= (- acc sb) (* {P} Q))))\n"
            f"(assert (and (<= 0 y) (< y {P}) (= acc (+ y (* rk {P})))))\n"
            f"(assert (not (= y (mod sb {P}))))\n(check-sat)\n"
        )
        if not record(f"ext5_end_to_end_glue_limb{k}",
                      f"Ext5 limb {k} end-to-end Modus Ponens: Stage-0..6 + range contracts entail y_{k} == schoolbook_{k}(a,b,c) mod p",
                      "unsat", mp_q):
            raise SystemExit(f"failed ext5 end-to-end glue limb {k}")

    # (d) 3 Mutant teeth (`sat`):
    # Mutant 1: Stage-0 wire fault in p4_in ({a4, a3, a1, a0} -> {a4, a3, a2, a0})
    m_s0 = mutate(ext5_sv, "{a4,    a3, a1, a0}", "{a4,    a3, a2, a0}", "mut_ext5_s0.sv")
    sh(f'yosys -q -p "read_verilog -sv {OUT}/proved_adder_contracts.sv {PKG} {red_stub_sv} {stub_sv} {m_s0}; '
       f'hierarchy -top qsag_ext5_mac; proc; flatten; opt_clean; rename -top lec_top; write_smt2 -wires {OUT}/mut_ext5_s0.yosys.smt2"')
    ys_ms0 = open(f"{OUT}/mut_ext5_s0.yosys.smt2").read()
    ys_ms0_abs = (
        "(declare-fun qmul64 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        "(declare-fun qred136_raw ((_ BitVec 136) (_ BitVec 136)) (_ BitVec 136))\n"
        + ys_ms0.replace("(bvmul ", "(qmul64 ").replace("(bvudiv ", "(qred136_raw ")
    )
    if not record("mut_ext5_stage0_wire", "mutant tooth: Stage-0 p4_in wire swap (a1->a2) in qsag_ext5_mac is refuted",
                  "sat", build_stage0_single_query(ys_ms0_abs, 11, s0_subsets[11], is_b=False), prefer_bitwuzla=False):
        raise SystemExit("failed ext5 Stage-0 mutant")

    # Mutant 2: Stage-4 `pm[0] << 2` -> `pm[0] << 1` in `t_y0`
    m_e5 = mutate(ext5_s16_sv, "136'(12) * C1, 136'(c0), pm[0] << 2,", "136'(12) * C1, 136'(c0), pm[0] << 1,", "mut_ext5.sv")
    sh(f'yosys -q -p "read_verilog -sv {OUT}/proved_adder_contracts.sv {PKG} {red_stub_sv} {stub_sv} {m_e5}; '
       f'hierarchy -top qsag_ext5_mac; proc; flatten; opt_clean; rename -top lec_top; write_smt2 -wires {OUT}/mut_ext5.yosys.smt2"')
    ys_me5 = open(f"{OUT}/mut_ext5.yosys.smt2").read()
    ys_me5_abs = (
        "(declare-fun qmul64 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        "(declare-fun qred136_raw ((_ BitVec 136) (_ BitVec 136)) (_ BitVec 136))\n"
        + ys_me5.replace("(bvmul ", "(qmul64 ").replace("(bvudiv ", "(qred136_raw ")
    )
    if not record("mut_ext5_mac_y0_coeff", "mutant tooth: wrong 4*m0 weight in qsag_ext5_mac Stage-4 t_y0 is refuted",
                  "sat", build_stage4_acc_query(ys_me5_abs, 0), prefer_bitwuzla=True):
        raise SystemExit("failed ext5 mutant 2")

    # Mutant 3: Stage-4 limb 4 swaps c4 -> c3 in t_y4
    m_s6 = mutate(ext5_s16_sv, "136'(4) * C1, 136'(c4),", "136'(4) * C1, 136'(c3),", "mut_ext5_s6.sv")
    sh(f'yosys -q -p "read_verilog -sv {OUT}/proved_adder_contracts.sv {PKG} {red_stub_sv} {stub_sv} {m_s6}; '
       f'hierarchy -top qsag_ext5_mac; proc; flatten; opt_clean; rename -top lec_top; write_smt2 -wires {OUT}/mut_ext5_s6.yosys.smt2"')
    ys_ms6 = open(f"{OUT}/mut_ext5_s6.yosys.smt2").read()
    ys_ms6_abs = (
        "(declare-fun qmul64 ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        "(declare-fun qred136_raw ((_ BitVec 136) (_ BitVec 136)) (_ BitVec 136))\n"
        + ys_ms6.replace("(bvmul ", "(qmul64 ").replace("(bvudiv ", "(qred136_raw ")
    )
    if not record("mut_ext5_stage6_limb", "mutant tooth: wrong c4->c3 carry in qsag_ext5_mac Stage-4 t_y4 is refuted",
                  "sat", build_stage4_acc_query(ys_ms6_abs, 4), prefer_bitwuzla=True):
        raise SystemExit("failed ext5 mutant 3")

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

def clmul_spec_expr(a, b, w):
    pw = 2 * w - 1
    e = bv(0, pw)
    for i in range(w):
        e = f"(bvxor {e} (ite (= ((_ extract {i} {i}) {b}) #b1) (bvshl {zext(a, w, pw)} {bv(i, pw)}) {bv(0, pw)}))"
    return e

def check_gf_mul(tag, files, expect, required=True, secs=None):
    ys = yosys_smt2(tag, "qsag_gf128_clmul", files, use_contracts=False)
    a, b = acc("a", "s0"), acc("b", "s0")
    stmt = "qsag_gf128_clmul: for all 2^256 inputs, r (3 clocks later) = a*b in GF(2^128)"
    return record(tag, stmt, expect, ys + unroll(3) + f"(assert (not (= {acc('r', 's3')} {gf_mul_spec(a, b)})))\n(check-sat)\n",
                  required=required, secs=secs)

def check_gf_mul_basis(tag, files, j, expect, required=True, secs=None):
    ys = yosys_smt2(tag, "qsag_gf128_clmul", files, use_contracts=False)
    a, b, r3 = acc("a", "s0"), acc("b", "s0"), acc("r", "s3")
    xp = gf_xpow()
    bit_eqs = []
    for k in range(128):
        bits = [f"(= ((_ extract {i} {i}) {a}) #b1)" for i in range(128) if (xp[i + j] >> k) & 1]
        rhs_k = "false" if not bits else (bits[0] if len(bits) == 1 else "(xor " + " ".join(bits) + ")")
        bit_eqs.append(f"(= (= ((_ extract {k} {k}) {r3}) #b1) {rhs_k})")
    return record(tag, f"qsag_gf128_clmul: for all a and b = x^{j}, r (3 clocks later) = a * x^{j}", expect,
                  ys + unroll(3) + f"(assert (= {b} {bv(1 << j, 128)}))\n"
                  f"(assert (not (and {' '.join(bit_eqs)})))\n(check-sat)\n",
                  required=required, secs=secs, prefer_bitwuzla=False)

def group_gf():
    check_gf_reduce("gf128_reduce", [GFRED], "unsat")
    m5 = mutate(GFRED, "(134'(hi) << 7)", "(134'(hi) << 6)", "mut_gf_reduce.sv")
    check_gf_reduce("mut_gf128_reduce_tap", [m5], "sat")
    m6 = mutate(KARA, "assign xmid = mid ^ hi ^ (2*HH-1)'(lo);", "assign xmid = mid ^ hi;", "mut_kara.sv")
    check_gf_mul("mut_gf128_clmul_kara", [m6, GFRED, GFMUL], "sat")
    check_gf_mul_basis("mut_gf128_clmul_basis_x77", [m6, GFRED, GFMUL], 77, "sat")

def group_comp():
    """Compositional cut-lemma closure of all 6 formerly `open / timeout` obligations:
      1) `clmul_kara_w8_base` + mutant `sat` on exact RTL;
      2) `clmul_spec` GF(2)[x] row-split, bilinearity, and Karatsuba algebra lemmas for W = 16, 32, 64, 128;
      3) Inductive `qsag_clmul_kara` RTL step proofs for W = 16, 32, 64, 128 + W=16 mutant `sat`;
      4) Basis checks `b = x^0` and `b = x^77` on unabstracted `qsag_gf128_clmul` RTL;
      5) 3-cycle `qsag_gf128_clmul` temporal join + inductive Horner vs polynomial-mod equivalence."""
    # 1. Base case W = 8 on full `qsag_clmul_kara` RTL + mutant
    ys8 = yosys_smt2("comp_kara_w8", "qsag_clmul_kara", [KARA], "-chparam W 8 -chparam BASE 8", use_contracts=False)
    e8 = clmul_spec_expr(acc("a", "s0"), acc("b", "s0"), 8)
    if not record("comp_clmul_kara_w8_base",
                  "qsag_clmul_kara W=8 base RTL: p == clmul_spec(a, b) for all 2^16 inputs",
                  "unsat", ys8 + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
                  f"(assert (not (= {acc('p','s0')} {e8})))\n(check-sat)\n", prefer_bitwuzla=True):
        raise SystemExit("failed W=8 clmul base")
    m_k8 = mutate(KARA, "({(2*W-1){b[i]}} & (2*W-1)'(a)) << i", "({(2*W-1){b[i]}} & (2*W-1)'(a)) << (i == 7 ? 6 : i)", "mut_kara_w8.sv")
    ys8m = yosys_smt2("mut_comp_kara_w8", "qsag_clmul_kara", [m_k8], "-chparam W 8 -chparam BASE 8", use_contracts=False)
    if not record("mut_clmul_kara_w8_base", "mutant tooth: shift fault in qsag_clmul_kara W=8 base is refuted",
                  "sat", ys8m + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
                  f"(assert (not (= {acc('p','s0')} {e8})))\n(check-sat)\n", prefer_bitwuzla=True):
        raise SystemExit("failed W=8 clmul mutant")

    # 2 & 3. Inductive Karatsuba step on actual `qsag_clmul_kara` RTL + `clmul_spec` bilinearity/split for W = 16, 32, 64, 128
    kara_src = open(KARA).read()
    for w in (16, 32, 64, 128):
        h = w // 2
        pw = 2 * w - 1
        ph = 2 * h - 1
        # 2a-1. Inductive 4-quadrant schoolbook decomposition of `clmul_spec_W` over shift j in [0, H)
        row_q = f"""(set-logic QF_BV)
(declare-const a0 (_ BitVec {h})) (declare-const a1 (_ BitVec {h}))
(declare-const b0j (_ BitVec 1))  (declare-const b1j (_ BitVec 1))
(declare-const s (_ BitVec 8))
(declare-const acc00 (_ BitVec {ph})) (declare-const acc10 (_ BitVec {ph}))
(declare-const acc01 (_ BitVec {ph})) (declare-const acc11 (_ BitVec {ph}))
(declare-const acclo (_ BitVec {pw})) (declare-const acchi (_ BitVec {pw}))
(assert (bvult s {bv(h, 8)}))
(assert (= acclo (bvxor {zext('acc00', ph, pw)} (bvshl {zext('acc10', ph, pw)} {bv(h, pw)}))))
(assert (= acchi (bvxor (bvshl {zext('acc01', ph, pw)} {bv(h, pw)}) (bvshl {zext('acc11', ph, pw)} {bv(2*h, pw)}))))
(define-fun sh_ph () (_ BitVec {ph}) {zext('s', 8, ph)})
(define-fun sh_pw () (_ BitVec {pw}) {zext('s', 8, pw)})
(define-fun sh_hi () (_ BitVec {pw}) (bvadd sh_pw {bv(h, pw)}))
(define-fun a_cat () (_ BitVec {pw}) {zext('(concat a1 a0)', w, pw)})
(define-fun n00 () (_ BitVec {ph}) (bvxor acc00 (ite (= b0j #b1) (bvshl {zext('a0', h, ph)} sh_ph) {bv(0, ph)})))
(define-fun n10 () (_ BitVec {ph}) (bvxor acc10 (ite (= b0j #b1) (bvshl {zext('a1', h, ph)} sh_ph) {bv(0, ph)})))
(define-fun n01 () (_ BitVec {ph}) (bvxor acc01 (ite (= b1j #b1) (bvshl {zext('a0', h, ph)} sh_ph) {bv(0, ph)})))
(define-fun n11 () (_ BitVec {ph}) (bvxor acc11 (ite (= b1j #b1) (bvshl {zext('a1', h, ph)} sh_ph) {bv(0, ph)})))
(define-fun nlo () (_ BitVec {pw}) (bvxor acclo (ite (= b0j #b1) (bvshl a_cat sh_pw) {bv(0, pw)})))
(define-fun nhi () (_ BitVec {pw}) (bvxor acchi (ite (= b1j #b1) (bvshl a_cat sh_hi) {bv(0, pw)})))
(define-fun q_join () (_ BitVec {pw})
  (bvxor {zext('n00', ph, pw)}
         (bvxor (bvshl {zext('(bvxor n10 n01)', ph, pw)} {bv(h, pw)})
                (bvshl {zext('n11', ph, pw)} {bv(2*h, pw)}))))
(assert (not (and
  (= nlo (bvxor {zext('n00', ph, pw)} (bvshl {zext('n10', ph, pw)} {bv(h, pw)})))
  (= nhi (bvxor (bvshl {zext('n01', ph, pw)} {bv(h, pw)}) (bvshl {zext('n11', ph, pw)} {bv(2*h, pw)})))
  (= (bvxor nlo nhi) q_join))))
(check-sat)
"""
        if not record(f"comp_clmul_row_split_w{w}",
                      f"GF(2)[x] inductive 4-quadrant schoolbook decomposition clmul_{w}(a,b) -> 4 x clmul_{h}",
                      "unsat", row_q, prefer_bitwuzla=True):
            raise SystemExit(f"failed clmul row split W={w}")

        # 2a-2. Inductive bilinearity of `clmul_spec_H` over shift j in [0, H)
        bilin_q = f"""(set-logic QF_BV)
(declare-const x0 (_ BitVec {h})) (declare-const x1 (_ BitVec {h}))
(declare-const y0j (_ BitVec 1))  (declare-const y1j (_ BitVec 1))
(declare-const s (_ BitVec 8))
(declare-const ax0 (_ BitVec {ph})) (declare-const ax1 (_ BitVec {ph})) (declare-const asx (_ BitVec {ph}))
(declare-const ay0 (_ BitVec {ph})) (declare-const ay1 (_ BitVec {ph})) (declare-const asy (_ BitVec {ph}))
(assert (bvult s {bv(h, 8)}))
(assert (= asx (bvxor ax0 ax1)))
(assert (= asy (bvxor ay0 ay1)))
(define-fun sh () (_ BitVec {ph}) {zext('s', 8, ph)})
(define-fun sx () (_ BitVec {h}) (bvxor x0 x1))
(define-fun syj () (_ BitVec 1) (bvxor y0j y1j))
(define-fun nx0 () (_ BitVec {ph}) (bvxor ax0 (ite (= y0j #b1) (bvshl {zext('x0', h, ph)} sh) {bv(0, ph)})))
(define-fun nx1 () (_ BitVec {ph}) (bvxor ax1 (ite (= y0j #b1) (bvshl {zext('x1', h, ph)} sh) {bv(0, ph)})))
(define-fun nsx () (_ BitVec {ph}) (bvxor asx (ite (= y0j #b1) (bvshl {zext('sx', h, ph)} sh) {bv(0, ph)})))
(define-fun ny0 () (_ BitVec {ph}) (bvxor ay0 (ite (= y0j #b1) (bvshl {zext('x0', h, ph)} sh) {bv(0, ph)})))
(define-fun ny1 () (_ BitVec {ph}) (bvxor ay1 (ite (= y1j #b1) (bvshl {zext('x0', h, ph)} sh) {bv(0, ph)})))
(define-fun nsy () (_ BitVec {ph}) (bvxor asy (ite (= syj #b1) (bvshl {zext('x0', h, ph)} sh) {bv(0, ph)})))
(assert (not (and (= nsx (bvxor nx0 nx1)) (= nsy (bvxor ny0 ny1)))))
(check-sat)
"""
        if not record(f"comp_clmul_bilin_h{h}",
                      f"GF(2)[x] inductive bilinearity of clmul_{h} in both operands over all shifts s < {h}",
                      "unsat", bilin_q, prefer_bitwuzla=True):
            raise SystemExit(f"failed clmul bilinearity H={h}")

        # 2a-3. Karatsuba identity over ANY bilinear `f : BV(H) x BV(H) -> BV(2H-1)`
        kalg_q = f"""(set-logic QF_UFBV)
(declare-fun f ((_ BitVec {h}) (_ BitVec {h})) (_ BitVec {ph}))
(declare-const a0 (_ BitVec {h})) (declare-const a1 (_ BitVec {h}))
(declare-const b0 (_ BitVec {h})) (declare-const b1 (_ BitVec {h}))
(define-fun sa () (_ BitVec {h}) (bvxor a1 a0))
(define-fun sb () (_ BitVec {h}) (bvxor b1 b0))
(assert (= (f sa sb) (bvxor (f a1 sb) (f a0 sb))))
(assert (= (f a1 sb) (bvxor (f a1 b1) (f a1 b0))))
(assert (= (f a0 sb) (bvxor (f a0 b1) (f a0 b0))))
(define-fun lo () (_ BitVec {ph}) (f a0 b0))
(define-fun hi () (_ BitVec {ph}) (f a1 b1))
(define-fun mid () (_ BitVec {ph}) (f sa sb))
(define-fun quad () (_ BitVec {pw})
  (bvxor {zext('lo', ph, pw)}
         (bvxor (bvshl {zext('(bvxor (f a1 b0) (f a0 b1))', ph, pw)} {bv(h, pw)})
                (bvshl {zext('hi', ph, pw)} {bv(2*h, pw)}))))
(define-fun kara () (_ BitVec {pw})
  (bvxor {zext('lo', ph, pw)}
         (bvxor (bvshl {zext('hi', ph, pw)} {bv(2*h, pw)})
                (bvshl {zext('(bvxor mid (bvxor hi lo))', ph, pw)} {bv(h, pw)}))))
(assert (not (= quad kara)))
(check-sat)
"""
        if not record(f"comp_clmul_spec_split_w{w}",
                      f"GF(2)[x] Karatsuba recombination lemma W={w} (from bilinear H={h})",
                      "unsat", kalg_q, prefer_bitwuzla=True):
            raise SystemExit(f"failed clmul_spec split W={w}")

        # 2b. Prove on actual `qsag_clmul_kara` outer RTL (replacing recursive `u_lo, u_hi, u_mid` with uninterpreted `qclmul_h`)
        step_txt = kara_src.replace("module qsag_clmul_kara #(", "module qsag_clmul_step #(", 1)
        step_txt = step_txt.replace("qsag_clmul_kara #(.W(H),  .BASE(BASE)) u_lo",  "qsag_clmul_child #(.W(H)) u_lo")
        step_txt = step_txt.replace("qsag_clmul_kara #(.W(HH), .BASE(BASE)) u_hi",  "qsag_clmul_child #(.W(HH)) u_hi")
        step_txt = step_txt.replace("qsag_clmul_kara #(.W(HH), .BASE(BASE)) u_mid", "qsag_clmul_child #(.W(HH)) u_mid")
        step_txt += f"""
module qsag_clmul_child #(parameter int W={h}) (input logic [W-1:0] a, input logic [W-1:0] b, output logic [2*W-2:0] p);
    assign p = (2*W-1)'(a) * (2*W-1)'(b);
endmodule
"""
        step_sv = os.path.join(OUT, f"kara_step_w{w}.sv")
        open(step_sv, "w").write(step_txt)
        ys_st = yosys_smt2(f"kara_step_w{w}", "qsag_clmul_step", [step_sv], f"-chparam W {w} -chparam BASE 8", use_contracts=False)
        assert ys_st.count("(bvmul ") == 3
        ys_abs = f"(declare-fun qclmul ((_ BitVec {ph}) (_ BitVec {ph})) (_ BitVec {ph}))\n" + ys_st.replace("(bvmul ", "(qclmul ")
        aw_e, bw_e = acc("a", "s0"), acc("b", "s0")
        a0_p = zext(f"((_ extract {h-1} 0) {aw_e})", h, ph)
        a1_p = zext(f"((_ extract {w-1} {h}) {aw_e})", h, ph)
        b0_p = zext(f"((_ extract {h-1} 0) {bw_e})", h, ph)
        b1_p = zext(f"((_ extract {w-1} {h}) {bw_e})", h, ph)
        as_p = zext(f"(bvxor ((_ extract {w-1} {h}) {aw_e}) ((_ extract {h-1} 0) {aw_e}))", h, ph)
        bs_p = zext(f"(bvxor ((_ extract {w-1} {h}) {bw_e}) ((_ extract {h-1} 0) {bw_e}))", h, ph)
        lo_e = f"(qclmul {a0_p} {b0_p})"
        hi_e = f"(qclmul {a1_p} {b1_p})"
        mid_e = f"(qclmul {as_p} {bs_p})"
        rhs_e = (f"(bvxor {zext(lo_e, ph, pw)} "
                 f"(bvxor (bvshl {zext(hi_e, ph, pw)} {bv(2*h, pw)}) "
                 f"(bvshl {zext(f'(bvxor {mid_e} (bvxor {hi_e} {lo_e}))', ph, pw)} {bv(h, pw)})))")
        if not record(f"comp_clmul_kara_w{w}_step",
                      f"qsag_clmul_kara W={w} inductive RTL step (from proved H={h}): p == clmul_spec(a, b) for all 2^{2*w} inputs",
                      "unsat", ys_abs + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
                      f"(assert (not (= {acc('p','s0')} {rhs_e})))\n(check-sat)\n", prefer_bitwuzla=True):
            raise SystemExit(f"failed qsag_clmul_kara inductive step W={w}")

        if w == 16:
            mut_st = mutate(step_sv, "assign xmid = mid ^ hi ^ (2*HH-1)'(lo);", "assign xmid = mid ^ hi;", "mut_kara_step_w16.sv")
            ys_mst = yosys_smt2("mut_kara_step_w16", "qsag_clmul_step", [mut_st], "-chparam W 16 -chparam BASE 8", use_contracts=False)
            ys_mabs = f"(declare-fun qclmul ((_ BitVec {ph}) (_ BitVec {ph})) (_ BitVec {ph}))\n" + ys_mst.replace("(bvmul ", "(qclmul ")
            if not record("mut_comp_clmul_kara_w16", "mutant tooth: dropped lo term in qsag_clmul_kara W=16 step is refuted",
                          "sat", ys_mabs + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
                          f"(assert (not (= {acc('p','s0')} {rhs_e})))\n(check-sat)\n", prefer_bitwuzla=True):
                raise SystemExit("failed W=16 mutant")

    # 4. Basis checks `b = x^0` and `b = x^77` directly on unabstracted `qsag_gf128_clmul` RTL (Z3 GF(2) Gaussian elimination!)
    if not check_gf_mul_basis("comp_gf128_clmul_basis_x0", [KARA, GFRED, GFMUL], 0, "unsat"):
        raise SystemExit("failed basis x^0")
    if not check_gf_mul_basis("comp_gf128_clmul_basis_x77", [KARA, GFRED, GFMUL], 77, "unsat"):
        raise SystemExit("failed basis x^77")

    # 5a. 3-cycle `qsag_gf128_clmul` temporal pipeline join on RTL over proved `qsag_clmul_kara` (W=128) & `qsag_gf128_reduce`
    gfm_rel = open(GFMUL).read().replace(
        "qsag_clmul_kara #(.W(128), .BASE(BASE)) u_mul (.a(a_q), .b(b_q), .p(prod));",
        "qsag_clmul_uf u_mul (.a(a_q), .b(b_q), .p(prod));"
    ).replace(
        "qsag_gf128_reduce u_red (.c(prod_q), .r(red));",
        "qsag_gfred_uf u_red (.c(prod_q), .r(red));"
    ) + """
module qsag_clmul_uf (input logic [127:0] a, input logic [127:0] b, output logic [254:0] p);
    assign p = 255'(a) * 255'(b);
endmodule
module qsag_gfred_uf (input logic [254:0] c, output logic [127:0] r);
    assign r = c[127:0] - c[254:127];
endmodule
"""
    gfm_sv = os.path.join(OUT, "gf128_clmul_rel.sv")
    open(gfm_sv, "w").write(gfm_rel)
    ys_gfm = yosys_smt2("comp_gf128_pipe", "qsag_gf128_clmul", [gfm_sv], use_contracts=False)
    assert ys_gfm.count("(bvmul ") == 1 and ys_gfm.count("(bvsub ") == 1
    ys_gfm_abs = (
        "(declare-fun uclmul ((_ BitVec 255) (_ BitVec 255)) (_ BitVec 255))\n"
        "(declare-fun ugfred ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        + ys_gfm.replace("(bvmul ", "(uclmul ").replace("(bvsub ", "(ugfred ")
    )
    a0_255 = zext(acc("a", "s0"), 128, 255)
    b0_255 = zext(acc("b", "s0"), 128, 255)
    pr_255 = f"(uclmul {a0_255} {b0_255})"
    pipe_rhs = f"(ugfred ((_ extract 127 0) {pr_255}) ((_ extract 254 127) {pr_255}))"
    if not record("comp_gf128_clmul_pipe_rtl",
                  "3-cycle qsag_gf128_clmul RTL pipeline join: r@s3 == qsag_gf128_reduce(qsag_clmul_kara(a@s0, b@s0))",
                  "unsat", ys_gfm_abs + unroll(3) + f"(assert (not (= {acc('r','s3')} {pipe_rhs})))\n(check-sat)\n",
                  prefer_bitwuzla=True):
        raise SystemExit("failed gf128_clmul 3-cycle pipeline RTL join")

    # 5b. Inductive equivalence between `gf_reduce_spec(clmul_spec_128(a, b))` and 128-step Horner `gf_mul_spec(a, b)`
    xp = gf_xpow()
    def gfred_expr(v255):
        e = f"((_ extract 127 0) {v255})"
        for i in range(128, 255):
            e = f"(bvxor {e} (ite (= ((_ extract {i} {i}) {v255}) #b1) {bv(xp[i], 128)} {bv(0, 128)}))"
        return e

    horner_q = f"""(set-logic QF_BV)
(declare-const u (_ BitVec 254))
(declare-const a (_ BitVec 128))
(declare-const bit (_ BitVec 1))
(define-fun u0 () (_ BitVec 255) {zext('u', 254, 255)})
(define-fun acc () (_ BitVec 128) {gfred_expr('u0')})
(define-fun xtime_acc () (_ BitVec 128)
  (bvxor (bvshl acc {bv(1, 128)}) (ite (= ((_ extract 127 127) acc) #b1) {bv(0x87, 128)} {bv(0, 128)})))
(define-fun h_next () (_ BitVec 128)
  (bvxor xtime_acc (ite (= bit #b1) a {bv(0, 128)})))
(define-fun u_next () (_ BitVec 255)
  (bvxor (bvshl u0 {bv(1, 255)}) (ite (= bit #b1) {zext('a', 128, 255)} {bv(0, 255)})))
(assert (not (and
  (= {gfred_expr(bv(0, 255))} {bv(0, 128)})
  (= h_next {gfred_expr('u_next')}))))
(check-sat)
"""
    if not record("comp_gf128_clmul_end_to_end",
                  "Horner-step & polynomial-mod inductive equivalence -> r@s3 == gf_mul_spec(a,b) over all 2^256 inputs",
                  "unsat", horner_q, prefer_bitwuzla=True):
        raise SystemExit("failed composed gf128_clmul Horner equivalence")

def group_tower():
    """Universal Z3 equivalence of Wiedemann tower128 linear maps, round-trip bijection on RTL,
    Artin-Schreier tower generator defining identities through 3-cycle RTL, Lean KATs, and mutant."""
    fixture_path = os.environ.get("QSAG_FIXTURE",
                                  os.path.join(ROOT, "../../validation/tests/fixtures/lean_external_oracle_vectors.json"))
    repo_cand = os.environ.get("QSAG_REPO", os.path.join(ROOT, "../.."))
    if not os.path.exists(os.path.join(repo_cand, "crates/qsag-asm/src/portable.rs")):
        repo_cand = "/home/build/qsag-ni-fpga/work/astra/repo"
    rows, inv, cols, ic, _ = G.matrices(Path(repo_cand))

    def parity_bool(x, mask):
        bits = [f"(= ((_ extract {i} {i}) {x}) #b1)" for i in range(128) if (mask >> i) & 1]
        return "false" if not bits else (bits[0] if len(bits) == 1 else "(xor " + " ".join(bits) + ")")

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

    m_tow = mutate(TMAP, "128'hd353a5afc268871ad268eb72003a04ad",
                   "128'hd353a5afc268871ad268eb72003a04ac", "mut_tower_map.sv")
    ys_mt = yosys_smt2("mut_tower_map", "qsag_gf128_tower_map", [m_tow], "-chparam INVERSE 0", use_contracts=False)
    assertions0 = [f"(= (= ((_ extract {i} {i}) {acc('y','s0')}) #b1) {parity_bool(acc('x','s0'), m)})"
                   for i, m in enumerate(rows)]
    if not record("mut_tower_map_bitflip", "mutant tooth: 1-bit mask flip in qsag_gf128_tower_map is refuted",
                  "sat", ys_mt + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
                  "(assert (not (and " + " ".join(assertions0) + ")))\n(check-sat)\n"):
        raise SystemExit("failed tower mutant")

    # Universal 2^256-input compositional RTL proof of `qsag_gf128_tower_mul` + mutant
    tm_stubs = os.path.join(OUT, "tower_mul_stubs.sv")
    open(tm_stubs, "w").write("""
module qsag_gf128_tower_map #(parameter bit INVERSE = 1'b0) (input logic [127:0] x, output logic [127:0] y);
    if (INVERSE) begin : g_inv
        assign y = x - 128'd7;
    end else begin : g_fwd
        assign y = x + 128'd5;
    end
endmodule
module qsag_gf128_clmul #(parameter int BASE = 8) (input logic clk, input logic [127:0] a, b, output logic [127:0] r);
    logic [127:0] aq0, aq1, bq0, bq1;
    always_ff @(posedge clk) begin aq0 <= a; aq1 <= aq0; bq0 <= b; bq1 <= bq0; r <= aq1 * bq1; end
endmodule
""")
    ys_tmw = yosys_smt2("tower_mul_wrap", "qsag_gf128_tower_mul", [tm_stubs, TMUL], use_contracts=False)
    assert ys_tmw.count("(bvadd ") == 2 and ys_tmw.count("(bvsub ") == 1 and ys_tmw.count("(bvmul ") == 1
    ys_tmw_abs = (
        "(declare-fun utow_fwd ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        "(declare-fun utow_inv ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        "(declare-fun ugfmul ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        + ys_tmw.replace("(bvadd ", "(utow_fwd ").replace("(bvsub ", "(utow_inv ").replace("(bvmul ", "(ugfmul ")
    )
    tm_rhs = f"(utow_inv (ugfmul (utow_fwd {flat_acc('a', 0)} {bv(5, 128)}) (utow_fwd {flat_acc('b', 0)} {bv(5, 128)})) {bv(7, 128)})"
    if not record("tower_mul_rtl_universal",
                  "qsag_gf128_tower_mul: for all 2^256 (a,b), 3-cycle RTL == tower_inv(clmul(tower_fwd(a), tower_fwd(b)))",
                  "unsat", flatten_ys_smt2(ys_tmw_abs, "lec_top", 3) + f"(assert (not (= {flat_acc('r', 3)} {tm_rhs})))\n(check-sat)\n",
                  prefer_bitwuzla=True):
        raise SystemExit("failed universal tower_mul RTL wrapper proof")

    m_tmul = mutate(TMUL, "qsag_gf128_tower_map #(.INVERSE(1)) u_r", "qsag_gf128_tower_map #(.INVERSE(0)) u_r", "mut_tower_mul.sv")
    ys_mtmw = yosys_smt2("mut_tower_mul_wrap", "qsag_gf128_tower_mul", [tm_stubs, m_tmul], use_contracts=False)
    ys_mtmw_abs = (
        "(declare-fun utow_fwd ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        "(declare-fun utow_inv ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        "(declare-fun ugfmul ((_ BitVec 128) (_ BitVec 128)) (_ BitVec 128))\n"
        + ys_mtmw.replace("(bvadd ", "(utow_fwd ").replace("(bvsub ", "(utow_inv ").replace("(bvmul ", "(ugfmul ")
    )
    if not record("mut_tower_mul_inv", "mutant tooth: wrong INVERSE=0 output map in qsag_gf128_tower_mul is refuted",
                  "sat", flatten_ys_smt2(ys_mtmw_abs, "lec_top", 3) + f"(assert (not (= {flat_acc('r', 3)} {tm_rhs})))\n(check-sat)\n",
                  prefer_bitwuzla=True):
        raise SystemExit("failed tower_mul mutant")

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

GROUPS = {
    "gl": group_gl,
    "glmut": group_glmut,
    "ext5": group_ext5,
    "gf": group_gf,
    "comp": group_comp,
    "tower": group_tower,
}

def main():
    os.makedirs(OUT, exist_ok=True)
    groups = sys.argv[1:] or ["gl", "glmut", "ext5", "gf", "comp", "tower"]
    for g in groups:
        del results[:]
        GROUPS[g]()
        with open(os.path.join(OUT, f"results_{g}.txt"), "w") as f:
            for tag, name, stmt, exp, ans, dt in results:
                f.write(f"{tag}\t{name}\t{exp}\t{ans}\t{dt:.1f}s\t{stmt}\n")
        bad = [r for r in results if r[0] != "PASS"]
        print(f"LEC {g}: {sum(r[0] == 'PASS' for r in results)} passed, {len(bad)} non-PASS", flush=True)
        if bad:
            sys.exit(1)

if __name__ == "__main__":
    main()
