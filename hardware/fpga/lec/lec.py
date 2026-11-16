#!/usr/bin/env python3
"""Formal checks of the QSAG-NI arithmetic units: Yosys reads the SystemVerilog and writes its
transition relation with `write_smt2` (frontend, `proc`, `flatten` only: no optimisation pass),
this script writes the specification and the miter around it, z3 decides.

Every check prints the statement, the expected answer and z3's answer. `unsat` on a proof and
`sat` on a mutant are the passing answers. See lec/README.md for what each statement means and
what is taken on trust.
"""
import os, re, subprocess, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
OUT = os.path.join(ROOT, "build", "lec")
P = 2**64 - 2**32 + 1
Z3_SECS = int(os.environ.get("LEC_SECS", "150"))
TRY_SECS = int(os.environ.get("LEC_TRY_SECS", "60"))
results = []

def sh(cmd):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(r.stdout[-3000:] + r.stderr[-3000:])
        raise SystemExit("command failed: " + cmd)
    return r.stdout

def yosys_smt2(name, top, files, chparam=""):
    """SMT-LIB2 of `top` as module lec_top; returns the text."""
    out = os.path.join(OUT, name + ".yosys.smt2")
    srcs = " ".join(files)
    sh(f'yosys -q -p "read_verilog -sv {srcs}; hierarchy -top {top} {chparam}; proc; flatten; '
       f'opt_clean; rename -top lec_top; write_smt2 -wires {out}"')
    return open(out).read()

def unroll(steps):
    s = "".join(f"(declare-fun s{k} () |lec_top_s|)\n" for k in range(steps + 1))
    s += "".join(f"(assert (|lec_top_h| s{k}))\n" for k in range(steps + 1))
    s += "".join(f"(assert (|lec_top_t| s{k} s{k+1}))\n" for k in range(steps))
    return s

def z3(name, text, secs):
    path = os.path.join(OUT, name + ".smt2")
    open(path, "w").write(text)
    t0 = time.time()
    try:
        r = subprocess.run(["z3", f"-T:{secs}", path], capture_output=True, text=True, timeout=secs + 30)
        ans = (r.stdout.strip().splitlines() or ["?"])[0]
    except subprocess.TimeoutExpired:
        ans = "timeout"
    return ans, time.time() - t0

def record(name, statement, expect, text, secs=None, required=True):
    ans, dt = z3(name, text, secs or Z3_SECS)
    ok = ans == expect
    tag = "PASS" if ok else ("FAIL" if required else "open")
    results.append((tag, name, statement, expect, ans, dt))
    print(f"[{tag}] {name}: z3 {ans} in {dt:.1f}s (expected {expect}) -- {statement}", flush=True)
    return ok

def bv(v, w):
    return f"(_ bv{v} {w})"

def zext(e, frm, to):
    return e if to == frm else f"((_ zero_extend {to - frm}) {e})"

VW = 72  # width of the reduction statement; the values below stay under 2^66

def reduce_spec(x136, r64):
    """r = x mod p, in two machine-checked halves.

    This half (bit-vectors, on the RTL): with x = lo + m*2^64 + h*2^96 + t*2^128 and
        V = lo + m*2^32 + p - m - h - t*2^32,
    r < p and V = r + k*p for some k in {0, 1, 2}.
    The other half (check_reduce_algebra, integers): 0 < V < 2^66 and x + p = V + p*Q0 with
    Q0 = m + (h + t*2^32)*(2^32 + 1). Together x = r + p*(Q0 + k - 1) with r < p, and the
    remainder of a division is unique."""
    lo = zext(f"((_ extract 63 0) {x136})", 64, VW)
    m = zext(f"((_ extract 95 64) {x136})", 32, VW)
    h = zext(f"((_ extract 127 96) {x136})", 32, VW)
    t = zext(f"((_ extract 135 128) {x136})", 8, VW)
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
    record("reduce_identity", "integers: x + p = V + p*Q0 for x = lo + m 2^64 + h 2^96 + t 2^128 "
           "(the Goldilocks reduction identity)", "unsat",
           decl + f"(assert (not (= (+ {x} {P}) (+ {V} (* {P} {q0})))))\n(check-sat)\n")
    record("reduce_range", "integers: limbs in range imply 0 < V < 3p (so V is exact in the bit-vector statement)",
           "unsat", decl + rng + f"(assert (not (and (> {V} 0) (< {V} {3 * P}))))\n(check-sat)\n")

def mutate(src, old, new, name):
    text = open(src).read()
    assert text.count(old) == 1, (src, old, text.count(old))
    path = os.path.join(OUT, name)
    open(path, "w").write(text.replace(old, new))
    return path

# ------------------------------------------------------------------------------------------
PKG = os.path.join(ROOT, "rtl/qsag_ni_pkg.sv")
RED = os.path.join(ROOT, "rtl/qsag_gl64_reduce.sv")
MUL = os.path.join(ROOT, "rtl/qsag_mul64_dsp.sv")
GLM = os.path.join(ROOT, "rtl/qsag_gl64_dsp_mul.sv")
KARA = os.path.join(ROOT, "rtl/qsag_clmul_kara.sv")
GFRED = os.path.join(ROOT, "rtl/qsag_gf128_reduce.sv")
GFMUL = os.path.join(ROOT, "rtl/qsag_gf128_clmul.sv")

def acc(port, state):
    return f"(|lec_top_n {port}| {state})"

def check_reduce(tag, files, expect, required=True):
    ys = yosys_smt2(tag, "qsag_gl64_reduce", files)
    body = ys + unroll(2)
    stmt = reduce_spec(acc("x", "s0"), acc("r", "s2"))
    return record(tag, "qsag_gl64_reduce: for all 2^136 inputs, r (2 clocks later) < p and V(x) = r + k*p, k in {0,1,2}",
                  expect, body + f"(assert (not {stmt}))\n(check-sat)\n", required=required)

def tile_sum(aw, bw, a, b, fn):
    """sum_{i,j} fn(a_i, b_j) << (aw*i + bw*j) as a 128-bit term, chunks zero-extended to aw+bw,
    and the hypotheses fn(a_i, b_j) <= (2^wa - 1)(2^wb - 1) for the true chunk widths wa, wb."""
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
    """Replace every tile multiply by one uninterpreted function `qtile`. The miter then only
    assumes of it the product bound (tile_sum's hypotheses), which multiplication satisfies
    (check_tiling_identity), so `unsat` holds in particular for real multiplication."""
    assert ys.count("(bvmul ") == n, (ys.count("(bvmul "), n)
    return f"(declare-fun qtile ((_ BitVec {tw}) (_ BitVec {tw})) (_ BitVec {tw}))\n" + ys.replace("(bvmul ", "(qtile ")

def check_mul_wiring(tag, files, aw, bw, expect, precise=False, required=True, secs=None):
    chp = f"-chparam AW {aw} -chparam BW {bw}"
    ys = yosys_smt2(tag, "qsag_mul64_dsp", files, chp)
    spec, n, tw, hyps, _ = tile_sum(aw, bw, acc("a", "s0"), acc("b", "s0"), "bvmul" if precise else "qtile")
    if not precise:
        ys = abstract_tiles(ys, n, tw)
    else:
        hyps = ""
    how = "bit-precise tiles" if precise else "tiles: any function within the product bound"
    return record(tag, f"qsag_mul64_dsp AW={aw} BW={bw}: p (4 clocks later) = sum of the {n} tile products "
                       f"shifted to their weights ({how})",
                  expect, ys + unroll(4) + hyps + f"(assert (not (= {acc('p', 's4')} {spec})))\n(check-sat)\n",
                  secs=secs, required=required)

def check_glmul(tag, files, aw, bw, expect_product="unsat", expect_reduce="unsat"):
    """The whole multiplier-reducer, as two statements about one transition system, joined at
    its 128-bit product register `prod`:
      product: prod, 4 clocks after (a, b), is the weighted sum X of the tile products;
      reduce : r, 2 clocks after any prod, is < p with V(prod) = r + k*p.
    Hence r, 6 clocks after (a, b), is X mod p; with the integer lemmas X = a*b."""
    chp = f"-chparam AW {aw} -chparam BW {bw}"
    ys = yosys_smt2(tag, "qsag_gl64_dsp_mul", files, chp)
    spec, n, tw, hyps, _ = tile_sum(aw, bw, acc("a", "s0"), acc("b", "s0"), "qtile")
    ys = abstract_tiles(ys, n, tw)
    ok = record(tag + "_product", f"qsag_gl64_dsp_mul AW={aw} BW={bw}: for all 2^128 inputs, the product register "
                f"(4 clocks later) = the weighted sum X of the {n} tile products (tiles: any function within the product bound)",
                expect_product, ys + unroll(4) + hyps + f"(assert (not (= {acc('prod', 's4')} {spec})))\n(check-sat)\n")
    stmt = reduce_spec(zext(acc("prod", "s0"), 128, 136), acc("r", "s2"))
    ok &= record(tag + "_reduce", f"qsag_gl64_dsp_mul AW={aw} BW={bw}: for every product register value X, r (2 clocks later) "
                 f"< p and V(X) = r + k*p, k in {{0,1,2}}",
                 expect_reduce, ys + unroll(2) + f"(assert (not {stmt}))\n(check-sat)\n")
    return ok

def check_tiling_identity(aw, bw):
    """Over the integers: the chunked product is the product. With the wiring proof and
    tile = multiplication this gives p = a*b; chunk products fit the tile width."""
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
    for wa, wb in tile_sum(aw, bw, "a", "b", "f")[4]:
        record(f"tile_bound_{wa}x{wb}",
               f"integers: 0 <= a < 2^{wa} and 0 <= b < 2^{wb} imply a*b <= (2^{wa}-1)(2^{wb}-1) < 2^{aw+bw}", "unsat",
               "(declare-const a Int)\n(declare-const b Int)\n"
               f"(assert (and (>= a 0) (< a {2**wa}) (>= b 0) (< b {2**wb})))\n"
               f"(assert (not (and (<= (* a b) {(2**wa - 1) * (2**wb - 1)}) (< {(2**wa - 1) * (2**wb - 1)} {2**(aw+bw)}))))\n(check-sat)\n")

def gf_xpow():
    """x^i mod (x^128 + x^7 + x^2 + x + 1) for i < 255, by the defining recurrence."""
    t, v = [], 1
    for _ in range(255):
        t.append(v)
        v <<= 1
        if v >> 128:
            v = (v & (2**128 - 1)) ^ 0x87
    return t

def check_gf_reduce(tag, files, expect, required=True):
    ys = yosys_smt2(tag, "qsag_gf128_reduce", files)
    xp = gf_xpow()
    c = acc("c", "s0")
    e = f"((_ extract 127 0) {c})"
    for i in range(128, 255):
        e = f"(bvxor {e} (ite (= ((_ extract {i} {i}) {c}) #b1) {bv(xp[i], 128)} {bv(0, 128)}))"
    return record(tag, "qsag_gf128_reduce: for all 2^255 inputs, r = c mod (x^128+x^7+x^2+x+1) "
                       "(spec: XOR of the constants x^i mod P over the set bits)",
                  expect, ys + "(declare-fun s0 () |lec_top_s|)\n(assert (|lec_top_h| s0))\n"
                  f"(assert (not (= {acc('r', 's0')} {e})))\n(check-sat)\n", required=required)

def gf_mul_spec(a, b):
    """Bit-serial GF(2^128) product, most significant bit of b first."""
    lets, prev = [], bv(0, 128)
    for n, i in enumerate(range(127, -1, -1)):
        x2 = f"(bvxor (bvshl {prev} {bv(1, 128)}) (ite (= ((_ extract 127 127) {prev}) #b1) {bv(0x87, 128)} {bv(0, 128)}))"
        lets.append(f"(g{n} (bvxor {x2} (ite (= ((_ extract {i} {i}) {b}) #b1) {a} {bv(0, 128)})))")
        prev = f"g{n}"
    return "".join(f"(let ({l}) " for l in lets) + prev + ")" * len(lets)

def check_gf_mul(tag, files, expect, onehot=None, required=True, secs=None):
    ys = yosys_smt2(tag, "qsag_gf128_clmul", files)
    a, b = acc("a", "s0"), acc("b", "s0")
    body = ys + unroll(3)
    if onehot is None:
        stmt = "qsag_gf128_clmul: for all 2^256 inputs, r (3 clocks later) = a*b in GF(2^128) (bit-serial spec)"
    else:
        body += f"(declare-const j (_ BitVec 128))\n(assert (bvult j {bv(128, 128)}))\n" \
                f"(assert (= {b} (bvshl {bv(1, 128)} j)))\n"
        stmt = "qsag_gf128_clmul: for all a and every basis element b = x^j, r = a * x^j in GF(2^128)"
    return record(tag, stmt, expect, body + f"(assert (not (= {acc('r', 's3')} {gf_mul_spec(a, b)})))\n(check-sat)\n",
                  required=required, secs=secs)

def group_gl():
    check_reduce_algebra()
    check_reduce("gl64_reduce", [PKG, RED], "unsat")
    for aw, bw in ((26, 17), (16, 16)):
        check_tiling_identity(aw, bw)
        check_glmul(f"gl64_dsp_mul_{aw}x{bw}", [PKG, RED, MUL, GLM], aw, bw)

def group_glmut():
    # mutants: each must be refuted with a counterexample
    m1 = mutate(RED, "- {34'b0, h}", "+ {34'b0, h}", "mut_reduce_sign.sv")
    check_reduce("mut_gl64_reduce_sign", [PKG, m1], "sat")
    m2 = mutate(RED, "!v2[66] ? v2[63:0]", "!v2[66] ? v1[63:0]", "mut_reduce_select.sv")
    check_glmul("mut_select_gl64_dsp_mul", [PKG, m2, MUL, GLM], 26, 17, expect_reduce="sat")
    m3 = mutate(MUL, "assign bj = TW'(b_q[j*BW +: BW]);", "assign bj = TW'(b_q[((j+1)%NB)*BW +: BW]);", "mut_mul_tile.sv")
    check_mul_wiring("mut_tile_mul64_wiring", [m3], 26, 17, "sat")
    m4 = mutate(MUL, "<< (j * BW));", "<< (j * BW + (j == 3 ? 1 : 0)));", "mut_mul_shift.sv")
    check_glmul("mut_shift_gl64_dsp_mul", [PKG, RED, m4, GLM], 26, 17, expect_product="sat")

def group_gf():
    check_gf_reduce("gf128_reduce", [GFRED], "unsat")
    check_gf_mul("gf128_clmul_basis", [KARA, GFRED, GFMUL], "unsat", onehot=True)
    m5 = mutate(GFRED, "(134'(hi) << 7)", "(134'(hi) << 6)", "mut_gf_reduce.sv")
    check_gf_reduce("mut_gf128_reduce_tap", [m5], "sat")
    m6 = mutate(KARA, "assign xmid = mid ^ hi ^ (2*HH-1)'(lo);", "assign xmid = mid ^ hi;", "mut_kara.sv")
    check_gf_mul("mut_gf128_clmul_kara", [m6, GFRED, GFMUL], "sat")
    check_gf_mul("mut_gf128_clmul_basis", [m6, GFRED, GFMUL], "sat", onehot=True)

def group_try():
    # attempts that are recorded, not required: bit-precise multiplier miters
    check_mul_wiring("try_mul64_wiring_precise_26x17", [MUL], 26, 17, "unsat", precise=True, required=False, secs=TRY_SECS)
    ys = yosys_smt2("try_monolithic", "qsag_gl64_dsp_mul", [PKG, RED, MUL, GLM])
    a, b = acc("a", "s0"), acc("b", "s0")
    mono = f"((_ extract 63 0) (bvurem (bvmul {zext(a, 64, 128)} {zext(b, 64, 128)}) {bv(P, 128)}))"
    record("try_gl64_dsp_mul_monolithic", "qsag_gl64_dsp_mul: r = bvurem(bvmul(a, b), p), one bit-blasted query",
           "unsat", ys + unroll(6) + f"(assert (not (= {acc('r', 's6')} {mono})))\n(check-sat)\n",
           secs=TRY_SECS, required=False)
    check_gf_mul("try_gf128_clmul_monolithic", [KARA, GFRED, GFMUL], "unsat", required=False, secs=TRY_SECS)

GROUPS = {"gl": group_gl, "glmut": group_glmut, "gf": group_gf, "try": group_try}

def main():
    """lec.py <group>...: each group fits one 600 s build slot; results accumulate per group."""
    os.makedirs(OUT, exist_ok=True)
    groups = sys.argv[1:] or list(GROUPS)
    for g in groups:
        del results[:]
        GROUPS[g]()
        with open(os.path.join(OUT, f"results_{g}.txt"), "w") as f:
            for tag, name, stmt, exp, ans, dt in results:
                f.write(f"{tag}\t{name}\t{exp}\t{ans}\t{dt:.1f}s\t{stmt}\n")
        bad = [r for r in results if r[0] == "FAIL"]
        print(f"LEC {g}: {sum(r[0] == 'PASS' for r in results)} passed, {len(bad)} failed, "
              f"{sum(r[0] == 'open' for r in results)} recorded as undecided", flush=True)
        if bad:
            sys.exit(1)

if __name__ == "__main__":
    main()
