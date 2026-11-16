#!/usr/bin/env python3
"""Complete equivalence check of qsag_gf128_clmul by canonical form.

A carry-less multiplier is a polynomial over GF(2) in the input bits, and every Boolean function
has exactly one algebraic normal form (Reed-Muller form: an XOR of AND-monomials). This script
computes the ANF of every output bit of the gate-level netlist Yosys elaborates from the RTL
(frontend, proc, flatten, techmap; constant folding only) and compares it, monomial for monomial,
with the ANF of the definition  r = sum_{i,j} a_i b_j x^(i+j) mod (x^128 + x^7 + x^2 + x + 1).
Equal normal forms mean equal functions on all 2^256 inputs; no SAT search is involved, which is
why this works where a Karatsuba-versus-schoolbook miter does not terminate.

Registers are followed as wires; the script checks that every path from the inputs to the
outputs crosses the same number of them (3), so the netlist is a pure pipeline.
A mutated multiplier (a dropped Karatsuba term) must be reported as different.
"""
import json, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
OUT = os.path.join(ROOT, "build", "lec")

def netlist(tag, top, files):
    path = os.path.join(OUT, tag + ".json")
    cmd = (f'yosys -q -p "read_verilog -sv {" ".join(files)}; hierarchy -top {top}; proc; flatten; '
           f'opt_expr; opt_clean; techmap; opt_expr; opt_clean; write_json {path}"')
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    if r.returncode:
        sys.exit(r.stdout + r.stderr)
    return json.load(open(path))["modules"][top]

# A monomial is an int: 0 is the constant 1, v is the variable v (1..256), u*512+v is u*v, u < v.
def mmul(m1, m2):
    vs = set()
    for m in (m1, m2):
        if m >= 512: vs.add(m >> 9); vs.add(m & 511)
        elif m: vs.add(m)
    vs = sorted(vs)
    if len(vs) > 2:
        raise SystemExit("monomial of degree > 2: the netlist is not bilinear")
    return 0 if not vs else (vs[0] if len(vs) == 1 else vs[0] * 512 + vs[1])

def pmul(p, q):
    out = set()
    for m1 in p:
        for m2 in q:
            out ^= {mmul(m1, m2)}
    return frozenset(out)

ONE, ZERO = frozenset([0]), frozenset()

def anf_outputs(mod):
    a, b, r = (mod["ports"][k]["bits"] for k in ("a", "b", "r"))
    val, stage = {}, {}
    for i, bit in enumerate(a): val[bit], stage[bit] = frozenset([1 + i]), 0
    for i, bit in enumerate(b): val[bit], stage[bit] = frozenset([129 + i]), 0
    drv = {}
    for c in mod["cells"].values():
        if c["type"] == "$scopeinfo":
            continue
        for bit in c["connections"]["Q" if c["type"].startswith("$_DFF") else "Y"]:
            drv[bit] = c
    def const(bit):
        return bit in ("0", "1", "x")
    def get(bit):
        if bit == "1": return ONE, None
        if bit in ("0", "x"): return ZERO, None
        return val[bit], stage[bit]
    def ready(bit):
        return const(bit) or bit in val
    gates = set()
    for out in r:
        stack = [out]
        while stack:
            bit = stack[-1]
            if ready(bit):
                stack.pop(); continue
            c = drv[bit]
            t, cn = c["type"], c["connections"]
            ins = [cn[p][0] for p in (("D",) if t.startswith("$_DFF") else ("A", "B", "S") if t == "$_MUX_" else ("A",) if t == "$_NOT_" else ("A", "B"))]
            todo = [x for x in ins if not ready(x)]
            if todo:
                stack.extend(todo); continue
            vals = [get(x) for x in ins]
            sts = {s for _, s in vals if s is not None}
            if len(sts) > 1:
                raise SystemExit("unbalanced pipeline at a gate")
            st = sts.pop() if sts else 0
            p = [v for v, _ in vals]
            gates.add(t)
            if t.startswith("$_DFF"): v, st = p[0], st + 1
            elif t == "$_XOR_": v = p[0] ^ p[1]
            elif t == "$_AND_": v = pmul(p[0], p[1])
            elif t == "$_OR_":  v = p[0] ^ p[1] ^ pmul(p[0], p[1])
            elif t == "$_NOT_": v = p[0] ^ ONE
            elif t == "$_MUX_": v = p[0] ^ pmul(p[2], p[0] ^ p[1])
            else: raise SystemExit("unexpected cell " + t)
            val[bit], stage[bit] = frozenset(v), st
            stack.pop()
    return [val[x] for x in r], {stage[x] for x in r}, sum(c["type"] != "$scopeinfo" for c in mod["cells"].values()), sorted(gates)

def spec():
    xp, v = [], 1
    for _ in range(255):
        xp.append(v)
        v <<= 1
        if v >> 128: v = (v & (2**128 - 1)) ^ 0x87
    outs = [set() for _ in range(128)]
    for i in range(128):
        for j in range(128):
            w = xp[i + j]
            for k in range(128):
                if (w >> k) & 1: outs[k] ^= {(1 + i) * 512 + (129 + j)}
    return [frozenset(s) for s in outs]

def tower_spec():
    def tmul(k, a, b):
        if k == 0:
            return a & b
        h = 1 << (k - 1)
        mask = (1 << h) - 1
        a0, a1 = a & mask, a >> h
        b0, b1 = b & mask, b >> h
        p = tmul(k - 1, a0, b0)
        q = tmul(k - 1, a1, b1)
        cross = tmul(k - 1, a0 ^ a1, b0 ^ b1) ^ p ^ q
        g = 1 if k == 1 else 1 << (h // 2)
        return (p ^ q) | ((cross ^ tmul(k - 1, g, q)) << h)

    outs = [set() for _ in range(128)]
    for i in range(128):
        for j in range(128):
            w = tmul(7, 1 << i, 1 << j)
            for k in range(128):
                if (w >> k) & 1:
                    outs[k] ^= {(1 + i) * 512 + (129 + j)}
    return [frozenset(s) for s in outs]

def run(tag, top, files, ref_fn, want_equal):
    got, stages, ncells, gates = anf_outputs(netlist(tag, top, files))
    ref = ref_fn()
    diff = sum(g != s for g, s in zip(got, ref))
    mono = sum(len(s) for s in ref)
    equal = diff == 0 and stages == {3}
    ok = equal == want_equal
    print(f"[{'PASS' if ok else 'FAIL'}] {tag}: {ncells} cells ({', '.join(gates)}), pipeline depth {sorted(stages)}, "
          f"{mono} monomials in the definition, {diff}/128 output bits differ "
          f"(expected {'equal' if want_equal else 'different'})")
    return ok, f"{'PASS' if ok else 'FAIL'}\tanf_{tag}\t{'equal' if want_equal else 'different'}\t{'equal' if equal else 'different'}\t{diff}/128 bits differ, {mono} monomials"

def main():
    os.makedirs(OUT, exist_ok=True)
    rtl = [os.path.join(ROOT, "rtl", f) for f in ("qsag_clmul_kara.sv", "qsag_gf128_reduce.sv", "qsag_gf128_clmul.sv")]
    tmap = os.path.join(ROOT, "rtl", "qsag_gf128_tower_map.sv")
    tmul = os.path.join(ROOT, "rtl", "qsag_gf128_tower_mul.sv")
    ok1, l1 = run("gf128_clmul_anf", "qsag_gf128_clmul", rtl, spec, True)
    kara = open(rtl[0]).read()
    old = "assign xmid = mid ^ hi ^ (2*HH-1)'(lo);"
    assert kara.count(old) == 1
    mut = os.path.join(OUT, "mut_kara_anf.sv")
    open(mut, "w").write(kara.replace(old, "assign xmid = mid ^ hi;"))
    ok2, l2 = run("mut_gf128_clmul_anf", "qsag_gf128_clmul", [mut] + rtl[1:], spec, False)
    ok3, l3 = run("gf128_tower_mul_anf", "qsag_gf128_tower_mul", rtl + [tmap, tmul], tower_spec, True)
    tmap_txt = open(tmap).read()
    old_t = "128'hd353a5afc268871ad268eb72003a04ad"
    assert tmap_txt.count(old_t) >= 1
    mut_t = os.path.join(OUT, "mut_tmap_anf.sv")
    open(mut_t, "w").write(tmap_txt.replace(old_t, "128'hd353a5afc268871ad268eb72003a04ac", 1))
    ok4, l4 = run("mut_gf128_tower_mul_anf", "qsag_gf128_tower_mul", rtl + [mut_t, tmul], tower_spec, False)

    # Also verify universal 2^128 canonical Reed-Muller ANF bijection of composed qsag_tower_rt (`inv(fwd(x)) == x` and `fwd(inv(x)) == x`).
    rt_sv = os.path.join(OUT, "anf_tower_rt.sv")
    open(rt_sv, "w").write("""
module qsag_anf_tower_rt (input logic [127:0] a, input logic [127:0] b, output logic [127:0] r);
    logic [127:0] m0, y01, m1, y10;
    qsag_gf128_tower_map #(.INVERSE(0)) u_f0 (.x(a),  .y(m0));
    qsag_gf128_tower_map #(.INVERSE(1)) u_i0 (.x(m0), .y(y01));
    qsag_gf128_tower_map #(.INVERSE(1)) u_i1 (.x(b),  .y(m1));
    qsag_gf128_tower_map #(.INVERSE(0)) u_f1 (.x(m1), .y(y10));
    assign r = y01 ^ y10;
endmodule
""")
    got_rt, st_rt, nc_rt, gt_rt = anf_outputs(netlist("gf128_tower_rt_anf", "qsag_anf_tower_rt", [tmap, rt_sv]))
    ref_rt = [frozenset([1 + i, 129 + i]) for i in range(128)]
    diff_rt = sum(g != s for g, s in zip(got_rt, ref_rt))
    ok5 = (diff_rt == 0 and st_rt == {0})
    print(f"[{'PASS' if ok5 else 'FAIL'}] gf128_tower_rt_anf: {nc_rt} cells ({', '.join(gt_rt)}), "
          f"inv(fwd(a)) ^ fwd(inv(b)) == a ^ b over all 2^256 (a,b), {diff_rt}/128 bits differ")
    l5 = f"{'PASS' if ok5 else 'FAIL'}\tanf_gf128_tower_rt\tequal\t{'equal' if ok5 else 'different'}\t{diff_rt}/128 bits differ, universal 2^256 bijection"

    with open(os.path.join(OUT, "results_anf.txt"), "w") as f:
        f.write("\n".join([l1, l2, l3, l4, l5]) + "\n")
    sys.exit(0 if (ok1 and ok2 and ok3 and ok4 and ok5) else 1)

if __name__ == "__main__":
    main()
