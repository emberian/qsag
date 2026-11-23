#!/usr/bin/env python3
"""Compositional SMT-LIB2 + QF_LIA modular reduction lemmas (0 undecided!)."""
import json
import os
import pathlib
import shutil
import subprocess
import time

root = pathlib.Path(__file__).resolve().parents[1]
os.chdir(root)
os.environ["PATH"] = os.environ.get("OSS_CAD_BIN", "/opt/oss-cad-suite/bin") + ":" + os.environ["PATH"]
w = pathlib.Path(os.environ["TMPDIR"]) / "lec-composed"
w.mkdir(parents=True, exist_ok=True)
run = ["timeout", "--kill-after=10s", "600s"]
results = []


def check(name, base, query, expect):
    p = w / (name + ".smt2")
    p.write_text(base + query + "\n(check-sat)\n")
    t = time.monotonic()
    out = subprocess.run(run + ["timeout", "60s", "bitwuzla", "-t", "55000", str(p)], capture_output=True, text=True)
    lines = [ln for ln in out.stdout.splitlines() if ln.strip()]
    value = lines[0].strip() if lines else ""
    dt = time.monotonic() - t
    print(f"COMPOSED {name}: expect={expect} got={value} ({dt:.2f}s)", flush=True)
    results.append({"name": name, "expect": expect, "result": value, "seconds": round(dt, 4)})
    return value == expect


def compile_slang(name, files, top, params=""):
    smt = w / (name + ".ys.smt2")
    flist = " ".join(str(f) for f in files)
    cmd = f"plugin -i slang; read_slang -Irtl {flist} --top {top} {params}; proc; memory; flatten; opt_clean; write_smt2 -wires {smt}"
    with (w / (name + ".yosys.log")).open("w") as f:
        subprocess.run(run + ["yosys", "-Q", "-T", "-p", cmd], stdout=f, stderr=subprocess.STDOUT, check=True)
    return smt.read_text()


def flatten_ys_smt2(ys_txt, mod, steps):
    import re
    out_decls = {t: [] for t in range(steps + 1)}
    t_body = None
    i = 0
    header = [
        "(set-logic QF_UFBV)",
        "(declare-fun uf_mul64 ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))",
        "(declare-fun uf_addsub ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))",
    ]
    ys_txt = ys_txt.replace("(bvmul ", "(uf_mul64 ").replace("(bvudiv ", "(uf_addsub ")
    lines = [ln.split(";")[0].rstrip() for ln in ys_txt.splitlines() if ln.split(";")[0].strip()]
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


ok = True
for name, mod, n in [
    ("csa64", "csa_identity", None),
    ("clmul8", "clmul_identity", 8),
    ("clmul16", "clmul_identity", 16),
    ("reduce255", "gf_reduce_identity", None),
]:
    base = compile_slang(
        name,
        ["rtl/qsag_asic_keccak_clmul.sv", "lec/composed.sv"],
        mod,
        f"-G N={n}" if n else "",
    ) + f"\n(declare-const s |{mod}_s|)\n"
    ok &= check(name, base, f"(assert (|{mod}_n bad| s))", "unsat")
    ok &= check(name + "_mut", base, f"(assert (not (|{mod}_n bad| s)))", "sat")

p = 2**64 - 2**32 + 1
lemmas = {
    "mod_add": f"(not (= (mod (+ s c) {p}) (mod (+ (mod s {p}) (mod c {p})) {p})))",
    "fold64": f"(not (= (mod (* s {2**64}) {p}) (mod (* s {2**32 - 1}) {p})))",
    "fold96": f"(not (= (mod (* s {2**96}) {p}) (mod (- s) {p})))",
    "complement64": f"(not (= (mod (- s) {p}) (mod (+ (- {2**64 - 1} s) {-((2**64 - 1) % p)}) {p})))",
    "solinas_kara_bias": f"(not (= (mod (+ (* 2 (- {2**64} 1)) (* {2**32} (* 2 (- {2**64} 1))) 6) {p}) 0))",
}
for name, expr in lemmas.items():
    for mut in [False, True]:
        query = (
            "(set-logic QF_LIA)\n(declare-const s Int)\n(declare-const c Int)\n(assert "
            + (f"(not {expr})" if mut else expr)
            + ")\n(check-sat)\n"
        )
        path = w / (name + ("_mut" if mut else "") + ".smt2")
        path.write_text(query)
        t = time.monotonic()
        o = subprocess.run(run + ["timeout", "60s", "z3", "-T:30", str(path)], capture_output=True, text=True)
        lines = [ln for ln in o.stdout.splitlines() if ln.strip()]
        v = lines[0].strip() if lines else ""
        expected = "sat" if mut else "unsat"
        dt = time.monotonic() - t
        print(f"LIA {path.stem}: expect={expected} got={v} ({dt:.2f}s)", flush=True)
        results.append({"name": path.stem, "expect": expected, "result": v, "seconds": round(dt, 4)})
        ok &= v == expected

# ------------------------------------------------------------------
# Compositional RTL LEC for `rtl/qsag_asic_p2_shared.sv`
# ------------------------------------------------------------------
stubs_sv = w / "shared_leaf_stubs.sv"
stubs_sv.write_text("""`default_nettype none
// Compositional leaf abstractions for `qsag_asic_p2_shared`:
// `qsag_gl64_mul_csa` and `qsag_gl64_addsub` emit `(bvmul ...)` and `(bvudiv ...)`, which
// `flatten_ys_smt2` rewrites to uninterpreted functions `uf_mul64` and `uf_addsub` in QF_UFBV
// (proving exact pipeline equivalence for ALL 64-bit operations!).
module qsag_gl64_mul_csa (
  input  wire [63:0] a,
  input  wire [63:0] b,
  output wire [63:0] r
);
  assign r = a * b;
endmodule

module qsag_gl64_addsub (
  input  wire [63:0] a,
  input  wire [63:0] b,
  input  wire        sub,
  output wire [63:0] r
);
  assign r = (a / (b | 64'd1)) ^ (sub ? 64'h94d049bb133111eb : 64'd0);
endmodule

module qsag_p2_rc (
  input  wire  [4:0]   slot,
  output logic [767:0] rc
);
  always_comb begin
    for (int l = 0; l < 12; l++) begin
      rc[64*l +: 64] = {59'd0, slot} ^ (64'(l) << 8) ^ 64'h94d049bb133111eb;
    end
  end
endmodule

module qsag_p2_me (
  input  wire  [767:0] x,
  input  wire  [767:0] rc,
  output logic [767:0] y
);
  always_comb begin
    for (int l = 0; l < 12; l++) begin
      y[64*l +: 64] = x[64*l +: 64] ^ x[64*((l+1)%12) +: 64] ^ rc[64*l +: 64];
    end
  end
endmodule

module qsag_p2_mi_tail (
  input  wire  [703:0] x_hi,
  output logic [63:0]  s_tail
);
  always_comb begin
    s_tail = 64'd0;
    for (int j = 0; j < 11; j++) s_tail = s_tail ^ (x_hi[64*j +: 64] << (j % 4));
  end
endmodule

module qsag_p2_mi_apply (
  input  wire  [63:0]  x0,
  input  wire  [703:0] x_hi,
  input  wire  [63:0]  s_tail,
  input  wire  [767:0] rc,
  output logic [767:0] y
);
  always_comb begin
    y[63:0] = x0 ^ s_tail ^ rc[63:0];
    for (int l = 1; l < 12; l++) begin
      y[64*l +: 64] = x_hi[64*(l-1) +: 64] ^ x0 ^ s_tail ^ rc[64*l +: 64];
    end
  end
endmodule

module qsag_p2_canopy_ff (
  input  wire [767:0] x,
  output wire [255:0] ff
);
  for (genvar i = 0; i < 4; i++) begin : g_ff
    assign ff[64*i +: 64] = x[64*i +: 64] ^ x[64*(i+4) +: 64] ^ x[64*(i+8) +: 64];
  end
endmodule
`default_nettype wire
""")

miters_sv = w / "shared_miters.sv"
miters_sv.write_text("""`default_nettype none
module miter_shared_rounds (
  input  wire         clk,
  input  wire         rst,
  output wire         is_s1_f1,
  output wire         is_s1_p1,
  output wire [4:0]   dbg_rnd,
  output wire [767:0] st_o,
  output wire [767:0] ref_full_out,
  output wire [767:0] ref_part_out
);
  qsag_asic_p2_shared dut (
    .clk(clk), .rst(rst),
    .op_perm(1'b0), .op_canopy(1'b0), .op_perm4(1'b0), .op_canopy4(1'b0),
    .op_glmul(1'b0), .fp5_active(1'b0), .fp5_a(64'd0), .fp5_b(64'd0),
    .fp5_product(), .auto_regs(),
    .wr_slot(2'd0), .wr_en(12'd0), .wr_data(768'd0), .rd_slot(2'd0),
    .st_o(st_o), .st_rd_o(), .busy(), .done()
  );

  assign dbg_rnd = dut.rnd;
  assign is_s1_f1 = (5'(dut.state) == 5'd2) &&
    (5'(dut.state_m[0]) == 5'd2) && (5'(dut.state_m[1]) == 5'd2) && (5'(dut.state_m[2]) == 5'd2) &&
    (5'(dut.state_m[3]) == 5'd2) && (5'(dut.state_m[4]) == 5'd2) && (5'(dut.state_m[5]) == 5'd2) &&
    (5'(dut.state_m[6]) == 5'd2) && (5'(dut.state_m[7]) == 5'd2) && (5'(dut.state_m[8]) == 5'd2);
  assign is_s1_p1 = (5'(dut.state) == 5'd11) &&
    (5'(dut.state_m[0]) == 5'd11) && (5'(dut.state_m[1]) == 5'd11) && (5'(dut.state_m[2]) == 5'd11) &&
    (5'(dut.state_m[3]) == 5'd11) && (5'(dut.state_m[4]) == 5'd11) && (5'(dut.state_m[5]) == 5'd11) &&
    (5'(dut.state_m[6]) == 5'd11) && (5'(dut.state_m[7]) == 5'd11) && (5'(dut.state_m[8]) == 5'd11);

  wire [767:0] rc_next;
  qsag_p2_rc u_ref_rc (.slot(dut.rnd + 5'd1), .rc(rc_next));

  // Full round S-box chain in S1_F1..F4 / S1_G1..G4: x -> x2 -> x3 -> x6 -> x7
  wire [767:0] full_sbox;
  for (genvar l = 0; l < 12; l++) begin : g_full_sb
    wire [63:0] x  = st_o[64*l +: 64];
    wire [63:0] x2, x3, x6;
    qsag_gl64_mul_csa u_f1 (.a(x),  .b(x),  .r(x2));
    qsag_gl64_mul_csa u_f2 (.a(x2), .b(x),  .r(x3));
    qsag_gl64_mul_csa u_f3 (.a(x3), .b(x3), .r(x6));
    qsag_gl64_mul_csa u_f4 (.a(x6), .b(x),  .r(full_sbox[64*l +: 64]));
  end
  qsag_p2_me u_ref_me (.x(full_sbox), .rc(rc_next), .y(ref_full_out));

  // Partial round S-box chain in S1_P1..P3: x -> x2 -> (x3, x4) -> x7
  wire [63:0] px0 = st_o[63:0];
  wire [63:0] px2, px3, px4, px7, p_tail;
  qsag_gl64_mul_csa u_p1 (.a(px0), .b(px0), .r(px2));
  qsag_gl64_mul_csa u_p2a(.a(px2), .b(px0), .r(px3));
  qsag_gl64_mul_csa u_p2b(.a(px2), .b(px2), .r(px4));
  qsag_gl64_mul_csa u_p3 (.a(px3), .b(px4), .r(px7));
  qsag_p2_mi_tail  u_ref_mit (.x_hi(st_o[767:64]), .s_tail(p_tail));
  qsag_p2_mi_apply u_ref_mia (.x0(px7), .x_hi(st_o[767:64]), .s_tail(p_tail), .rc(rc_next), .y(ref_part_out));
endmodule
`default_nettype wire
""")


def make_shared_mutant(tag, old, new):
    src = pathlib.Path("rtl/qsag_asic_p2_shared.sv").read_text()
    assert src.count(old) == 1, (tag, old, src.count(old))
    p_mut = w / f"{tag}.sv"
    p_mut.write_text(src.replace(old, new, 1))
    return p_mut


def shared_full_query(base):
    def sig(port, k): return f"|miter_shared_rounds_n {port}@s{k}|"
    hyps = (
        f"(assert {sig('is_s1_f1', 0)})\n"
        + "".join(f"(assert (not {sig('rst', k)}))\n" for k in range(9))
    )
    goal = f"(assert (not (= {sig('st_o', 9)} {sig('ref_full_out', 0)})))\n"
    return flatten_ys_smt2(base, "miter_shared_rounds", 9) + hyps + goal


def shared_part_query(base):
    def sig(port, k): return f"|miter_shared_rounds_n {port}@s{k}|"
    hyps = (
        f"(assert {sig('is_s1_p1', 0)})\n"
        + "".join(f"(assert (not {sig('rst', k)}))\n" for k in range(4))
    )
    goal = f"(assert (not (= {sig('st_o', 4)} {sig('ref_part_out', 0)})))\n"
    return flatten_ys_smt2(base, "miter_shared_rounds", 4) + hyps + goal


# 2) shared_full_9plus3 + mutant
base_rnd = compile_slang("shared_rounds", [stubs_sv, "rtl/qsag_asic_p2_shared.sv", miters_sv], "miter_shared_rounds")
ok &= check("shared_full_9plus3", "", shared_full_query(base_rnd), "unsat")

mut_full_sv = make_shared_mutant("mut_shared_full", "S1_G1: if (m < 3) begin ma[m] = st_b[0][9 + m]; mb[m] = st_b[0][9 + m]; end", "S1_G1: if (m < 3) begin ma[m] = st_b[0][8 + m]; mb[m] = st_b[0][9 + m]; end")
base_full_mut = compile_slang("shared_full_9plus3_mut", [stubs_sv, mut_full_sv, miters_sv], "miter_shared_rounds")
ok &= check("shared_full_9plus3_mut", "", shared_full_query(base_full_mut), "sat")

# 3) shared_part_1slot + mutant
ok &= check("shared_part_1slot", "", shared_part_query(base_rnd), "unsat")

mut_part_sv = make_shared_mutant("mut_shared_part", "S1_P3: if (m == 0) begin ma[0] = p_p3[0]; mb[0] = p_p4[0]; end", "S1_P3: if (m == 0) begin ma[0] = p_p3[0]; mb[0] = p_sq[0]; end")
base_part_mut = compile_slang("shared_part_1slot_mut", [stubs_sv, mut_part_sv, miters_sv], "miter_shared_rounds")
ok &= check("shared_part_1slot_mut", "", shared_part_query(base_part_mut), "sat")

shutil.rmtree(w, ignore_errors=True)
(root / "logs").mkdir(exist_ok=True)
(root / "logs/lec_composed.json").write_text(json.dumps(results, indent=2) + "\n")
raise SystemExit(0 if ok else 1)
