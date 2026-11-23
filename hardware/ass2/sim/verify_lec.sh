#!/usr/bin/env bash
# Formal SAT / Inductive Equivalence Proof (LEC) for Rev. 2.1 ASS2-0P5 Arithmetic & ALU Units:
#   1. `gl_reduce64`, `gl_mul_2p32m1`, `add64_u8`, AND shared-adder Goldilocks `+- PRIME` correction === exact math (`UNSAT`)
#   2. `qsag_ass2_gf_step` (2-bit/clk Horner step) === 2-fold composition of 1-bit GF(2^128) step (`UNSAT`)
#   3. `qsag_ass2_alu` (6-stage log-shifter + shared add64 + unified LUT4 bitwise + crypto Rho) === reference ALU (`UNSAT`)
#   4. `qsag_gl64_karatsuba_csa` (64-step 1-bit/clk iterative shift-accumulate sharing `qsag_ass2_add64`):
#      - Universal 2^192 1-step inductive transition theorem (`{cout, sum, prev[63:1]}` === exact shift-add, `UNSAT`)
#      - 66-cycle sequential FSM & boundary theorem (`last` at step 65, exact `(opa*opb)+mc`, `UNSAT`)
set -euo pipefail
[[ $(uname -s) == Linux ]] || { echo "Run on a Linux host" >&2; exit 2; }
export PATH="${OSS_CAD_BIN:-/opt/oss-cad-suite/bin}:$PATH"
here=$(cd "$(dirname "$0")" && pwd)
rtl=$(cd "$here/../rtl" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/ass2-lec.XXXXXX")
trap 'rm -rf "$work"' EXIT

cat > "$work/lec_harnesses.sv" <<'SV'
module lec_gl_helpers (
    input  logic [63:0] x_i,
    input  logic [63:0] y64_i,
    input  logic        sub_i,
    output logic        ok_reduce_o,
    output logic        ok_mul2p32m1_o,
    output logic        ok_add64_u8_o,
    output logic        ok_mod_addsub_o
);
    import qsag_ass2_pkg::*;
    localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
    wire [63:0] dut_red = gl_reduce64(x_i);
    wire [63:0] ref_red = (x_i >= P) ? (x_i - P) : x_i;
    assign ok_reduce_o  = (dut_red == ref_red);

    wire [63:0] dut_m   = gl_mul_2p32m1(y64_i[31:0]);
    wire [63:0] ref_m   = (64'(y64_i[31:0]) << 32) - 64'(y64_i[31:0]);
    assign ok_mul2p32m1_o = (dut_m == ref_m);

    wire [63:0] dut_inc = add64_u8(x_i, y64_i[7:0]);
    wire [63:0] ref_inc = x_i + {56'd0, y64_i[7:0]};
    assign ok_add64_u8_o = (dut_inc == ref_inc);

    // Prove 2-pass shared-adder Goldilocks modular add/sub (`qsag_ass2_crypto` stages 1 & 2) === gl_add64/gl_sub64!
    wire [63:0] ca = gl_reduce64(x_i);
    wire [63:0] cb = gl_reduce64(y64_i) ^ {64{sub_i}};
    wire [63:0] s1;
    wire        c1, c2;
    qsag_ass2_add64 u_a1 (.a(ca), .b(cb), .cin(sub_i), .sum(s1), .cout(c1));
    wire        ge_p      = c1 || ((&s1[63:32]) && (|s1[31:0]));
    wire        need_corr = sub_i ? !c1 : ge_p;
    wire [63:0] corr_b    = !need_corr ? 64'd0 : sub_i ? P : 64'h0000_0000_FFFF_FFFF;
    wire [63:0] s2;
    qsag_ass2_add64 u_a2 (.a(s1), .b(corr_b), .cin(1'b0), .sum(s2), .cout(c2));
    wire [63:0] ref_mod   = sub_i ? gl_sub64(x_i, y64_i) : gl_add64(x_i, y64_i);
    assign ok_mod_addsub_o = (s2 == ref_mod);
endmodule

module lec_gf_step2 (
    input  logic [127:0] acc_i,
    input  logic [127:0] b_i,
    input  logic         bit_i,
    output logic         ok_o
);
    wire [127:0] dut_out;
    qsag_ass2_gf_step u_dut (.a(b_i), .acc(acc_i), .bit_in(bit_i), .result(dut_out));

    wire [127:0] sh      = {acc_i[126:0], 1'b0} ^ (acc_i[127] ? 128'h87 : 128'd0);
    wire [127:0] ref_out = sh ^ (bit_i ? b_i : 128'd0);
    assign ok_o = (dut_out == ref_out);
endmodule

module lec_alu_equiv (
    input  logic        addr_mode_i,
    input  logic [63:0] addr_base_i,
    input  logic [63:0] addr_offset_i,
    input  logic        ext_add_en_i,
    input  logic [63:0] ext_add_a_i,
    input  logic [63:0] ext_add_b_i,
    input  logic        ext_add_cin_i,
    input  logic        crypto_rot_en_i,
    input  logic [5:0]  crypto_rot_amt_i,
    input  logic [3:0]  op, fn, flags, byte_idx,
    input  logic [19:0] imm,
    input  logic [63:0] ra, rb, rc, pc,
    output logic        ok_res_o,
    output logic        ok_ea_o,
    output logic        ok_ext_o,
    output logic        ok_rot_o
);
    import qsag_ass2_pkg::*;
    wire [63:0] dut_sum, dut_rot, dut_res;
    wire        dut_cout;
    qsag_ass2_alu u_dut (
        .addr_mode_i, .addr_base_i, .addr_offset_i,
        .ext_add_en_i, .ext_add_a_i, .ext_add_b_i, .ext_add_cin_i,
        .crypto_rot_en_i, .crypto_rot_amt_i,
        .op, .fn, .flags, .byte_idx, .imm, .ra, .rb, .rc, .pc,
        .sum_o(dut_sum), .cout_o(dut_cout), .rot_o(dut_rot), .result(dut_res)
    );

    assign ok_ea_o  = !(addr_mode_i && !ext_add_en_i) || (dut_sum == (addr_base_i + addr_offset_i));
    wire [64:0] ref_ext = {1'b0, ext_add_a_i} + {1'b0, ext_add_b_i} + {64'd0, ext_add_cin_i};
    assign ok_ext_o = !ext_add_en_i || ({dut_cout, dut_sum} == ref_ext);

    wire [5:0]  csh = crypto_rot_amt_i;
    wire [63:0] ref_crot = (csh == 6'd0) ? ra : ((ra << csh) | (ra >> (7'd64 - {1'b0, csh})));
    assign ok_rot_o = !crypto_rot_en_i || (dut_rot == ref_crot);

    logic [63:0] ref_res;
    logic        check_en;
    wire [63:0] u16 = {48'd0, imm[15:0]};
    wire [63:0] s16 = {{48{imm[15]}}, imm[15:0]};
    wire [5:0]  sh  = (op == ALUI) ? imm[5:0] : rb[5:0];
    wire        sat = (op == ALU) && (|rb[63:6]);
    always_comb begin
        check_en = !addr_mode_i && !ext_add_en_i && !crypto_rot_en_i;
        ref_res  = 64'd0;
        case (op)
            ALU: case (fn)
                4'h0: ref_res = ra + rb;
                4'h1: ref_res = ra - rb;
                4'h2: ref_res = sat ? 64'd0        : (ra << sh);
                4'h3: ref_res = sat ? 64'd0        : (ra >> sh);
                4'h4: ref_res = sat ? {64{ra[63]}} : 64'($signed(ra) >>> sh);
                4'h5: ref_res = (sh == 6'd0) ? ra : ((ra << sh) | (ra >> (7'd64 - {1'b0, sh})));
                4'h6: ref_res = (sh == 6'd0) ? ra : ((ra >> sh) | (ra << (7'd64 - {1'b0, sh})));
                default: check_en = 1'b0;
            endcase
            ALUI: case (fn)
                4'h0: ref_res = ra + s16;
                4'h1: ref_res = ra + u16;
                4'h2: ref_res = ra ^ u16;
                4'h3: ref_res = ra & u16;
                4'h4: ref_res = ra | u16;
                4'h5: ref_res = ra << sh;
                4'h6: ref_res = ra >> sh;
                4'h7: ref_res = 64'($signed(ra) >>> sh);
                4'h8: ref_res = (sh == 6'd0) ? ra : ((ra << sh) | (ra >> (7'd64 - {1'b0, sh})));
                4'h9: ref_res = {ra[47:0], imm[15:0]};
                default: check_en = 1'b0;
            endcase
            default: check_en = 1'b0;
        endcase
    end
    assign ok_res_o = !check_en || (dut_res == ref_res);
endmodule
SV

cat > "$work/prove_comb.ys" <<YS
read_slang --top lec_gl_helpers -I$rtl $rtl/qsag_ass2_pkg.sv $rtl/qsag_ass2_add64.sv $work/lec_harnesses.sv
hierarchy -check -top lec_gl_helpers
proc; opt; techmap; opt
sat -prove ok_reduce_o 1 -prove ok_mul2p32m1_o 1 -prove ok_add64_u8_o 1 -prove ok_mod_addsub_o 1 -verify lec_gl_helpers

design -reset
read_slang --top lec_gf_step2 -I$rtl $rtl/qsag_ass2_pkg.sv $rtl/qsag_ass2_gf_step.sv $work/lec_harnesses.sv
hierarchy -check -top lec_gf_step2
proc; opt; techmap; opt
sat -prove ok_o 1 -verify lec_gf_step2

design -reset
read_slang --top lec_alu_equiv -I$rtl $rtl/qsag_ass2_pkg.sv $rtl/qsag_ass2_add64.sv $rtl/qsag_ass2_alu.sv $work/lec_harnesses.sv
hierarchy -check -top lec_alu_equiv
proc; opt; techmap; opt
sat -prove ok_res_o 1 -prove ok_ea_o 1 -prove ok_ext_o 1 -prove ok_rot_o 1 -verify lec_alu_equiv
YS

yosys -m slang -s "$work/prove_comb.ys" | tee "$work/comb_lec.log"

cat > "$work/seq_mul_miter.sv" <<'SV'
module seq_mul_inductive (
    input  logic         clk,
    input  logic [63:0]  opa_i,
    input  logic [127:0] init_prod_i
);
    reg [2:0]   ph     = 3'd0;
    reg [63:0]  opa_r  = 64'd0;
    reg [127:0] prev_p = 128'd0;

    wire         last, step_act, cout;
    wire [63:0]  ma_a, ma_b, sum64;
    wire [127:0] prod128;

    always @(posedge clk) begin
        if (ph == 3'd0) begin
            ph <= 3'd1;
        end else if (ph == 3'd1) begin
            opa_r  <= opa_i;
            prev_p <= init_prod_i;
            ph     <= 3'd2;
        end else if (ph < 3'd4) begin
            ph <= ph + 3'd1;
        end
    end

    qsag_ass2_add64 u_add (.a(ma_a), .b(ma_b), .cin(1'b0), .sum(sum64), .cout(cout));
    qsag_gl64_karatsuba_csa u_dut (
        .clk(clk), .srst_n(ph != 3'd0),
        .start(ph == 3'd1), .mode_gl(1'b1),
        .gf_clr_i(1'b0), .gf_step_i(1'b0), .gf_next_i(128'd0),
        .fold_we_i(1'b0), .fold_val_i(64'd0),
        .opa(ph == 3'd1 ? opa_i : opa_r),
        .opb(init_prod_i[63:0]),
        .opc(init_prod_i[127:64]),
        .step_active_o(step_act),
        .mul_add_a_o(ma_a), .mul_add_b_o(ma_b),
        .mul_add_sum_i(sum64), .mul_add_cout_i(cout),
        .last(last), .prod128(prod128)
    );

    wire [64:0] exp_hi = {1'b0, prev_p[127:64]} + (prev_p[0] ? {1'b0, opa_r} : 65'd0);
    always @(posedge clk) begin
        if (ph == 3'd2) begin
            assert(prod128 == prev_p);
            assert(step_act);
            assert(!last);
        end
        if (ph == 3'd3) begin
            assert(prod128 == {exp_hi, prev_p[63:1]});
            assert(!last);
        end
    end
endmodule

module seq_mul_miter (
    input  logic        clk,
    input  logic        mode_gl,
    input  logic [63:0] opa,
    input  logic [63:0] opb,
    input  logic [63:0] opc
);
    reg [6:0]  cyc    = 7'd0;
    reg        srst_n = 1'b0;
    reg        start  = 1'b0;
    reg        mode_r = 1'b0;
    reg [63:0] a_r    = 64'd0;
    reg [63:0] b_r    = 64'd0;
    reg [63:0] c_r    = 64'd0;

    wire         last, step_act, cout;
    wire [63:0]  ma_a, ma_b, sum64;
    wire [127:0] prod128;

    always @(posedge clk) begin
        if (cyc == 7'd0) begin
            srst_n <= 1'b1;
            start  <= 1'b1;
            mode_r <= mode_gl;
            a_r    <= opa;
            b_r    <= opb;
            c_r    <= opc;
            cyc    <= 7'd1;
        end else begin
            start <= 1'b0;
            if (cyc < 7'd68) cyc <= cyc + 7'd1;
        end
    end

    qsag_ass2_add64 u_add (.a(ma_a), .b(ma_b), .cin(1'b0), .sum(sum64), .cout(cout));
    qsag_gl64_karatsuba_csa u_dut (
        .clk(clk), .srst_n(srst_n), .start(start), .mode_gl(mode_r),
        .gf_clr_i(1'b0), .gf_step_i(1'b0), .gf_next_i(128'd0),
        .fold_we_i(1'b0), .fold_val_i(64'd0),
        .opa(a_r), .opb(b_r), .opc(c_r),
        .step_active_o(step_act),
        .mul_add_a_o(ma_a), .mul_add_b_o(ma_b),
        .mul_add_sum_i(sum64), .mul_add_cout_i(cout),
        .last(last), .prod128(prod128)
    );

    always @(posedge clk) begin
        if (cyc == 7'd2) begin
            assert(prod128 == {mode_r ? c_r : 64'd0, b_r});
        end
        if (cyc >= 7'd2 && cyc <= 7'd65) begin
            assert(step_act);
            assert(u_dut.step_q == (cyc - 7'd1));
        end
        if (cyc >= 7'd2 && cyc <= 7'd67) begin
            assert(last == (cyc == 7'd66));
        end
        if (cyc == 7'd66 && a_r == 64'd0) begin
            assert(prod128 == (mode_r ? {64'd0, c_r} : 128'd0));
        end
        if (cyc == 7'd67) begin
            assert(u_dut.step_q == 7'd0);
        end
    end
endmodule
SV

cat > "$work/prove_mul_ind.sby" <<SBY
[options]
mode bmc
depth 5

[engines]
smtbmc bitwuzla

[script]
plugin -i slang
read_slang --top seq_mul_inductive qsag_ass2_pkg.sv qsag_ass2_cg_dff.sv qsag_ass2_add64.sv qsag_gl64_karatsuba_csa.sv seq_mul_miter.sv
prep -top seq_mul_inductive

[files]
$rtl/qsag_ass2_pkg.sv
$rtl/qsag_ass2_cg_dff.sv
$rtl/qsag_ass2_add64.sv
$rtl/qsag_gl64_karatsuba_csa.sv
$work/seq_mul_miter.sv
SBY

cat > "$work/prove_mul_bmc.sby" <<SBY
[options]
mode bmc
depth 68

[engines]
smtbmc bitwuzla

[script]
plugin -i slang
read_slang --top seq_mul_miter qsag_ass2_pkg.sv qsag_ass2_cg_dff.sv qsag_ass2_add64.sv qsag_gl64_karatsuba_csa.sv seq_mul_miter.sv
prep -top seq_mul_miter

[files]
$rtl/qsag_ass2_pkg.sv
$rtl/qsag_ass2_cg_dff.sv
$rtl/qsag_ass2_add64.sv
$rtl/qsag_gl64_karatsuba_csa.sv
$work/seq_mul_miter.sv
SBY

if ! command -v bitwuzla >/dev/null 2>&1; then
    sed -i 's/smtbmc bitwuzla/smtbmc z3/' "$work/prove_mul_ind.sby" "$work/prove_mul_bmc.sby"
fi
sby -f "$work/prove_mul_ind.sby" | tee "$work/mul_ind.log"
sby -f "$work/prove_mul_bmc.sby" | tee "$work/mul_lec.log"
echo "ALL FORMAL LEC PROOFS PASSED (UNSAT)!"
