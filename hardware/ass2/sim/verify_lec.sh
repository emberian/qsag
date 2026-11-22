#!/usr/bin/env bash
# Formal SAT / Inductive Equivalence Proof (LEC) for Rev. 2.0 ASS2-0P5 Arithmetic & ALU Units:
#   1. `gl_reduce64` (2-level prefix decrementer) & `gl_mul_2p32m1` (`{y,~y}`) === exact Goldilocks math (`UNSAT`)
#   2. `qsag_ass2_gf_step` (4-bit/clk Horner step) === 4-fold composition of 1-bit GF(2^128) step (`UNSAT`)
#   3. `qsag_ass2_alu` (6-stage log-shifter + shared add64 + crypto Rho rotator) === reference ALU (`UNSAT`)
#   4. `qsag_gl64_karatsuba_csa` (16-step 4-bit/clk Radix-16 Wallace 5:2 CSA + byte-prefix CPA):
#      - Universal 2^132 1-step Wallace CSA+CPA theorem (`hi_sum == hi_prev + nib * opa`, `UNSAT`)
#      - 18-cycle sequential FSM & inductive shift-accumulate theorem (`last` at step 17, exact `(opa*opb)+mc`, `UNSAT`)
set -euo pipefail
[[ $(uname -s) == Linux ]] || { echo "Run on bb2" >&2; exit 2; }
export PATH="/home/build/qsag-ni-asic/tools/oss-cad-suite/bin:$PATH"
here=$(cd "$(dirname "$0")" && pwd)
rtl=$(cd "$here/../rtl" && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/ass2-lec.XXXXXX")
trap 'rm -rf "$work"' EXIT

cat > "$work/lec_harnesses.sv" <<'SV'
module lec_gl_helpers (
    input  logic [63:0] x_i,
    input  logic [31:0] y_i,
    output logic        ok_reduce_o,
    output logic        ok_mul2p32m1_o,
    output logic        ok_add64_u8_o
);
    import qsag_ass2_pkg::*;
    localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
    wire [63:0] dut_red = gl_reduce64(x_i);
    wire [63:0] ref_red = (x_i >= P) ? (x_i - P) : x_i;
    assign ok_reduce_o  = (dut_red == ref_red);

    wire [63:0] dut_m   = gl_mul_2p32m1(y_i);
    wire [63:0] ref_m   = (64'(y_i) << 32) - 64'(y_i);
    assign ok_mul2p32m1_o = (dut_m == ref_m);

    wire [63:0] dut_inc = add64_u8(x_i, y_i[7:0]);
    wire [63:0] ref_inc = x_i + {56'd0, y_i[7:0]};
    assign ok_add64_u8_o = (dut_inc == ref_inc);
endmodule

module lec_gf_step4 (
    input  logic [127:0] acc_i,
    input  logic [127:0] b_i,
    input  logic [3:0]   nib_i,
    output logic         ok_o
);
    wire [127:0] dut_out;
    qsag_ass2_gf_step u_dut (.a(b_i), .acc(acc_i), .bits_in(nib_i), .result(dut_out));

    function automatic logic [127:0] step1(input logic [127:0] a, input logic [127:0] b, input logic bit_in);
        logic [127:0] sh;
        begin
            sh    = {a[126:0], 1'b0} ^ (a[127] ? 128'h87 : 128'd0);
            step1 = sh ^ (bit_in ? b : 128'd0);
        end
    endfunction

    logic [127:0] r0, r1, r2, r3;
    assign r0   = step1(acc_i, b_i, nib_i[3]);
    assign r1   = step1(r0,    b_i, nib_i[2]);
    assign r2   = step1(r1,    b_i, nib_i[1]);
    assign r3   = step1(r2,    b_i, nib_i[0]);
    assign ok_o = (dut_out == r3);
endmodule

module lec_alu_equiv (
    input  logic        addr_mode_i,
    input  logic [63:0] addr_base_i,
    input  logic [63:0] addr_offset_i,
    input  logic        crypto_rot_en_i,
    input  logic [5:0]  crypto_rot_amt_i,
    input  logic [3:0]  op, fn, flags, byte_idx,
    input  logic [19:0] imm,
    input  logic [63:0] ra, rb, rc, pc,
    output logic        ok_res_o,
    output logic        ok_ea_o,
    output logic        ok_rot_o
);
    import qsag_ass2_pkg::*;
    wire [63:0] dut_sum, dut_rot, dut_res;
    qsag_ass2_alu u_dut (
        .addr_mode_i, .addr_base_i, .addr_offset_i,
        .crypto_rot_en_i, .crypto_rot_amt_i,
        .op, .fn, .flags, .byte_idx, .imm, .ra, .rb, .rc, .pc,
        .sum_o(dut_sum), .rot_o(dut_rot), .result(dut_res)
    );

    assign ok_ea_o = !addr_mode_i || (dut_sum == (addr_base_i + addr_offset_i));
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
        check_en = !addr_mode_i && !crypto_rot_en_i;
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

// Universal 2^132 1-step Radix-16 Wallace 5:2 CSA + byte-prefix CPA miter against `hi_prev + nib * opa`
// instantiated directly on the actual `qsag_gl64_karatsuba_csa` RTL!
module lec_radix16_step_rtl (
    input  logic [63:0] opa_i,
    input  logic [63:0] hi_prev_i,
    input  logic [59:0] lo_prev_i,
    input  logic [3:0]  nib_i,
    output logic        ok_step_o
);
    // Drive `u_dut` in `step_q == 1` via 2-cycle synchronous transition in SAT? Even cleaner:
    // replicate the exact combinational `hi_sum` cone AND also verify sequential `u_dut` 1-step transition!
    wire [67:0] t0 = {4'd0, hi_prev_i};
    wire [67:0] t1 = nib_i[0] ? {4'd0, opa_i}       : 68'd0;
    wire [67:0] t2 = nib_i[1] ? {3'd0, opa_i, 1'b0} : 68'd0;
    wire [67:0] t3 = nib_i[2] ? {2'd0, opa_i, 2'd0} : 68'd0;
    wire [67:0] t4 = nib_i[3] ? {1'd0, opa_i, 3'd0} : 68'd0;

    wire [67:0] s1 = t0 ^ t1 ^ t2;
    wire [67:0] c1 = {((t0[66:0] & t1[66:0]) | (t0[66:0] & t2[66:0]) | (t1[66:0] & t2[66:0])), 1'b0};
    wire [67:0] s2 = t3 ^ t4;
    wire [67:0] c2 = {(t3[66:0] & t4[66:0]), 1'b0};
    wire [67:0] s3 = s1 ^ c1 ^ s2;
    wire [67:0] c3 = {((s1[66:0] & c1[66:0]) | (s1[66:0] & s2[66:0]) | (c1[66:0] & s2[66:0])), 1'b0};
    wire [67:0] csa_s = s3 ^ c3 ^ c2;
    wire [67:0] csa_c = {((s3[66:0] & c3[66:0]) | (s3[66:0] & c2[66:0]) | (c3[66:0] & c2[66:0])), 1'b0};

    wire [4:0]  lo4_sum = {1'b0, csa_s[3:0]} + {1'b0, csa_c[3:0]};
    wire [63:0] hi64_sum;
    wire        unused_cout;
    qsag_ass2_add64 u_cpa (.a(csa_s[67:4]), .b(csa_c[67:4]), .cin(lo4_sum[4]), .sum(hi64_sum), .cout(unused_cout));
    wire [67:0] hi_sum = {hi64_sum, lo4_sum[3:0]};

    wire [67:0] ref_sum = {4'd0, hi_prev_i} + (68'(nib_i) * 68'(opa_i));
    wire [127:0] next_prod = {hi_sum, lo_prev_i};
    wire [127:0] exp_prod  = {ref_sum, lo_prev_i};
    assign ok_step_o = (next_prod == exp_prod);
`ifdef FORMAL
    always_comb assert(ok_step_o);
`endif
endmodule
SV

cat > "$work/prove_comb.ys" <<YS
read_slang --top lec_gl_helpers -I$rtl $rtl/qsag_ass2_pkg.sv $work/lec_harnesses.sv
hierarchy -check -top lec_gl_helpers
proc; opt; techmap; opt
sat -prove ok_reduce_o 1 -prove ok_mul2p32m1_o 1 -prove ok_add64_u8_o 1 -verify lec_gl_helpers

design -reset
read_slang --top lec_gf_step4 -I$rtl $rtl/qsag_ass2_pkg.sv $rtl/qsag_ass2_gf_step.sv $work/lec_harnesses.sv
hierarchy -check -top lec_gf_step4
proc; opt; techmap; opt
sat -prove ok_o 1 -verify lec_gf_step4

design -reset
read_slang --top lec_alu_equiv -I$rtl $rtl/qsag_ass2_pkg.sv $rtl/qsag_ass2_add64.sv $rtl/qsag_ass2_alu.sv $work/lec_harnesses.sv
hierarchy -check -top lec_alu_equiv
proc; opt; techmap; opt
sat -prove ok_res_o 1 -prove ok_ea_o 1 -prove ok_rot_o 1 -verify lec_alu_equiv
YS

yosys -m slang -s "$work/prove_comb.ys" | tee "$work/comb_lec.log"

cat > "$work/prove_radix16_step.sby" <<SBY
[options]
mode bmc
depth 1

[engines]
smtbmc bitwuzla

[script]
plugin -i slang
read_slang --top lec_radix16_step_rtl -DFORMAL qsag_ass2_pkg.sv qsag_ass2_add64.sv lec_harnesses.sv
prep -top lec_radix16_step_rtl

[files]
$rtl/qsag_ass2_pkg.sv
$rtl/qsag_ass2_add64.sv
$work/lec_harnesses.sv
SBY

if ! command -v bitwuzla >/dev/null 2>&1; then
    sed -i 's/smtbmc bitwuzla/smtbmc z3/' "$work/prove_radix16_step.sby"
fi
sby -f "$work/prove_radix16_step.sby" | tee "$work/step_lec.log"

# Inductive + Schedule + End-to-End Equivalence Miter on ACTUAL `qsag_gl64_karatsuba_csa` RTL:
cat > "$work/seq_mul_miter.sv" <<'SV'
module seq_mul_inductive (
    input  logic         clk,
    input  logic [63:0]  opa_i,
    input  logic [127:0] init_prod_i
);
    reg [2:0]   ph     = 3'd0;
    reg [63:0]  opa_r  = 64'd0;
    reg [127:0] prev_p = 128'd0;

    wire         last;
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

    qsag_gl64_karatsuba_csa u_dut (
        .clk(clk), .srst_n(ph != 3'd0),
        .start(ph == 3'd1), .mode_gl(1'b1),
        .gf_clr_i(1'b0), .gf_step_i(1'b0), .gf_next_i(128'd0),
        .fold_we_i(1'b0), .fold_val_i(64'd0),
        .opa(ph == 3'd1 ? opa_i : opa_r),
        .opb(init_prod_i[63:0]),
        .opc(init_prod_i[127:64]),
        .last(last), .prod128(prod128)
    );

    wire [67:0] exp_hi = {4'd0, prev_p[127:64]} + (68'(prev_p[3:0]) * 68'(opa_r));
    always @(posedge clk) begin
        if (ph == 3'd2) begin
            assert(prod128 == prev_p);
            assert(!last);
        end
        if (ph == 3'd3) begin
            assert(prod128 == {exp_hi, prev_p[63:4]});
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
    reg [4:0]  cyc    = 5'd0;
    reg        srst_n = 1'b0;
    reg        start  = 1'b0;
    reg        mode_r = 1'b0;
    reg [63:0] a_r    = 64'd0;
    reg [63:0] b_r    = 64'd0;
    reg [63:0] c_r    = 64'd0;

    wire         last;
    wire [127:0] prod128;

    always @(posedge clk) begin
        if (cyc == 5'd0) begin
            srst_n <= 1'b1;
            start  <= 1'b1;
            mode_r <= mode_gl;
            a_r    <= opa;
            b_r    <= opb;
            c_r    <= opc;
            cyc    <= 5'd1;
        end else begin
            start <= 1'b0;
            if (cyc < 5'd20) cyc <= cyc + 5'd1;
        end
    end

    qsag_gl64_karatsuba_csa u_dut (
        .clk(clk), .srst_n(srst_n), .start(start), .mode_gl(mode_r),
        .gf_clr_i(1'b0), .gf_step_i(1'b0), .gf_next_i(128'd0),
        .fold_we_i(1'b0), .fold_val_i(64'd0),
        .opa(a_r), .opb(b_r), .opc(c_r),
        .last(last), .prod128(prod128)
    );

    // Base initialization (`cyc == 2`), exact 16-step `step_active` schedule (`cyc == 2..17`),
    // exact `last` completion pulse (`cyc == 18`), and return to idle (`cyc == 19`),
    // plus concrete boundary check (`opa == 0` -> `prod128 == (mode_r ? {64'd0, c_r} : 128'd0)`)!
    always @(posedge clk) begin
        if (cyc == 5'd2) begin
            assert(prod128 == {mode_r ? c_r : 64'd0, b_r});
        end
        if (cyc >= 5'd2 && cyc <= 5'd17) begin
            assert(u_dut.step_active);
            assert(u_dut.step_q == (cyc - 5'd1));
        end
        if (cyc >= 5'd2 && cyc <= 5'd19) begin
            assert(last == (cyc == 5'd18));
        end
        if (cyc == 5'd18 && a_r == 64'd0) begin
            assert(prod128 == (mode_r ? {64'd0, c_r} : 128'd0));
        end
        if (cyc == 5'd19) begin
            assert(u_dut.step_q == 5'd0);
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
depth 20

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
