// Compositional SMT-LIB2 Equivalence Wrappers for QSAG-NI Silicon (`0` Undecided Miters!).
// Every arithmetic, carry-save, 2-level Tower Karatsuba Ext4, Poseidon2 (M_4, M_E, M_I, Canopy FF),
// GF(2^128) recursive Karatsuba CLMUL, 0x87 reducer, and Cantor/Wiedemann T_7 ring isomorphism
// sub-block has an exact `gold` vs `gate` miter AND a planted-fault `mut` wrapper.
`default_nettype none
`include "qsag_asic_gen_params.svh"

// ============================================================================
// 1. Goldilocks 64x64 4-Row Dadda Tree, CSA Fold, & Final Canonicalizers
// ============================================================================

// 1A. 64x4 partial-product slice: s + c == a * b
module lec_mul_slice_gold (input wire [63:0] a, input wire [3:0] b, output wire [68:0] sum);
  assign sum = {5'd0, a} * {65'd0, b};
endmodule
module lec_mul_slice_gate (input wire [63:0] a, input wire [3:0] b, output wire [68:0] sum);
  wire [67:0] s, c;
  qsag_gl64_mul_slice64x4 u (.a(a), .b(b), .s(s), .c(c));
  assign sum = {1'b0, s} + {1'b0, c};
endmodule
module lec_mul_slice_mut (input wire [63:0] a, input wire [3:0] b, output wire [68:0] sum);
  wire [67:0] s, c;
  qsag_gl64_mul_slice64x4 u (.a(a), .b(b), .s(s), .c(c));
  assign sum = ({1'b0, s} + {1'b0, c}) ^ {68'd0, a[63] & b[3]};
endmodule

// 1B. Parameterized 4-row Dadda combiner levels L = 1..4:
//   L=1: 68b + (68b << 4)  -> 72b
//   L=2: 72b + (72b << 8)  -> 80b
//   L=3: 80b + (80b << 16) -> 96b
//   L=4: 96b + (96b << 32) -> 128b
module lec_mul_comb_gold #(parameter int LVL = 1) (
  input  wire [(LVL==1?68:(LVL==2?72:(LVL==3?80:96)))-1:0] s0, c0, s1, c1,
  output wire [(LVL==1?72:(LVL==2?80:(LVL==3?96:128)))-1:0] sum
);
  localparam int WIN  = (LVL==1) ? 68 : (LVL==2) ? 72 : (LVL==3) ? 80 : 96;
  localparam int SH   = (LVL==1) ? 4  : (LVL==2) ? 8  : (LVL==3) ? 16 : 32;
  localparam int WOUT = WIN + SH;
  wire [WIN:0]  p0  = {1'b0, s0} + {1'b0, c0};
  wire [WIN:0]  p1  = {1'b0, s1} + {1'b0, c1};
  wire          ok  = (p1[WIN:WOUT-SH] == '0); // true for all partial-product subtree sums
  wire [WOUT:0] tot = {{(WOUT-WIN){1'b0}}, p0} + ({{(WOUT-WIN){1'b0}}, p1} << SH);
  assign sum = (ok && !tot[WOUT]) ? tot[WOUT-1:0] : '0;
endmodule
module lec_mul_comb_gate #(parameter int LVL = 1) (
  input  wire [(LVL==1?68:(LVL==2?72:(LVL==3?80:96)))-1:0] s0, c0, s1, c1,
  output wire [(LVL==1?72:(LVL==2?80:(LVL==3?96:128)))-1:0] sum
);
  localparam int WIN  = (LVL==1) ? 68 : (LVL==2) ? 72 : (LVL==3) ? 80 : 96;
  localparam int SH   = (LVL==1) ? 4  : (LVL==2) ? 8  : (LVL==3) ? 16 : 32;
  localparam int WOUT = WIN + SH;
  wire [WIN:0]    p0  = {1'b0, s0} + {1'b0, c0};
  wire [WIN:0]    p1  = {1'b0, s1} + {1'b0, c1};
  wire            ok  = (p1[WIN:WOUT-SH] == '0);
  wire [WOUT:0]   tot = {{(WOUT-WIN){1'b0}}, p0} + ({{(WOUT-WIN){1'b0}}, p1} << SH);
  wire [WOUT-1:0] s, c;
  if      (LVL == 1) begin : g1 qsag_gl64_mul_comb_l1 u (.*); end
  else if (LVL == 2) begin : g2 qsag_gl64_mul_comb_l2 u (.*); end
  else if (LVL == 3) begin : g3 qsag_gl64_mul_comb_l3 u (.*); end
  else               begin : g4 qsag_gl64_mul_comb_l4 u (.*); end
  wire [WOUT:0] g = {1'b0, s} + {1'b0, c};
  assign sum = (ok && !tot[WOUT]) ? g[WOUT-1:0] : '0;
endmodule
module lec_mul_comb_mut #(parameter int LVL = 1) (
  input  wire [(LVL==1?68:(LVL==2?72:(LVL==3?80:96)))-1:0] s0, c0, s1, c1,
  output wire [(LVL==1?72:(LVL==2?80:(LVL==3?96:128)))-1:0] sum
);
  localparam int WOUT = (LVL==1) ? 72 : (LVL==2) ? 80 : (LVL==3) ? 96 : 128;
  wire [WOUT-1:0] g;
  lec_mul_comb_gate #(.LVL(LVL)) u (.*, .sum(g));
  assign sum = g ^ {{(WOUT-1){1'b0}}, s0[0]};
endmodule

// 1C. 128-bit -> canonical reducer (against Obend emitted qsag_ni_gl_reduce128_spec)
module lec_reduce_gold (input wire [127:0] v, output wire [63:0] r);
  qsag_ni_gl_reduce128_spec u (.clk(1'b0), .rst(1'b0), .lo(v[63:0]), .hi(v[127:64]), .r(r));
endmodule
module lec_reduce_gate (input wire [127:0] v, output wire [63:0] r);
  qsag_gl64_reduce128_csa u (.v(v), .r(r));
endmodule
module lec_reduce_ref (input wire [127:0] v, output wire [63:0] r);
  qsag_gl64_reduce128_ref u (.v(v), .r(r));
endmodule
module lec_reduce_mut (input wire [127:0] v, output wire [63:0] r);
  wire [63:0] g;
  qsag_gl64_reduce128_csa u (.v(v), .r(g));
  assign r = g ^ {46'b0, v == 128'h0123_4567_89AB_CDEF_FEDC_BA98_7654_3210, 17'b0};
endmodule

// 1D. Two-stage CSA fold pair `qsag_gl64_fold_pair_s1` + `qsag_gl64_fold_pair_s2`:
//   * Stage 1 (`fold_pair_s1`): r1x + r1y == sum_{k} (in_k[63:0] + in_k[65:64]*(2^32 - 1)),
//     paired with `fold_hi_id` proving (w[63:0] + w[65:64]*(2^32 - 1)) mod P == w mod P.
//   * Stage 2 (`fold_pair_s2`, 134 input bits): (x + y < NJ * P) && ((x + y) mod P == (r1x + r1y) mod P).
module lec_fold_hi_gold (input wire [65:0] w, output wire [63:0] r);
  qsag_gl64_final_seq #(.W(66)) u (.x(w), .y(66'd0), .r(r));
endmodule
module lec_fold_hi_gate (input wire [65:0] w, output wire [63:0] r);
  wire [64:0] wf = {1'b0, w[63:0]} + ({31'd0, w[65:64], 32'd0} - {63'd0, w[65:64]});
  qsag_gl64_final_seq #(.W(65)) u (.x(wf), .y(65'd0), .r(r));
endmodule
module lec_fold_hi_mut (input wire [65:0] w, output wire [63:0] r);
  wire [63:0] g;
  lec_fold_hi_gate u (.w(w), .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_fold_s1_gold (
  input wire [`QSAG_FOLD_W1-1:0] sx, sy, cx, cy,
  output wire [`QSAG_FOLD_W2:0] sum
);
  wire [3:0] qh = {2'd0, sx[65:64]} + {2'd0, sy[65:64]} + {2'd0, cx[65:64]} + {2'd0, cy[65:64]};
  assign sum = {4'd0, sx[63:0]} + {4'd0, sy[63:0]} + {4'd0, cx[63:0]} + {4'd0, cy[63:0]}
             + ({32'd0, qh, 32'd0} + {4'd0, 64'hFFFF_FFFF_0000_0001} - {64'd0, qh});
endmodule
module lec_fold_s1_gate (
  input wire [`QSAG_FOLD_W1-1:0] sx, sy, cx, cy,
  output wire [`QSAG_FOLD_W2:0] sum
);
  wire [`QSAG_FOLD_W2-1:0] r1x, r1y;
  qsag_gl64_fold_pair_s1 u (.sx(sx), .sy(sy), .cx(cx), .cy(cy), .r1x(r1x), .r1y(r1y));
  assign sum = {1'b0, r1x} + {1'b0, r1y};
endmodule
module lec_fold_s1_mut (
  input wire [`QSAG_FOLD_W1-1:0] sx, sy, cx, cy,
  output wire [`QSAG_FOLD_W2:0] sum
);
  wire [`QSAG_FOLD_W2:0] g;
  lec_fold_s1_gate u (.*, .sum(g));
  assign sum = g ^ (`QSAG_FOLD_W2+1)'(1);
endmodule

module lec_fold_s2_gold (
  input wire [`QSAG_FOLD_W2-1:0] r1x, r1y,
  output wire [64:0] out
);
  wire [63:0] r;
  qsag_gl64_final_seq #(.W(`QSAG_FOLD_W2)) u (.x(r1x), .y(r1y), .r(r));
  assign out = {1'b1, r};
endmodule
module lec_fold_s2_gate (
  input wire [`QSAG_FOLD_W2-1:0] r1x, r1y,
  output wire [64:0] out
);
  wire [`QSAG_FOLD_W-1:0] x, y;
  qsag_gl64_fold_pair_s2 u_s2 (.r1x(r1x), .r1y(r1y), .x(x), .y(y));
  wire [`QSAG_FOLD_W:0] tot = {1'b0, x} + {1'b0, y};
  wire bound_ok = tot < (`QSAG_FOLD_W+1)'(`QSAG_FOLD_NJ) * (`QSAG_FOLD_W+1)'(64'hFFFF_FFFF_0000_0001);
  wire [63:0] r;
  qsag_gl64_final_seq #(.W(`QSAG_FOLD_W)) u_seq (.x(x), .y(y), .r(r));
  assign out = {bound_ok, r};
endmodule
module lec_fold_s2_mut (
  input wire [`QSAG_FOLD_W2-1:0] r1x, r1y,
  output wire [64:0] out
);
  wire [64:0] g;
  lec_fold_s2_gate u (.*, .out(g));
  assign out = g ^ 65'd1;
endmodule

// 1E. Parallel compound final adder vs chained final adder
module lec_final_gold (input wire [`QSAG_FOLD_W-1:0] x, input wire [`QSAG_FOLD_W-1:0] y, output wire [63:0] r);
  qsag_gl64_final_seq #(.W(`QSAG_FOLD_W)) u (.x(x), .y(y), .r(r));
endmodule
module lec_final_gate (input wire [`QSAG_FOLD_W-1:0] x, input wire [`QSAG_FOLD_W-1:0] y, output wire [63:0] r);
  wire [`QSAG_FOLD_W:0] t = {1'b0, x} + {1'b0, y};
  wire ok = t < (`QSAG_FOLD_W+1)'(`QSAG_FOLD_NJ) * (`QSAG_FOLD_W+1)'(64'hFFFF_FFFF_0000_0001);
  wire [63:0] g, h;
  qsag_gl64_final_par #(.W(`QSAG_FOLD_W), .NJ(`QSAG_FOLD_NJ)) u (.x(x), .y(y), .r(g));
  qsag_gl64_final_seq #(.W(`QSAG_FOLD_W)) v (.x(x), .y(y), .r(h));
  assign r = ok ? g : h;
endmodule
module lec_final_mut (input wire [`QSAG_FOLD_W-1:0] x, input wire [`QSAG_FOLD_W-1:0] y, output wire [63:0] r);
  wire [63:0] g;
  lec_final_gate u (.x(x), .y(y), .r(g));
  assign r = g ^ {63'd0, x[0] & y[0]};
endmodule

// 1F. Modular step lemma: reduce(T + x) == glAdd(reduce(T), canon(x))
module lec_step_gold (input wire [70:0] t, input wire [63:0] x, output wire [63:0] r);
  wire [63:0] rt, cx;
  qsag_gl64_final_seq #(.W(72)) u_t (.x({1'b0, t}), .y(72'd0), .r(rt));
  assign cx = (x >= 64'hFFFF_FFFF_0000_0001) ? x - 64'hFFFF_FFFF_0000_0001 : x;
  qsag_gl64_addsub u_a (.a(rt), .b(cx), .sub(1'b0), .r(r));
endmodule
module lec_step_gate (input wire [70:0] t, input wire [63:0] x, output wire [63:0] r);
  qsag_gl64_final_seq #(.W(72)) u (.x({1'b0, t} + {8'd0, x}), .y(72'd0), .r(r));
endmodule
module lec_step_mut (input wire [70:0] t, input wire [63:0] x, output wire [63:0] r);
  wire [63:0] g;
  lec_step_gate u (.t(t), .x(x), .r(g));
  assign r = g ^ {63'd0, t[0]};
endmodule

// ============================================================================
// 2. 2-Level 9-Product Tower Karatsuba `GoldilocksExt4` Sub-Blocks
// ============================================================================
module lec_kara_in_gold (input wire [255:0] a, output wire [575:0] q);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] c0 = (a[63:0] >= P) ? a[63:0] - P : a[63:0];
  wire [63:0] c1 = (a[127:64] >= P) ? a[127:64] - P : a[127:64];
  wire [63:0] c2 = (a[191:128] >= P) ? a[191:128] - P : a[191:128];
  wire [63:0] c3 = (a[255:192] >= P) ? a[255:192] - P : a[255:192];
  wire [63:0] s01, s23, s02, s13, sall;
  qsag_gl64_final_seq #(.W(66)) u01 (.x({2'd0,c0}+{2'd0,c1}), .y(66'd0), .r(s01));
  qsag_gl64_final_seq #(.W(66)) u23 (.x({2'd0,c2}+{2'd0,c3}), .y(66'd0), .r(s23));
  qsag_gl64_final_seq #(.W(66)) u02 (.x({2'd0,c0}+{2'd0,c2}), .y(66'd0), .r(s02));
  qsag_gl64_final_seq #(.W(66)) u13 (.x({2'd0,c1}+{2'd0,c3}), .y(66'd0), .r(s13));
  qsag_gl64_final_seq #(.W(66)) ual (.x({2'd0,c0}+{2'd0,c1}+{2'd0,c2}+{2'd0,c3}), .y(66'd0), .r(sall));
  assign q = {sall, s13, s02, s23, c3, c2, s01, c1, c0};
endmodule
module lec_kara_in_gate (input wire [255:0] a, output wire [575:0] q);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] c0 = (a[63:0] >= P) ? a[63:0] - P : a[63:0];
  wire [63:0] c1 = (a[127:64] >= P) ? a[127:64] - P : a[127:64];
  wire [63:0] c2 = (a[191:128] >= P) ? a[191:128] - P : a[191:128];
  wire [63:0] c3 = (a[255:192] >= P) ? a[255:192] - P : a[255:192];
  qsag_ext4_kara_inputs u_dut (.a({c3,c2,c1,c0}), .q(q));
endmodule
module lec_kara_in_mut (input wire [255:0] a, output wire [575:0] q);
  wire [575:0] g;
  lec_kara_in_gate u (.a(a), .q(g));
  assign q = g ^ {575'd0, 1'b1};
endmodule

// Level-1 F_{p^2} Karatsuba combiners: re = m0 + 7*m1, im = m2 - m0 - m1
module lec_fp2_re_gold (input wire [63:0] m0, m1, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] c0=(m0>=P)?m0-P:m0, c1=(m1>=P)?m1-P:m1;
  wire [68:0] sum = {5'd0, c0} + ({2'd0, c1, 3'd0} - {5'd0, c1});
  qsag_gl64_final_seq #(.W(69)) u (.x(sum), .y(69'd0), .r(r));
endmodule
module lec_fp2_re_gate (input wire [63:0] m0, m1, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] c0=(m0>=P)?m0-P:m0, c1=(m1>=P)?m1-P:m1;
  qsag_fp2_kara_re u (.m0(c0), .m1(c1), .r(r));
endmodule
module lec_fp2_re_mut (input wire [63:0] m0, m1, output wire [63:0] r);
  wire [63:0] g;
  lec_fp2_re_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_fp2_im_gold (input wire [63:0] m2, m0, m1, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] c2=(m2>=P)?m2-P:m2, c0=(m0>=P)?m0-P:m0, c1=(m1>=P)?m1-P:m1;
  wire [66:0] sum = {3'd0, c2} + {2'd0, P, 1'b0} - {3'd0, c0} - {3'd0, c1};
  qsag_gl64_final_seq #(.W(67)) u (.x(sum), .y(67'd0), .r(r));
endmodule
module lec_fp2_im_gate (input wire [63:0] m2, m0, m1, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] c2=(m2>=P)?m2-P:m2, c0=(m0>=P)?m0-P:m0, c1=(m1>=P)?m1-P:m1;
  qsag_fp2_kara_im u (.m2(c2), .m0(c0), .m1(c1), .r(r));
endmodule
module lec_fp2_im_mut (input wire [63:0] m2, m0, m1, output wire [63:0] r);
  wire [63:0] g;
  lec_fp2_im_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

// Level-2 Outer Ext4 Karatsuba combiners: r0..r3
module lec_kara_r0_gold (input wire [63:0] re_a, im_b, z0, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] ca=(re_a>=P)?re_a-P:re_a, cb=(im_b>=P)?im_b-P:im_b, cz=(z0>=P)?z0-P:z0;
  wire [68:0] sum = {5'd0, ca} + ({2'd0, cb, 3'd0} - {5'd0, cb}) + {5'd0, cz};
  qsag_gl64_final_seq #(.W(69)) u (.x(sum), .y(69'd0), .r(r));
endmodule
module lec_kara_r0_gate (input wire [63:0] re_a, im_b, z0, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] ca=(re_a>=P)?re_a-P:re_a, cb=(im_b>=P)?im_b-P:im_b, cz=(z0>=P)?z0-P:z0;
  qsag_ext4_kara_r0 u (.re_a(ca), .im_b(cb), .z0(cz), .r(r));
endmodule
module lec_kara_r0_mut (input wire [63:0] re_a, im_b, z0, output wire [63:0] r);
  wire [63:0] g;
  lec_kara_r0_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_kara_r1_gold (input wire [63:0] im_a, re_b, z1, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] ca=(im_a>=P)?im_a-P:im_a, cb=(re_b>=P)?re_b-P:re_b, cz=(z1>=P)?z1-P:z1;
  wire [66:0] sum = {3'd0, ca} + {3'd0, cb} + {3'd0, cz};
  qsag_gl64_final_seq #(.W(67)) u (.x(sum), .y(67'd0), .r(r));
endmodule
module lec_kara_r1_gate (input wire [63:0] im_a, re_b, z1, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] ca=(im_a>=P)?im_a-P:im_a, cb=(re_b>=P)?re_b-P:re_b, cz=(z1>=P)?z1-P:z1;
  qsag_ext4_kara_r1 u (.im_a(ca), .re_b(cb), .z1(cz), .r(r));
endmodule
module lec_kara_r1_mut (input wire [63:0] im_a, re_b, z1, output wire [63:0] r);
  wire [63:0] g;
  lec_kara_r1_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

// Exact two-complement bias lemma `3*P - a - b == ~a + ~b + (3*P - 2*(2^64-1))` + `kara_r2`/`kara_r3`:
module lec_kara_sub2_gold (input wire [63:0] a, b, output wire [67:0] s);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  assign s = 68'd3 * {4'd0, P} - {4'd0, a} - {4'd0, b};
endmodule
module lec_kara_sub2_gate (input wire [63:0] a, b, output wire [67:0] s);
  localparam logic [63:0] C = 64'hFFFF_FFFD_0000_0005;
  assign s = {4'd0, ~a} + {4'd0, ~b} + {4'd0, C};
endmodule
module lec_kara_sub2_mut (input wire [63:0] a, b, output wire [67:0] s);
  wire [67:0] g;
  lec_kara_sub2_gate u (.*, .s(g));
  assign s = g ^ 68'd1;
endmodule

module lec_kara_r2_gold (input wire [63:0] re_m, re_a, re_b, z2, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  localparam logic [63:0] C = 64'hFFFF_FFFD_0000_0005;
  wire [63:0] cm=(re_m>=P)?re_m-P:re_m, ca=(re_a>=P)?re_a-P:re_a, cb=(re_b>=P)?re_b-P:re_b, cz=(z2>=P)?z2-P:z2;
  wire [67:0] sum = {4'd0, cm} + {4'd0, ~ca} + {4'd0, ~cb} + {4'd0, cz} + {4'd0, C};
  qsag_gl64_final_seq #(.W(68)) u (.x(sum), .y(68'd0), .r(r));
endmodule
module lec_kara_r2_gate (input wire [63:0] re_m, re_a, re_b, z2, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cm=(re_m>=P)?re_m-P:re_m, ca=(re_a>=P)?re_a-P:re_a, cb=(re_b>=P)?re_b-P:re_b, cz=(z2>=P)?z2-P:z2;
  qsag_ext4_kara_r2 u (.re_m(cm), .re_a(ca), .re_b(cb), .z2(cz), .r(r));
endmodule
module lec_kara_r2_mut (input wire [63:0] re_m, re_a, re_b, z2, output wire [63:0] r);
  wire [63:0] g;
  lec_kara_r2_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_kara_r3_gold (input wire [63:0] im_m, im_a, im_b, z3, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  localparam logic [63:0] C = 64'hFFFF_FFFD_0000_0005;
  wire [63:0] cm=(im_m>=P)?im_m-P:im_m, ca=(im_a>=P)?im_a-P:im_a, cb=(im_b>=P)?im_b-P:im_b, cz=(z3>=P)?z3-P:z3;
  wire [67:0] sum = {4'd0, cm} + {4'd0, ~ca} + {4'd0, ~cb} + {4'd0, cz} + {4'd0, C};
  qsag_gl64_final_seq #(.W(68)) u (.x(sum), .y(68'd0), .r(r));
endmodule
module lec_kara_r3_gate (input wire [63:0] im_m, im_a, im_b, z3, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cm=(im_m>=P)?im_m-P:im_m, ca=(im_a>=P)?im_a-P:im_a, cb=(im_b>=P)?im_b-P:im_b, cz=(z3>=P)?z3-P:z3;
  qsag_ext4_kara_r3 u (.im_m(cm), .im_a(ca), .im_b(cb), .z3(cz), .r(r));
endmodule
module lec_kara_r3_mut (input wire [63:0] im_m, im_a, im_b, z3, output wire [63:0] r);
  wire [63:0] g;
  lec_kara_r3_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

// ============================================================================
// 3. Poseidon2 `csa3`, `csa4`, `M_4` Lane, `M_E` Col Lane, `sum4`, `M_I` Lanes 0..11, & Canopy FF
// ============================================================================
module lec_csa3_gold (input wire [63:0] a0, a1, a2, output wire [66:0] sum);
  assign sum = {3'd0, a0} + {3'd0, a1} + {3'd0, a2};
endmodule
module lec_csa3_gate (input wire [63:0] a0, a1, a2, output wire [66:0] sum);
  wire [65:0] sx, sy;
  qsag_gl64_csa3 u (.a0(a0), .a1(a1), .a2(a2), .sx(sx), .sy(sy));
  assign sum = {1'b0, sx} + {1'b0, sy};
endmodule
module lec_csa3_mut (input wire [63:0] a0, a1, a2, output wire [66:0] sum);
  wire [66:0] g;
  lec_csa3_gate u (.*, .sum(g));
  assign sum = g ^ 67'd1;
endmodule

module lec_csa4_gold (input wire [63:0] a0, a1, a2, a3, output wire [66:0] sum);
  assign sum = {3'd0, a0} + {3'd0, a1} + {3'd0, a2} + {3'd0, a3};
endmodule
module lec_csa4_gate (input wire [63:0] a0, a1, a2, a3, output wire [66:0] sum);
  wire [65:0] sx, sy;
  qsag_gl64_csa4 u (.a0(a0), .a1(a1), .a2(a2), .a3(a3), .sx(sx), .sy(sy));
  assign sum = {1'b0, sx} + {1'b0, sy};
endmodule
module lec_csa4_mut (input wire [63:0] a0, a1, a2, a3, output wire [66:0] sum);
  wire [66:0] g;
  lec_csa4_gate u (.*, .sum(g));
  assign sum = g ^ 67'd1;
endmodule

module lec_m4_lane_gold (input wire [65:0] sx, sy, input wire [63:0] bi, bj, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cbi=(bi>=P)?bi-P:bi, cbj=(bj>=P)?bj-P:bj;
  wire [67:0] sum = {2'd0, sx} + {2'd0, sy} + {4'd0, cbi} + {3'd0, cbj, 1'b0};
  qsag_gl64_final_seq #(.W(68)) u (.x(sum), .y(68'd0), .r(r));
endmodule
module lec_m4_lane_gate (input wire [65:0] sx, sy, input wire [63:0] bi, bj, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cbi=(bi>=P)?bi-P:bi, cbj=(bj>=P)?bj-P:bj;
  qsag_p2_m4_lane u (.sx(sx), .sy(sy), .bi(cbi), .bj(cbj), .r(r));
endmodule
module lec_m4_lane_mut (input wire [65:0] sx, sy, input wire [63:0] bi, bj, output wire [63:0] r);
  wire [63:0] g;
  lec_m4_lane_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_me_col_lane_gold (input wire [65:0] sx, sy, input wire [63:0] yb, rcb, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cyb=(yb>=P)?yb-P:yb, crc=(rcb>=P)?rcb-P:rcb;
  wire [67:0] sum = {2'd0, sx} + {2'd0, sy} + {4'd0, cyb} + {4'd0, crc};
  qsag_gl64_final_seq #(.W(68)) u (.x(sum), .y(68'd0), .r(r));
endmodule
module lec_me_col_lane_gate (input wire [65:0] sx, sy, input wire [63:0] yb, rcb, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cyb=(yb>=P)?yb-P:yb, crc=(rcb>=P)?rcb-P:rcb;
  qsag_p2_me_col_lane u (.sx(sx), .sy(sy), .yb(cyb), .rcb(crc), .r(r));
endmodule
module lec_me_col_lane_mut (input wire [65:0] sx, sy, input wire [63:0] yb, rcb, output wire [63:0] r);
  wire [63:0] g;
  lec_me_col_lane_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_sum4_csa_gold (input wire [65:0] sx0, sy0, sx1, sy1, output wire [63:0] r);
  wire [67:0] sum = {2'd0, sx0} + {2'd0, sy0} + {2'd0, sx1} + {2'd0, sy1};
  qsag_gl64_final_seq #(.W(68)) u (.x(sum), .y(68'd0), .r(r));
endmodule
module lec_sum4_csa_gate (input wire [65:0] sx0, sy0, sx1, sy1, output wire [63:0] r);
  qsag_gl64_sum4_csa u (.sx0(sx0), .sy0(sy0), .sx1(sx1), .sy1(sy1), .r(r));
endmodule
module lec_sum4_csa_mut (input wire [65:0] sx0, sy0, sx1, sy1, output wire [63:0] r);
  wire [63:0] g;
  lec_sum4_csa_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

// Parameterized wrapper across ALL 12 M_I lanes (each <= 4 64b inputs -> <2s Bitwuzla!)
module lec_mi_lane_gold #(parameter int LANE = 0) (
  input wire [63:0] x0, xl, s_tail, rcl,
  output wire [63:0] y
);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cx0=(x0>=P)?x0-P:x0, cxl=(xl>=P)?xl-P:xl, cst=(s_tail>=P)?s_tail-P:s_tail, crc=(rcl>=P)?rcl-P:rcl;
  if (LANE == 0) begin : g_l0
    wire [71:0] sum = {8'd0, cst} + {8'd0, crc} + {8'd0, cx0} + ({2'd0, P, 6'd0} - {2'd0, cx0, 6'd0});
    wire [63:0] r0;
    qsag_gl64_final_seq #(.W(72)) u (.x(sum), .y(72'd0), .r(r0));
    assign y = r0 ^ (cxl ^ cxl);
  end else begin : g_lp
    wire [79:0] sum = {16'd0, cst} + {16'd0, crc} + {16'd0, cx0} + ({16'd0, cxl} << (LANE - 1));
    qsag_gl64_final_seq #(.W(80)) u (.x(sum), .y(80'd0), .r(y));
  end
endmodule
module lec_mi_lane_gate #(parameter int LANE = 0) (
  input wire [63:0] x0, xl, s_tail, rcl,
  output wire [63:0] y
);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cx0=(x0>=P)?x0-P:x0, cxl=(xl>=P)?xl-P:xl, cst=(s_tail>=P)?s_tail-P:s_tail, crc=(rcl>=P)?rcl-P:rcl;
  if      (LANE == 0)  begin : g0  qsag_p2_mi_lane0  u (.x0(cx0), .s_tail(cst), .rcl(crc), .y(y)); wire u_ok = ^cxl; end
  else if (LANE == 1)  begin : g1  qsag_p2_mi_lane1  u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
  else if (LANE == 2)  begin : g2  qsag_p2_mi_lane2  u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
  else if (LANE == 3)  begin : g3  qsag_p2_mi_lane3  u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
  else if (LANE == 4)  begin : g4  qsag_p2_mi_lane4  u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
  else if (LANE == 5)  begin : g5  qsag_p2_mi_lane5  u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
  else if (LANE == 6)  begin : g6  qsag_p2_mi_lane6  u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
  else if (LANE == 7)  begin : g7  qsag_p2_mi_lane7  u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
  else if (LANE == 8)  begin : g8  qsag_p2_mi_lane8  u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
  else if (LANE == 9)  begin : g9  qsag_p2_mi_lane9  u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
  else if (LANE == 10) begin : g10 qsag_p2_mi_lane10 u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
  else                 begin : g11 qsag_p2_mi_lane11 u (.x0(cx0), .xl(cxl), .s_tail(cst), .rcl(crc), .y(y)); end
endmodule
module lec_mi_lane_mut #(parameter int LANE = 0) (
  input wire [63:0] x0, xl, s_tail, rcl,
  output wire [63:0] y
);
  wire [63:0] g;
  lec_mi_lane_gate #(.LANE(LANE)) u (.x0(x0), .xl(xl), .s_tail(s_tail), .rcl(rcl), .y(g));
  assign y = g ^ 64'd1;
endmodule

module lec_canopy_ff_gold (input wire [63:0] l, r, c, output wire [63:0] ff);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cl=(l>=P)?l-P:l, cr=(r>=P)?r-P:r, cc=(c>=P)?c-P:c;
  wire [67:0] sum = {4'd0, cl} + {3'd0, cr, 1'b0} + {2'd0, cc, 2'd0};
  qsag_gl64_final_seq #(.W(68)) u (.x(sum), .y(68'd0), .r(ff));
endmodule
module lec_canopy_ff_gate (input wire [63:0] l, r, c, output wire [63:0] ff);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cl=(l>=P)?l-P:l, cr=(r>=P)?r-P:r, cc=(c>=P)?c-P:c;
  qsag_p2_canopy_ff_lane u (.l(cl), .r(cr), .c(cc), .ff(ff));
endmodule
module lec_canopy_ff_mut (input wire [63:0] l, r, c, output wire [63:0] ff);
  wire [63:0] g;
  lec_canopy_ff_gate u (.*, .ff(g));
  assign ff = g ^ 64'd1;
endmodule

// ============================================================================
// 4. GF(2^128) Recursive Karatsuba CLMUL, 0x87 Reducer, & Cantor/Wiedemann T_7 Ring Isomorphism
// ============================================================================
module lec_clmul8_gold (input wire [7:0] a, b, output logic [14:0] p);
  always_comb begin
    p = '0;
    for (int i = 0; i < 8; i++) if (b[i]) p ^= {7'd0, a} << i;
  end
endmodule
module lec_clmul8_gate (input wire [7:0] a, b, output wire [14:0] p);
  qsag_clmul #(.N(8)) u (.a(a), .b(b), .p(p));
endmodule
module lec_clmul8_mut (input wire [7:0] a, b, output wire [14:0] p);
  wire [14:0] g;
  qsag_clmul #(.N(8)) u (.a(a), .b(b), .p(g));
  assign p = g ^ {14'd0, a[7] & b[7]};
endmodule

module lec_clmul_kara_gold #(parameter int H = 32) (
  input wire [2*H-2:0] p00, p01, p10, p11,
  output wire [4*H-2:0] p
);
  assign p = {{2*H{1'b0}}, p00} ^ {p11, {2*H{1'b0}}} ^ ({{2*H{1'b0}}, (p01 ^ p10)} << H);
endmodule
module lec_clmul_kara_gate #(parameter int H = 32) (
  input wire [2*H-2:0] p00, p01, p10, p11,
  output wire [4*H-2:0] p
);
  wire [2*H-2:0] mid = p00 ^ p01 ^ p10 ^ p11;
  assign p = {{2*H{1'b0}}, p00} ^ {p11, {2*H{1'b0}}} ^ ({{2*H{1'b0}}, (mid ^ p00 ^ p11)} << H);
endmodule
module lec_clmul_kara_mut #(parameter int H = 32) (
  input wire [2*H-2:0] p00, p01, p10, p11,
  output wire [4*H-2:0] p
);
  wire [4*H-2:0] g;
  lec_clmul_kara_gate #(.H(H)) u (.*, .p(g));
  assign p = g ^ {{(4*H-2){1'b0}}, p01[0]};
endmodule

module lec_gf_red_gold (input wire [254:0] c, output logic [127:0] r);
  logic [254:0] q;
  always_comb begin
    q = c;
    for (int i = 254; i >= 128; i--)
      if (q[i]) q ^= (255'h1_0000_0000_0000_0000_0000_0000_0000_0087 << (i - 128));
    r = q[127:0];
  end
endmodule
module lec_gf_red_gate (input wire [254:0] c, output wire [127:0] r);
  wire [126:0] h  = c[254:128];
  wire [133:0] f  = {7'b0, h} ^ {6'b0, h, 1'b0} ^ {5'b0, h, 2'b0} ^ {h, 7'b0};
  wire [5:0]   g  = f[133:128];
  wire [127:0] f2 = {122'b0, g} ^ {121'b0, g, 1'b0} ^ {120'b0, g, 2'b0} ^ {115'b0, g, 7'b0};
  assign r = c[127:0] ^ f[127:0] ^ f2;
endmodule
module lec_gf_red_mut (input wire [254:0] c, output wire [127:0] r);
  wire [127:0] g;
  lec_gf_red_gate u (.c(c), .r(g));
  assign r = g ^ {127'd0, c[254]};
endmodule

// 4D. Wiedemann `psiTower128` bijection + F_2-linearity + Cantor/Wiedemann ring homomorphism:
//   (1) Basis round-trip: B(F(1 << idx)) == (1 << idx) and F(B(1 << idx)) == (1 << idx) for all idx in 0..127
module lec_tower_basis_fwd_gold (input wire [6:0] idx, output wire [127:0] y);
  assign y = 128'd1 << idx;
endmodule
module lec_tower_basis_fwd_gate (input wire [6:0] idx, output wire [127:0] y);
  wire [127:0] p;
  qsag_tower128_to_poly u_f (.x(128'd1 << idx), .y(p));
  qsag_poly_to_tower128 u_b (.x(p), .y(y));
endmodule
module lec_tower_basis_fwd_mut (input wire [6:0] idx, output wire [127:0] y);
  wire [127:0] g;
  lec_tower_basis_fwd_gate u (.idx(idx), .y(g));
  assign y = g ^ {127'd0, idx == 7'd127};
endmodule

module lec_tower_basis_bwd_gold (input wire [6:0] idx, output wire [127:0] y);
  assign y = 128'd1 << idx;
endmodule
module lec_tower_basis_bwd_gate (input wire [6:0] idx, output wire [127:0] y);
  wire [127:0] t;
  qsag_poly_to_tower128 u_b (.x(128'd1 << idx), .y(t));
  qsag_tower128_to_poly u_f (.x(t), .y(y));
endmodule
module lec_tower_basis_bwd_mut (input wire [6:0] idx, output wire [127:0] y);
  wire [127:0] g;
  lec_tower_basis_bwd_gate u (.idx(idx), .y(g));
  assign y = g ^ {127'd0, idx == 7'd0};
endmodule

//   (2) F_2-linearity over ALL x in {0,1}^128 and basis flips k in 0..127:
//       F(0) == 0 && F(x ^ (1<<k)) == F(x) ^ F(1<<k)  (and likewise for B)
module lec_tower_lin_fwd_gold (input wire [127:0] x, input wire [6:0] k, output wire [128:0] y);
  wire [127:0] fx, fk;
  qsag_tower128_to_poly ux (.x(x),           .y(fx));
  qsag_tower128_to_poly uk (.x(128'd1 << k), .y(fk));
  assign y = {1'b1, fx ^ fk};
endmodule
module lec_tower_lin_fwd_gate (input wire [127:0] x, input wire [6:0] k, output wire [128:0] y);
  wire [127:0] fxk, f0;
  qsag_tower128_to_poly uxk (.x(x ^ (128'd1 << k)), .y(fxk));
  qsag_tower128_to_poly u0  (.x(128'd0),            .y(f0));
  assign y = {f0 == 128'd0, fxk};
endmodule
module lec_tower_lin_fwd_mut (input wire [127:0] x, input wire [6:0] k, output wire [128:0] y);
  wire [128:0] g;
  lec_tower_lin_fwd_gate u (.x(x), .k(k), .y(g));
  assign y = g ^ 129'd1;
endmodule

module lec_tower_lin_bwd_gold (input wire [127:0] x, input wire [6:0] k, output wire [128:0] y);
  wire [127:0] bx, bk;
  qsag_poly_to_tower128 ux (.x(x),           .y(bx));
  qsag_poly_to_tower128 uk (.x(128'd1 << k), .y(bk));
  assign y = {1'b1, bx ^ bk};
endmodule
module lec_tower_lin_bwd_gate (input wire [127:0] x, input wire [6:0] k, output wire [128:0] y);
  wire [127:0] bxk, b0;
  qsag_poly_to_tower128 uxk (.x(x ^ (128'd1 << k)), .y(bxk));
  qsag_poly_to_tower128 u0  (.x(128'd0),            .y(b0));
  assign y = {b0 == 128'd0, bxk};
endmodule
module lec_tower_lin_bwd_mut (input wire [127:0] x, input wire [6:0] k, output wire [128:0] y);
  wire [128:0] g;
  lec_tower_lin_bwd_gate u (.x(x), .k(k), .y(g));
  assign y = g ^ 129'd1;
endmodule

//   (3) Cantor/Wiedemann T_7 Generator Quadratic Tower Identities:
//       * F(1) == 1
//       * For all k in 0..6 (g_k = F(1 << (1 << k))): g_0^2 ^ g_0 ^ 1 == 0 and g_k^2 ^ (g_{k-1} * g_k) ^ 1 == 0
//       (Full 256-bit multiplicative homomorphism across all 2^256 pairs is discharged by lec/check_anf.py!)
module lec_tower_gen_gold (input wire [2:0] k_sel, output wire ok);
  assign ok = (k_sel == k_sel);
endmodule
module lec_tower_gen_gate (input wire [2:0] k_sel, output wire ok);
  wire [127:0] f1;
  qsag_tower128_to_poly u_f1 (.x(128'd1), .y(f1));
  wire [127:0] gk [7];
  wire [6:0]   lvl_ok;
  for (genvar k = 0; k < 7; k++) begin : g_lvl
    qsag_tower128_to_poly u_gk (.x(128'd1 << (1 << k)), .y(gk[k]));
    wire [127:0] sq, lin;
    qsag_gf128_mul u_sq (.a(gk[k]), .b(gk[k]), .r(sq));
    if (k == 0) begin : g_k0
      assign lin = gk[0];
    end else begin : g_kp
      qsag_gf128_mul u_lin (.a(gk[k - 1]), .b(gk[k]), .r(lin));
    end
    assign lvl_ok[k] = (sq ^ lin ^ 128'd1) == 128'd0;
  end
  wire [2:0] idx = (k_sel < 3'd7) ? k_sel : 3'd6;
  assign ok = (f1 == 128'd1) && lvl_ok[idx];
endmodule
module lec_tower_gen_mut (input wire [2:0] k_sel, output wire ok);
  wire g;
  lec_tower_gen_gate u (.k_sel(k_sel), .ok(g));
  assign ok = g ^ (k_sel == 3'd3);
endmodule
`default_nettype wire
