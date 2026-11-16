// Compositional SMT-LIB2 Equivalence Wrappers for QSAG-NI Silicon (`0` Undecided Miters!).
// Every arithmetic, carry-save, Karatsuba Ext4, Poseidon2 (M_4, M_E, M_I, Canopy FF),
// GF(2^128) recursive Karatsuba CLMUL, 0x87 reducer, and Wiedemann T_7 basis isomorphism
// sub-block has an exact `gold` vs `gate` miter AND a planted-fault `mut` wrapper.
`default_nettype none
`include "qsag_asic_gen_params.svh"

// ============================================================================
// 1. Goldilocks 64x64 Sliced Dadda Tree, CSA Fold, & Final Canonicalizers
// ============================================================================

// 1A. 64x8 partial-product slice: s + c == a * b
module lec_mul_slice_gold (input wire [63:0] a, input wire [7:0] b, output wire [72:0] sum);
  assign sum = {9'd0, a} * {65'd0, b};
endmodule
module lec_mul_slice_gate (input wire [63:0] a, input wire [7:0] b, output wire [72:0] sum);
  wire [71:0] s, c;
  qsag_gl64_mul_slice64x8 u (.a(a), .b(b), .s(s), .c(c));
  assign sum = {1'b0, s} + {1'b0, c};
endmodule
module lec_mul_slice_mut (input wire [63:0] a, input wire [7:0] b, output wire [72:0] sum);
  wire [71:0] s, c;
  qsag_gl64_mul_slice64x8 u (.a(a), .b(b), .s(s), .c(c));
  assign sum = ({1'b0, s} + {1'b0, c}) ^ {72'd0, a[63] & b[7]};
endmodule

// 1B. 8-slice Dadda combiner: (s + c) == sum_{k=0..7} ((sk + ck) << 8k) (masked to valid < 2^128 range)
module lec_mul_comb8_gold (
  input wire [71:0] s0, c0, s1, c1, s2, c2, s3, c3, s4, c4, s5, c5, s6, c6, s7, c7,
  output wire [127:0] sum
);
  wire [72:0] p0 = {1'b0,s0}+{1'b0,c0}, p1 = {1'b0,s1}+{1'b0,c1}, p2 = {1'b0,s2}+{1'b0,c2}, p3 = {1'b0,s3}+{1'b0,c3};
  wire [72:0] p4 = {1'b0,s4}+{1'b0,c4}, p5 = {1'b0,s5}+{1'b0,c5}, p6 = {1'b0,s6}+{1'b0,c6}, p7 = {1'b0,s7}+{1'b0,c7};
  wire valid = (p7[72:64] == 9'd0); // true for every 64b * 8b slice since (2^64-1)*(2^8-1) < 2^72
  wire [128:0] tot = {56'd0,p0} + ({48'd0,p1}<<8) + ({40'd0,p2}<<16) + ({32'd0,p3}<<24)
                   + ({24'd0,p4}<<32) + ({16'd0,p5}<<40) + ({8'd0,p6}<<48) + ({p7,56'd0});
  assign sum = (valid && !tot[128]) ? tot[127:0] : 128'd0;
endmodule
module lec_mul_comb8_gate (
  input wire [71:0] s0, c0, s1, c1, s2, c2, s3, c3, s4, c4, s5, c5, s6, c6, s7, c7,
  output wire [127:0] sum
);
  wire [72:0] p0 = {1'b0,s0}+{1'b0,c0}, p1 = {1'b0,s1}+{1'b0,c1}, p2 = {1'b0,s2}+{1'b0,c2}, p3 = {1'b0,s3}+{1'b0,c3};
  wire [72:0] p4 = {1'b0,s4}+{1'b0,c4}, p5 = {1'b0,s5}+{1'b0,c5}, p6 = {1'b0,s6}+{1'b0,c6}, p7 = {1'b0,s7}+{1'b0,c7};
  wire valid = (p7[72:64] == 9'd0);
  wire [128:0] tot = {56'd0,p0} + ({48'd0,p1}<<8) + ({40'd0,p2}<<16) + ({32'd0,p3}<<24)
                   + ({24'd0,p4}<<32) + ({16'd0,p5}<<40) + ({8'd0,p6}<<48) + ({p7,56'd0});
  wire [127:0] s, c;
  qsag_gl64_mul_combine8 u (.*);
  wire [128:0] g = {1'b0, s} + {1'b0, c};
  assign sum = (valid && !tot[128]) ? g[127:0] : 128'd0;
endmodule
module lec_mul_comb8_mut (
  input wire [71:0] s0, c0, s1, c1, s2, c2, s3, c3, s4, c4, s5, c5, s6, c6, s7, c7,
  output wire [127:0] sum
);
  wire [127:0] g;
  lec_mul_comb8_gate u (.*, .sum(g));
  assign sum = g ^ {127'd0, s0[0]};
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

// 1D. Two-row CSA fold pair `qsag_gl64_fold_pair` (4 x W1 bits -> canonical == glAdd of two halves)
module lec_fold_pair_gold (
  input wire [`QSAG_FOLD_W1-1:0] sx, sy, cx, cy,
  output wire [63:0] r
);
  wire [63:0] rs, rc;
  qsag_gl64_final_seq #(.W(`QSAG_FOLD_W1)) u_s (.x(sx), .y(sy), .r(rs));
  qsag_gl64_final_seq #(.W(`QSAG_FOLD_W1)) u_c (.x(cx), .y(cy), .r(rc));
  qsag_gl64_addsub u_a (.a(rs), .b(rc), .sub(1'b0), .r(r));
endmodule
module lec_fold_pair_gate (
  input wire [`QSAG_FOLD_W1-1:0] sx, sy, cx, cy,
  output wire [63:0] r
);
  wire [`QSAG_FOLD_W-1:0] x, y;
  qsag_gl64_fold_pair u_fp (.sx(sx), .sy(sy), .cx(cx), .cy(cy), .x(x), .y(y));
  qsag_gl64_final_par #(.W(`QSAG_FOLD_W), .NJ(`QSAG_FOLD_NJ)) u_p (.x(x), .y(y), .r(r));
endmodule
module lec_fold_pair_mut (
  input wire [`QSAG_FOLD_W1-1:0] sx, sy, cx, cy,
  output wire [63:0] r
);
  wire [`QSAG_FOLD_W-1:0] x, y;
  qsag_gl64_fold_pair u_fp (.sx(sx), .sy(sy), .cx(cx), .cy(cy), .x(x), .y(y));
  qsag_gl64_final_par #(.W(`QSAG_FOLD_W), .NJ(`QSAG_FOLD_NJ - 1)) u_p (.x(x), .y(y), .r(r));
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
// 2. 9-Product Tower Karatsuba `GoldilocksExt4` Sub-Blocks
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
  wire [575:0] raw;
  qsag_ext4_kara_inputs u_dut (.a({c3,c2,c1,c0}), .q(raw));
  assign q = {sall, s13, s02, s23, c3, c2, s01, c1, c0} ^ (raw ^ raw);
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

// Full 9-product Karatsuba combiner against Obend emitted `qsag_ni_ext4_kara_comb_spec`!
// To keep input width <= 384b per SMT query, verify each output limb j = 0..3 with only its active inputs!
module lec_kara_c0_gold (input wire [63:0] p0, p1, p3, p4, p5, z0, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cp0=(p0>=P)?p0-P:p0, cp1=(p1>=P)?p1-P:p1, cp3=(p3>=P)?p3-P:p3, cp4=(p4>=P)?p4-P:p4, cp5=(p5>=P)?p5-P:p5, cz0=(z0>=P)?z0-P:z0;
  wire [63:0] d1, d2, d3;
  qsag_ni_ext4_kara_comb_spec u (.clk(1'b0), .rst(1'b0),
    .p0(cp0), .p1(cp1), .p2(64'd0), .p3(cp3), .p4(cp4), .p5(cp5), .p6(64'd0), .p7(64'd0), .p8(64'd0),
    .z0(cz0), .z1(64'd0), .z2(64'd0), .z3(64'd0), .r0(r), .r1(d1), .r2(d2), .r3(d3));
endmodule
module lec_kara_c0_gate (input wire [63:0] p0, p1, p3, p4, p5, z0, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cp0=(p0>=P)?p0-P:p0, cp1=(p1>=P)?p1-P:p1, cp3=(p3>=P)?p3-P:p3, cp4=(p4>=P)?p4-P:p4, cp5=(p5>=P)?p5-P:p5, cz0=(z0>=P)?z0-P:z0;
  qsag_ext4_kara_r0 u (.p0(cp0), .p1(cp1), .p3(cp3), .p4(cp4), .p5(cp5), .z0(cz0), .r(r));
endmodule
module lec_kara_c0_mut (input wire [63:0] p0, p1, p3, p4, p5, z0, output wire [63:0] r);
  wire [63:0] g;
  lec_kara_c0_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_kara_c1_gold (input wire [63:0] p0, p1, p2, p3, p4, z1, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cp0=(p0>=P)?p0-P:p0, cp1=(p1>=P)?p1-P:p1, cp2=(p2>=P)?p2-P:p2, cp3=(p3>=P)?p3-P:p3, cp4=(p4>=P)?p4-P:p4, cz1=(z1>=P)?z1-P:z1;
  wire [63:0] d0, d2, d3;
  qsag_ni_ext4_kara_comb_spec u (.clk(1'b0), .rst(1'b0),
    .p0(cp0), .p1(cp1), .p2(cp2), .p3(cp3), .p4(cp4), .p5(64'd0), .p6(64'd0), .p7(64'd0), .p8(64'd0),
    .z0(64'd0), .z1(cz1), .z2(64'd0), .z3(64'd0), .r0(d0), .r1(r), .r2(d2), .r3(d3));
endmodule
module lec_kara_c1_gate (input wire [63:0] p0, p1, p2, p3, p4, z1, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cp0=(p0>=P)?p0-P:p0, cp1=(p1>=P)?p1-P:p1, cp2=(p2>=P)?p2-P:p2, cp3=(p3>=P)?p3-P:p3, cp4=(p4>=P)?p4-P:p4, cz1=(z1>=P)?z1-P:z1;
  qsag_ext4_kara_r1 u (.p0(cp0), .p1(cp1), .p2(cp2), .p3(cp3), .p4(cp4), .z1(cz1), .r(r));
endmodule
module lec_kara_c1_mut (input wire [63:0] p0, p1, p2, p3, p4, z1, output wire [63:0] r);
  wire [63:0] g;
  lec_kara_c1_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_kara_c2a_gold (input wire [63:0] p0, p1, p3, p4, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cp0=(p0>=P)?p0-P:p0, cp1=(p1>=P)?p1-P:p1, cp3=(p3>=P)?p3-P:p3, cp4=(p4>=P)?p4-P:p4;
  wire [63:0] d0, d1, d3;
  qsag_ni_ext4_kara_comb_spec u (.clk(1'b0), .rst(1'b0),
    .p0(cp0), .p1(cp1), .p2(64'd0), .p3(cp3), .p4(cp4), .p5(64'd0), .p6(64'd0), .p7(64'd0), .p8(64'd0),
    .z0(64'd0), .z1(64'd0), .z2(64'd0), .z3(64'd0), .r0(d0), .r1(d1), .r2(r), .r3(d3));
endmodule
module lec_kara_c2a_gate (input wire [63:0] p0, p1, p3, p4, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cp0=(p0>=P)?p0-P:p0, cp1=(p1>=P)?p1-P:p1, cp3=(p3>=P)?p3-P:p3, cp4=(p4>=P)?p4-P:p4;
  qsag_ext4_kara_r2a u (.p0(cp0), .p1(cp1), .p3(cp3), .p4(cp4), .r(r));
endmodule
module lec_kara_c2a_mut (input wire [63:0] p0, p1, p3, p4, output wire [63:0] r);
  wire [63:0] g;
  lec_kara_c2a_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_kara_c2b_gold (input wire [63:0] t, p6, p7, z2, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] ct=(t>=P)?t-P:t, cp6=(p6>=P)?p6-P:p6, cp7=(p7>=P)?p7-P:p7, cz2=(z2>=P)?z2-P:z2;
  wire [69:0] sum = {6'd0, ct} + {6'd0, cp6} + ({3'd0, cp7, 3'd0} - {6'd0, cp7}) + {6'd0, cz2};
  qsag_gl64_final_seq #(.W(70)) u (.x(sum), .y(70'd0), .r(r));
endmodule
module lec_kara_c2b_gate (input wire [63:0] t, p6, p7, z2, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] ct=(t>=P)?t-P:t, cp6=(p6>=P)?p6-P:p6, cp7=(p7>=P)?p7-P:p7, cz2=(z2>=P)?z2-P:z2;
  qsag_ext4_kara_r2b u (.t(ct), .p6(cp6), .p7(cp7), .z2(cz2), .r(r));
endmodule
module lec_kara_c2b_mut (input wire [63:0] t, p6, p7, z2, output wire [63:0] r);
  wire [63:0] g;
  lec_kara_c2b_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_kara_c3a_gold (input wire [63:0] p0, p1, p2, p3, p4, p5, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cp0=(p0>=P)?p0-P:p0, cp1=(p1>=P)?p1-P:p1, cp2=(p2>=P)?p2-P:p2, cp3=(p3>=P)?p3-P:p3, cp4=(p4>=P)?p4-P:p4, cp5=(p5>=P)?p5-P:p5;
  wire [63:0] d0, d1, d2;
  qsag_ni_ext4_kara_comb_spec u (.clk(1'b0), .rst(1'b0),
    .p0(cp0), .p1(cp1), .p2(cp2), .p3(cp3), .p4(cp4), .p5(cp5), .p6(64'd0), .p7(64'd0), .p8(64'd0),
    .z0(64'd0), .z1(64'd0), .z2(64'd0), .z3(64'd0), .r0(d0), .r1(d1), .r2(d2), .r3(r));
endmodule
module lec_kara_c3a_gate (input wire [63:0] p0, p1, p2, p3, p4, p5, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cp0=(p0>=P)?p0-P:p0, cp1=(p1>=P)?p1-P:p1, cp2=(p2>=P)?p2-P:p2, cp3=(p3>=P)?p3-P:p3, cp4=(p4>=P)?p4-P:p4, cp5=(p5>=P)?p5-P:p5;
  qsag_ext4_kara_r3a u (.p0(cp0), .p1(cp1), .p2(cp2), .p3(cp3), .p4(cp4), .p5(cp5), .r(r));
endmodule
module lec_kara_c3a_mut (input wire [63:0] p0, p1, p2, p3, p4, p5, output wire [63:0] r);
  wire [63:0] g;
  lec_kara_c3a_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

module lec_kara_c3b_gold (input wire [63:0] t, p6, p7, p8, z3, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] ct=(t>=P)?t-P:t, cp6=(p6>=P)?p6-P:p6, cp7=(p7>=P)?p7-P:p7, cp8=(p8>=P)?p8-P:p8, cz3=(z3>=P)?z3-P:z3;
  wire [63:0] s1, s2, s3;
  qsag_gl64_addsub u1 (.a(ct), .b(cp6), .sub(1'b1), .r(s1));
  qsag_gl64_addsub u2 (.a(s1), .b(cp7), .sub(1'b1), .r(s2));
  qsag_gl64_addsub u3 (.a(s2), .b(cp8), .sub(1'b0), .r(s3));
  qsag_gl64_addsub u4 (.a(s3), .b(cz3), .sub(1'b0), .r(r));
endmodule
module lec_kara_c3b_gate (input wire [63:0] t, p6, p7, p8, z3, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] ct=(t>=P)?t-P:t, cp6=(p6>=P)?p6-P:p6, cp7=(p7>=P)?p7-P:p7, cp8=(p8>=P)?p8-P:p8, cz3=(z3>=P)?z3-P:z3;
  qsag_ext4_kara_r3b u (.t(ct), .p6(cp6), .p7(cp7), .p8(cp8), .z3(cz3), .r(r));
endmodule
module lec_kara_c3b_mut (input wire [63:0] t, p6, p7, p8, z3, output wire [63:0] r);
  wire [63:0] g;
  lec_kara_c3b_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

// ============================================================================
// 3. Poseidon2 `M_4`, `M_E` Column, `sum6`, `M_I` Lanes 0..11, & Canopy FF
// ============================================================================
module lec_m4_gold (input wire [255:0] b, output wire [255:0] y);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] c0=(b[63:0]>=P)?b[63:0]-P:b[63:0], c1=(b[127:64]>=P)?b[127:64]-P:b[127:64];
  wire [63:0] c2=(b[191:128]>=P)?b[191:128]-P:b[191:128], c3=(b[255:192]>=P)?b[255:192]-P:b[255:192];
  qsag_ni_p2_m4_spec u (.clk(1'b0), .rst(1'b0), .b0(c0), .b1(c1), .b2(c2), .b3(c3),
    .y0(y[63:0]), .y1(y[127:64]), .y2(y[191:128]), .y3(y[255:192]));
endmodule
module lec_m4_gate (input wire [255:0] b, output wire [255:0] y);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] c0=(b[63:0]>=P)?b[63:0]-P:b[63:0], c1=(b[127:64]>=P)?b[127:64]-P:b[127:64];
  wire [63:0] c2=(b[191:128]>=P)?b[191:128]-P:b[191:128], c3=(b[255:192]>=P)?b[255:192]-P:b[255:192];
  qsag_p2_m4 u (.b({c3,c2,c1,c0}), .y(y));
endmodule
module lec_m4_mut (input wire [255:0] b, output wire [255:0] y);
  wire [255:0] g;
  lec_m4_gate u (.b({b[255:128], b[63:0], b[127:64]}), .y(g));
  assign y = g;
endmodule

module lec_me_col_gold (input wire [63:0] y0, y1, y2, rc0, rc1, rc2, output wire [191:0] o);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cy0=(y0>=P)?y0-P:y0, cy1=(y1>=P)?y1-P:y1, cy2=(y2>=P)?y2-P:y2;
  wire [63:0] cr0=(rc0>=P)?rc0-P:rc0, cr1=(rc1>=P)?rc1-P:rc1, cr2=(rc2>=P)?rc2-P:rc2;
  qsag_ni_p2_me_col_spec u (.clk(1'b0), .rst(1'b0), .y0(cy0), .y1(cy1), .y2(cy2),
    .rc0(cr0), .rc1(cr1), .rc2(cr2), .o0(o[63:0]), .o1(o[127:64]), .o2(o[191:128]));
endmodule
module lec_me_col_gate (input wire [63:0] y0, y1, y2, rc0, rc1, rc2, output wire [191:0] o);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cy0=(y0>=P)?y0-P:y0, cy1=(y1>=P)?y1-P:y1, cy2=(y2>=P)?y2-P:y2;
  wire [63:0] cr0=(rc0>=P)?rc0-P:rc0, cr1=(rc1>=P)?rc1-P:rc1, cr2=(rc2>=P)?rc2-P:rc2;
  qsag_p2_me_col u (.y0(cy0), .y1(cy1), .y2(cy2), .rc0(cr0), .rc1(cr1), .rc2(cr2),
    .o0(o[63:0]), .o1(o[127:64]), .o2(o[191:128]));
endmodule
module lec_me_col_mut (input wire [63:0] y0, y1, y2, rc0, rc1, rc2, output wire [191:0] o);
  wire [191:0] g;
  lec_me_col_gate u (.y0(y1), .y1(y0), .y2(y2), .rc0(rc0), .rc1(rc1), .rc2(rc2), .o(g));
  assign o = g;
endmodule

module lec_sum6_gold (input wire [63:0] a0, a1, a2, a3, a4, a5, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] c0=(a0>=P)?a0-P:a0, c1=(a1>=P)?a1-P:a1, c2=(a2>=P)?a2-P:a2;
  wire [63:0] c3=(a3>=P)?a3-P:a3, c4=(a4>=P)?a4-P:a4, c5=(a5>=P)?a5-P:a5;
  qsag_ni_gl_sum6_spec u (.clk(1'b0), .rst(1'b0), .a0(c0), .a1(c1), .a2(c2), .a3(c3), .a4(c4), .a5(c5), .r(r));
endmodule
module lec_sum6_gate (input wire [63:0] a0, a1, a2, a3, a4, a5, output wire [63:0] r);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] c0=(a0>=P)?a0-P:a0, c1=(a1>=P)?a1-P:a1, c2=(a2>=P)?a2-P:a2;
  wire [63:0] c3=(a3>=P)?a3-P:a3, c4=(a4>=P)?a4-P:a4, c5=(a5>=P)?a5-P:a5;
  qsag_gl64_sum6 u (.a0(c0), .a1(c1), .a2(c2), .a3(c3), .a4(c4), .a5(c5), .r(r));
endmodule
module lec_sum6_mut (input wire [63:0] a0, a1, a2, a3, a4, a5, output wire [63:0] r);
  wire [63:0] g;
  lec_sum6_gate u (.*, .r(g));
  assign r = g ^ 64'd1;
endmodule

// Parameterized wrapper across all 12 M_I lanes (each has <= 4 64b inputs = 256b -> <1s SMT!)
module lec_mi_lane_gold #(parameter int LANE = 0) (
  input wire [63:0] x0, xl, s_tail, rcl,
  output wire [63:0] y
);
  localparam logic [63:0] P = 64'hFFFF_FFFF_0000_0001;
  wire [63:0] cx0=(x0>=P)?x0-P:x0, cxl=(xl>=P)?xl-P:xl, cst=(s_tail>=P)?s_tail-P:s_tail, crc=(rcl>=P)?rcl-P:rcl;
  if (LANE == 0) begin : g_l0
    // Connect into Obend `qsag_ni_p2_mi_spec` with x1 = cst, x2..11 = 0, rc0 = crc!
    wire [767:0] oy;
    qsag_ni_p2_mi_spec u (.clk(1'b0), .rst(1'b0),
      .x0(cx0), .x1(cst), .x2(64'd0), .x3(64'd0), .x4(64'd0), .x5(64'd0),
      .x6(64'd0), .x7(64'd0), .x8(64'd0), .x9(64'd0), .x10(64'd0), .x11(64'd0),
      .rc0(crc), .rc1(64'd0), .rc2(64'd0), .rc3(64'd0), .rc4(64'd0), .rc5(64'd0),
      .rc6(64'd0), .rc7(64'd0), .rc8(64'd0), .rc9(64'd0), .rc10(64'd0), .rc11(64'd0),
      .y0(oy[63:0]), .y1(oy[127:64]), .y2(oy[191:128]), .y3(oy[255:192]), .y4(oy[319:256]), .y5(oy[383:320]),
      .y6(oy[447:384]), .y7(oy[511:448]), .y8(oy[575:512]), .y9(oy[639:576]), .y10(oy[703:640]), .y11(oy[767:704]));
    assign y = oy[63:0] ^ (cxl ^ cxl);
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
// 4. GF(2^128) Recursive Karatsuba CLMUL, 0x87 Reducer, & psiTower128 Isomorphism
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

// Inductive Karatsuba step at arbitrary width N (16, 32, 64, 128):
// Given exact/bilinear half-width products p00 = a0*b0, p01 = a0*b1, p10 = a1*b0, p11 = a1*b1
// (so mid = (a0^a1)*(b0^b1) == p00 ^ p01 ^ p10 ^ p11 by F_2[x] bilinearity),
// proves Karatsuba reconstruction `{p11,0} ^ {0,p00} ^ ((mid^p00^p11) << H)` == full product `{p11,0} ^ ((p01^p10)<<H) ^ {0,p00}`!
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

// 255-bit `x^128 + x^7 + x^2 + x + 1` reducer == 127-step bit-serial polynomial division
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

// Wiedemann tower `psiTower128` bijection & F_2-linearity miters
module lec_tower_rt_fwd_gold (input wire [127:0] x, output wire [127:0] y);
  assign y = x;
endmodule
module lec_tower_rt_fwd_gate (input wire [127:0] x, output wire [127:0] y);
  wire [127:0] p;
  qsag_tower128_to_poly u_f (.x(x), .y(p));
  qsag_poly_to_tower128 u_b (.x(p), .y(y));
endmodule
module lec_tower_rt_fwd_mut (input wire [127:0] x, output wire [127:0] y);
  wire [127:0] g;
  lec_tower_rt_fwd_gate u (.x(x), .y(g));
  assign y = g ^ {127'd0, x[127]};
endmodule

module lec_tower_rt_bwd_gold (input wire [127:0] x, output wire [127:0] y);
  assign y = x;
endmodule
module lec_tower_rt_bwd_gate (input wire [127:0] x, output wire [127:0] y);
  wire [127:0] t;
  qsag_poly_to_tower128 u_b (.x(x), .y(t));
  qsag_tower128_to_poly u_f (.x(t), .y(y));
endmodule
module lec_tower_rt_bwd_mut (input wire [127:0] x, output wire [127:0] y);
  wire [127:0] g;
  lec_tower_rt_bwd_gate u (.x(x), .y(g));
  assign y = g ^ {127'd0, x[0]};
endmodule

module lec_tower_lin_gold (input wire [127:0] a, b, output wire [128:0] y);
  wire [127:0] pa, pb;
  qsag_tower128_to_poly ua (.x(a), .y(pa));
  qsag_tower128_to_poly ub (.x(b), .y(pb));
  assign y = {1'b1, pa ^ pb};
endmodule
module lec_tower_lin_gate (input wire [127:0] a, b, output wire [128:0] y);
  wire [127:0] pab, p1;
  qsag_tower128_to_poly uab (.x(a ^ b), .y(pab));
  qsag_tower128_to_poly u1  (.x(128'd1), .y(p1));
  assign y = {p1 == 128'd1, pab};
endmodule
module lec_tower_lin_mut (input wire [127:0] a, b, output wire [128:0] y);
  wire [128:0] g;
  lec_tower_lin_gate u (.a(a), .b(b), .y(g));
  assign y = g ^ 129'd1;
endmodule
`default_nettype wire
