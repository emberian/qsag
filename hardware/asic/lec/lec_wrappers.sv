// Miter sides for lec/run_lec.sh. "gold" sides are built from the SystemVerilog that Obend's
// emitModuleSV printed for the RtlModules in obend/QsagNi.lean (obend/emitted/*.sv); "gate" sides
// are the QSAG-NI carry-save RTL. Every pair has identical ports.
`default_nettype none
`include "qsag_asic_gen_params.svh"

// ---- 128-bit -> canonical reducer
module lec_reduce_gold (input wire [127:0] v, output wire [63:0] r);
  qsag_ni_gl_reduce128_spec u (.clk(1'b0), .rst(1'b0), .lo(v[63:0]), .hi(v[127:64]), .r(r));
endmodule
module lec_reduce_gate (input wire [127:0] v, output wire [63:0] r);
  qsag_gl64_reduce128_csa u (.v(v), .r(r));
endmodule
module lec_reduce_ref (input wire [127:0] v, output wire [63:0] r);
  qsag_gl64_reduce128_ref u (.v(v), .r(r));
endmodule
// planted fault: one result bit wrong for exactly one input
module lec_reduce_mut (input wire [127:0] v, output wire [63:0] r);
  wire [63:0] g;
  qsag_gl64_reduce128_csa u (.v(v), .r(g));
  assign r = g ^ {46'b0, v == 128'h0123_4567_89AB_CDEF_FEDC_BA98_7654_3210, 17'b0};
endmodule

// ---- the multiplier's carry-save reduction: fold + parallel final adder on arbitrary rows (s, c)
module lec_fold_gold (input wire [127:0] s, input wire [127:0] c, output wire [63:0] r);
  wire [63:0] rs, rc;
  qsag_ni_gl_reduce128_spec u_s (.clk(1'b0), .rst(1'b0), .lo(s[63:0]), .hi(s[127:64]), .r(rs));
  qsag_ni_gl_reduce128_spec u_c (.clk(1'b0), .rst(1'b0), .lo(c[63:0]), .hi(c[127:64]), .r(rc));
  qsag_gl64_addsub u_a (.a(rs), .b(rc), .sub(1'b0), .r(r));
endmodule
module lec_fold_gate (input wire [127:0] s, input wire [127:0] c, output wire [63:0] r);
  wire [`QSAG_FOLD_W-1:0] x, y;
  qsag_gl64_fold u_f (.s(s), .c(c), .x(x), .y(y));
  qsag_gl64_final_par #(.W(`QSAG_FOLD_W), .NJ(`QSAG_FOLD_NJ)) u_p (.x(x), .y(y), .r(r));
endmodule
module lec_fold_mut (input wire [127:0] s, input wire [127:0] c, output wire [63:0] r);
  wire [`QSAG_FOLD_W-1:0] x, y;
  qsag_gl64_fold u_f (.s(s), .c(c), .x(x), .y(y));
  // one candidate short: wrong only when the quotient reaches NJ - 1
  qsag_gl64_final_par #(.W(`QSAG_FOLD_W), .NJ(`QSAG_FOLD_NJ - 1)) u_p (.x(x), .y(y), .r(r));
endmodule

// ---- final adders: parallel compound form against the chained form
module lec_final_gold (input wire [`QSAG_FOLD_W-1:0] x, input wire [`QSAG_FOLD_W-1:0] y, output wire [63:0] r);
  qsag_gl64_final_seq #(.W(`QSAG_FOLD_W)) u (.x(x), .y(y), .r(r));
endmodule
module lec_final_gate (input wire [`QSAG_FOLD_W-1:0] x, input wire [`QSAG_FOLD_W-1:0] y, output wire [63:0] r);
  // valid for x + y < NJ * p; outside that range the miter is masked to 0
  wire [`QSAG_FOLD_W:0] t = {1'b0, x} + {1'b0, y};
  wire ok = t < (`QSAG_FOLD_W+1)'(`QSAG_FOLD_NJ) * (`QSAG_FOLD_W+1)'(64'hFFFF_FFFF_0000_0001);
  wire [63:0] g, h;
  qsag_gl64_final_par #(.W(`QSAG_FOLD_W), .NJ(`QSAG_FOLD_NJ)) u (.x(x), .y(y), .r(g));
  qsag_gl64_final_seq #(.W(`QSAG_FOLD_W)) v (.x(x), .y(y), .r(h));
  assign r = ok ? g : h;
endmodule

// ---- Poseidon2 linear layers (with round-constant addition), one output lane per miter
module lec_me_gold #(parameter int LANE = 0) (input wire [767:0] x, input wire [767:0] rc, output wire [63:0] r);
  wire [767:0] y;
  qsag_ni_p2_me_spec u (.clk(1'b0), .rst(1'b0),
    .x0(x[63:0]), .x1(x[127:64]), .x2(x[191:128]), .x3(x[255:192]), .x4(x[319:256]), .x5(x[383:320]),
    .x6(x[447:384]), .x7(x[511:448]), .x8(x[575:512]), .x9(x[639:576]), .x10(x[703:640]), .x11(x[767:704]),
    .rc0(rc[63:0]), .rc1(rc[127:64]), .rc2(rc[191:128]), .rc3(rc[255:192]), .rc4(rc[319:256]), .rc5(rc[383:320]),
    .rc6(rc[447:384]), .rc7(rc[511:448]), .rc8(rc[575:512]), .rc9(rc[639:576]), .rc10(rc[703:640]), .rc11(rc[767:704]),
    .y0(y[63:0]), .y1(y[127:64]), .y2(y[191:128]), .y3(y[255:192]), .y4(y[319:256]), .y5(y[383:320]),
    .y6(y[447:384]), .y7(y[511:448]), .y8(y[575:512]), .y9(y[639:576]), .y10(y[703:640]), .y11(y[767:704]));
  assign r = y[64*LANE +: 64];
endmodule
module lec_me_gate #(parameter int LANE = 0) (input wire [767:0] x, input wire [767:0] rc, output wire [63:0] r);
  wire [767:0] y;
  qsag_p2_me u (.x(x), .rc(rc), .y(y));
  assign r = y[64*LANE +: 64];
endmodule
module lec_mi_gold #(parameter int LANE = 0) (input wire [767:0] x, input wire [767:0] rc, output wire [63:0] r);
  wire [767:0] y;
  qsag_ni_p2_mi_spec u (.clk(1'b0), .rst(1'b0),
    .x0(x[63:0]), .x1(x[127:64]), .x2(x[191:128]), .x3(x[255:192]), .x4(x[319:256]), .x5(x[383:320]),
    .x6(x[447:384]), .x7(x[511:448]), .x8(x[575:512]), .x9(x[639:576]), .x10(x[703:640]), .x11(x[767:704]),
    .rc0(rc[63:0]), .rc1(rc[127:64]), .rc2(rc[191:128]), .rc3(rc[255:192]), .rc4(rc[319:256]), .rc5(rc[383:320]),
    .rc6(rc[447:384]), .rc7(rc[511:448]), .rc8(rc[575:512]), .rc9(rc[639:576]), .rc10(rc[703:640]), .rc11(rc[767:704]),
    .y0(y[63:0]), .y1(y[127:64]), .y2(y[191:128]), .y3(y[255:192]), .y4(y[319:256]), .y5(y[383:320]),
    .y6(y[447:384]), .y7(y[511:448]), .y8(y[575:512]), .y9(y[639:576]), .y10(y[703:640]), .y11(y[767:704]));
  assign r = y[64*LANE +: 64];
endmodule
module lec_mi_gate #(parameter int LANE = 0) (input wire [767:0] x, input wire [767:0] rc, output wire [63:0] r);
  wire [767:0] y;
  qsag_p2_mi u (.x(x), .rc(rc), .y(y));
  assign r = y[64*LANE +: 64];
endmodule
// planted fault: the diagonal of lane LANE off by one doubling (lane 2 uses 2^2 instead of 2^1) is
// modelled by swapping two input lanes of the implementation
module lec_mi_mut #(parameter int LANE = 0) (input wire [767:0] x, input wire [767:0] rc, output wire [63:0] r);
  wire [767:0] y;
  qsag_p2_mi u (.x({x[767:192], x[127:64], x[191:128], x[63:0]}), .rc(rc), .y(y));
  assign r = y[64*LANE +: 64];
endmodule
module lec_me_mut #(parameter int LANE = 0) (input wire [767:0] x, input wire [767:0] rc, output wire [63:0] r);
  wire [767:0] y;
  qsag_p2_me u (.x({x[767:192], x[127:64], x[191:128], x[63:0]}), .rc(rc), .y(y));
  assign r = y[64*LANE +: 64];
endmodule

// ---- GF(2^128) multiplier against the bit-serial definition
module lec_gf_gold (input wire [127:0] a, input wire [127:0] b, output logic [127:0] r);
  logic [127:0] acc, sh;
  always_comb begin
    acc = '0;
    sh = a;
    for (int i = 0; i < 128; i++) begin
      if (b[i]) acc ^= sh;
      sh = {sh[126:0], 1'b0} ^ (sh[127] ? 128'h87 : 128'h0);
    end
    r = acc;
  end
endmodule
module lec_gf_gate (input wire [127:0] a, input wire [127:0] b, output wire [127:0] r);
  qsag_gf128_mul u (.a(a), .b(b), .r(r));
endmodule
module lec_gf_mut (input wire [127:0] a, input wire [127:0] b, output wire [127:0] r);
  wire [127:0] g;
  qsag_gf128_mul u (.a(a), .b(b), .r(g));
  assign r = g ^ {127'b0, a[127] & b[127] & a[0] & b[64]};
endmodule

// ---- full multiplier against Obend's fieldMul (expected undecided by SAT: 64x64 multiplier miter)
module lec_mul_gold (input wire [63:0] a, input wire [63:0] b, output wire [63:0] r);
  qsag_ni_gl_mul_spec u (.clk(1'b0), .rst(1'b0), .a(a), .b(b), .r(r));
endmodule
module lec_mul_gate (input wire [63:0] a, input wire [63:0] b, output wire [63:0] r);
  qsag_gl64_mul_csa u (.a(a), .b(b), .r(r));
endmodule
`default_nettype wire

// =====================================================================================
// Decomposed miters. The direct miters "modular-add chain vs carry-save network" above do not
// finish in SAT; these split each proof at the integer sum.
// =====================================================================================
`default_nettype none
// canonical (t mod p) of a 72-bit integer, chained-adder form (the function of qsag_gl64_final_seq)
module lec_reduce72 (input wire [71:0] t, output wire [63:0] r);
  qsag_gl64_final_seq #(.W(72)) u (.x(t), .y(72'b0), .r(r));
endmodule

// Step lemma (one query, independent of the number of operands): reducing after adding one more
// canonicalized word equals the modular add of the reduced partial sum.
//   reduce(T + x) == glAdd(reduce(T), canon(x))     for every T < 2^71, x < 2^64
module lec_step_gold (input wire [70:0] t, input wire [63:0] x, output wire [63:0] r);
  wire [63:0] rt, cx;
  lec_reduce72 u_t (.t({1'b0, t}), .r(rt));
  assign cx = (x >= 64'hFFFF_FFFF_0000_0001) ? x - 64'hFFFF_FFFF_0000_0001 : x;
  qsag_gl64_addsub u_a (.a(rt), .b(cx), .sub(1'b0), .r(r));
endmodule
module lec_step_gate (input wire [70:0] t, input wire [63:0] x, output wire [63:0] r);
  lec_reduce72 u (.t({1'b0, t} + {8'b0, x}), .r(r));
endmodule

// Integer-sum forms of the linear layers: y_l = reduce(sum_j m_lj * x_j + rc_l) with plain adders.
module lec_me_int #(parameter int LANE = 0) (input wire [767:0] x, input wire [767:0] rc, output wire [63:0] r);
  // lane(b, i) = 3i + b ; y(b,i) = 2x(b,i) + 3x(b,i+1) + x(b,i+2) + x(b,i+3) ; out(b,i) = y(b,i) + sum_b' y(b',i)
  localparam int B = LANE % 3;
  localparam int I = LANE / 3;
  function automatic logic [71:0] m4row(input logic [767:0] v, input int b, input int i);
    m4row = {7'b0, v[64*(3*(i % 4) + b) +: 64], 1'b0}
          + {7'b0, v[64*(3*((i + 1) % 4) + b) +: 64], 1'b0} + {8'b0, v[64*(3*((i + 1) % 4) + b) +: 64]}
          + {8'b0, v[64*(3*((i + 2) % 4) + b) +: 64]} + {8'b0, v[64*(3*((i + 3) % 4) + b) +: 64]};
  endfunction
  wire [71:0] t = {m4row(x, B, I)[70:0], 1'b0} + m4row(x, (B + 1) % 3, I) + m4row(x, (B + 2) % 3, I)
                + {8'b0, rc[64*LANE +: 64]};
  lec_reduce72 u (.t(t), .r(r));
endmodule
module lec_mi_int #(parameter int LANE = 0) (input wire [767:0] x, input wire [767:0] rc, output logic [63:0] r);
  // lane 0: -64 x_0 = 64 * (~x_0) - 64 * (2^64 - 1); the constant enters reduced mod p, as in the RTL
  localparam logic [63:0] PRIME = 64'hFFFF_FFFF_0000_0001;
  localparam logic [71:0] K = (72'd64 * (72'(PRIME) - 72'd4294967294)) % 72'(PRIME);
  logic [79:0] s;   // lane 11 carries x << 10: up to 2^74 plus the other terms
  wire  [63:0] rr;
  always_comb begin
    s = {16'b0, rc[64*LANE +: 64]};
    for (int j = 0; j < 12; j++) s += {16'b0, x[64*j +: 64]};
    if (LANE == 0) s += {10'b0, ~x[63:0], 6'b0} + {8'b0, K};
    else s += 80'(x[64*LANE +: 64]) << (LANE - 1);
  end
  qsag_gl64_final_seq #(.W(80)) u (.x(s), .y(80'b0), .r(rr));
  assign r = rr;
endmodule

// the multiplier fold with one row tied off: fold(s, 0) and fold(0, c) against the reducer spec
module lec_fold_c0_gate (input wire [127:0] v, output wire [63:0] r);
  lec_fold_gate u (.s(v), .c(128'b0), .r(r));
endmodule
module lec_fold_s0_gate (input wire [127:0] v, output wire [63:0] r);
  lec_fold_gate u (.s(128'b0), .c(v), .r(r));
endmodule

// GF(2^128) pieces: 64x64 carry-less tree against the bit-serial definition; reduction of a 255-bit
// polynomial against the bit-serial reduction.
module lec_clmul_gold (input wire [63:0] a, input wire [63:0] b, output logic [126:0] p);
  always_comb begin
    p = '0;
    for (int i = 0; i < 64; i++) if (b[i]) p ^= {63'b0, a} << i;
  end
endmodule
module lec_clmul_gate (input wire [63:0] a, input wire [63:0] b, output wire [126:0] p);
  qsag_clmul64 u (.a(a), .b(b), .p(p));
endmodule
`default_nettype wire
