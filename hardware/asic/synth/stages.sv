// Register-to-register stages of the QSAG-NI datapath as combinational tops, for mapped delay
// and area (the flops around them are the st/t registers of qsag_asic_ext4_p2_shared).
`default_nettype none
`include "qsag_asic_gen_params.svh"

// S-box cycle: operand select, product tree, carry-save fold, parallel final adder
module stage_sbox (input wire [63:0] st, input wire [63:0] t, input wire [1:0] sel, output wire [63:0] r);
  qsag_gl64_mul_csa u (.a(sel[0] ? st : t), .b(sel[1] ? t : st), .r(r));
endmodule
// conventional counterpart: plain multiplier, carry-propagate reduction
module stage_sbox_ref (input wire [63:0] st, input wire [63:0] t, input wire [1:0] sel, output wire [63:0] r);
  qsag_gl64_mul_ref u (.a(sel[0] ? st : t), .b(sel[1] ? t : st), .r(r));
endmodule
// last partial-round cycle: product tree, fold, M_I with the product still in carry-save form
module stage_partial (input wire [63:0] a, input wire [63:0] b, input wire [767:0] x, input wire [767:0] rc,
                      output wire [767:0] y);
  wire [127:0] s, c;
  wire [`QSAG_FOLD_W-1:0] fx, fy;
  qsag_gl64_mul_tree u_t (.a(a), .b(b), .s(s), .c(c));
  qsag_gl64_fold u_f (.s(s), .c(c), .x(fx), .y(fy));
  qsag_p2_mi_fused u_m (.sx(fx), .sy(fy), .x(x), .rc(rc), .y(y));
endmodule
// GoldilocksExt4 multiply-add: 16 trees, four fused coefficient accumulators
module stage_ext4 (input wire [255:0] a, input wire [255:0] b, input wire [255:0] z, output wire [255:0] r);
  wire [127:0] ps [16];
  wire [127:0] pc [16];
  for (genvar i = 0; i < 4; i++) begin : g_i
    for (genvar j = 0; j < 4; j++) begin : g_j
      qsag_gl64_mul_tree u (.a(a[64*i +: 64]), .b(b[64*j +: 64]), .s(ps[4*i + j]), .c(pc[4*i + j]));
    end
  end
  `define PROD(i, k) (4*(i) + (((k) - (i) + 4) % 4))
  qsag_ext4_coef0 u0 (.s0(ps[`PROD(0,0)]), .c0(pc[`PROD(0,0)]), .s1(ps[`PROD(1,0)]), .c1(pc[`PROD(1,0)]), .s2(ps[`PROD(2,0)]), .c2(pc[`PROD(2,0)]), .s3(ps[`PROD(3,0)]), .c3(pc[`PROD(3,0)]), .z(z[63:0]), .r(r[63:0]));
  qsag_ext4_coef1 u1 (.s0(ps[`PROD(0,1)]), .c0(pc[`PROD(0,1)]), .s1(ps[`PROD(1,1)]), .c1(pc[`PROD(1,1)]), .s2(ps[`PROD(2,1)]), .c2(pc[`PROD(2,1)]), .s3(ps[`PROD(3,1)]), .c3(pc[`PROD(3,1)]), .z(z[127:64]), .r(r[127:64]));
  qsag_ext4_coef2 u2 (.s0(ps[`PROD(0,2)]), .c0(pc[`PROD(0,2)]), .s1(ps[`PROD(1,2)]), .c1(pc[`PROD(1,2)]), .s2(ps[`PROD(2,2)]), .c2(pc[`PROD(2,2)]), .s3(ps[`PROD(3,2)]), .c3(pc[`PROD(3,2)]), .z(z[191:128]), .r(r[191:128]));
  qsag_ext4_coef3 u3 (.s0(ps[`PROD(0,3)]), .c0(pc[`PROD(0,3)]), .s1(ps[`PROD(1,3)]), .c1(pc[`PROD(1,3)]), .s2(ps[`PROD(2,3)]), .c2(pc[`PROD(2,3)]), .s3(ps[`PROD(3,3)]), .c3(pc[`PROD(3,3)]), .z(z[255:192]), .r(r[255:192]));
  `undef PROD
endmodule
module stage_me (input wire [767:0] x, input wire [767:0] rc, output wire [767:0] y);
  qsag_p2_me u (.x(x), .rc(rc), .y(y));
endmodule
module stage_reduce (input wire [127:0] v, output wire [63:0] r);
  qsag_gl64_reduce128_csa u (.v(v), .r(r));
endmodule
module stage_reduce_ref (input wire [127:0] v, output wire [63:0] r);
  qsag_gl64_reduce128_ref u (.v(v), .r(r));
endmodule
module stage_keccak2 (input wire [1599:0] a, input wire [63:0] rc0, input wire [63:0] rc1, output wire [1599:0] o);
  wire [1599:0] m;
  qsag_keccak_round u0 (.a(a), .rc(rc0), .o(m));
  qsag_keccak_round u1 (.a(m), .rc(rc1), .o(o));
endmodule
module stage_gf128 (input wire [127:0] a, input wire [127:0] b, output wire [127:0] r);
  qsag_gf128_mul u (.a(a), .b(b), .r(r));
endmodule
module stage_tower128 (input wire [127:0] a, input wire [127:0] b, output wire [127:0] r);
  qsag_tower128_mul u (.a(a), .b(b), .r(r));
endmodule
`default_nettype wire
