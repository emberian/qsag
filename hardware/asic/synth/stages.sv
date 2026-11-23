// Register-to-register stages of the QSAG-NI datapath as combinational tops, for mapped delay
// and area (the flops around them are the st/t registers of qsag_asic_p2_shared).
`default_nettype none
`include "qsag_asic_gen_params.svh"

// S-box cycle: operand select, 4-row Dadda tree, carry-save fold, parallel final adder
module stage_sbox (input wire [63:0] st, input wire [63:0] t, input wire [1:0] sel, output wire [63:0] r);
  qsag_gl64_mul_csa u (.a(sel[0] ? st : t), .b(sel[1] ? t : st), .r(r));
endmodule

// Conventional counterpart: plain multiplier, carry-propagate reduction
module stage_sbox_ref (input wire [63:0] st, input wire [63:0] t, input wire [1:0] sel, output wire [63:0] r);
  qsag_gl64_mul_ref u (.a(sel[0] ? st : t), .b(sel[1] ? t : st), .r(r));
endmodule

// Decoupled partial-round linear stage: pre-staged s_tail + qsag_p2_mi_apply
module stage_partial (
  input wire [63:0]  x0,
  input wire [703:0] x_hi,
  input wire [63:0]  s_tail,
  input wire [767:0] rc,
  output wire [767:0] y
);
  qsag_p2_mi_apply u_m (.x0(x0), .x_hi(x_hi), .s_tail(s_tail), .rc(rc), .y(y));
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
