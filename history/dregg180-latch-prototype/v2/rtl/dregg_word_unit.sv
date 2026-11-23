// Dregg-180 v2 word unit (ARCHITECTURE.md 5.4; v2/model/units.py alu() and unary()).
//
// Combinational. y = f(h, x) where h is the accumulator (the visible value of the hold register) and
// x is the operand: a register-file row, a 16-bit immediate, a constant, a framer field, a payload
// word or a FRAM word, selected by the sequencer.
//
//   fn  LD  y = x                     XOR AND OR  bitwise
//       ADD y = (h + x) mod 2^32, cy = carry out of bit 31       (upper half of y is zero)
//       SUB y = (h - x) mod 2^32, cy = borrow
//       CMP y = h, ne = (h != x)      (the sequencer ORs ne into the sticky flag Z)
//       UN  y = wiring-only function `un` of h
`default_nettype none

module dregg_word_unit (
    input  wire  [63:0] h,
    input  wire  [63:0] x,
    input  wire  [4:0]  op,      // OP_LD .. OP_UN (other values: y = x)
    input  wire  [6:0]  un,      // unary function code (OP_UN)
    output logic [63:0] y,
    output wire         cy,
    output wire         ne,
    output wire         un_ok    // the unary code is defined
);
`include "dregg_defs.svh"

    // one 33-bit adder serves ADD and SUB: h + x, or h + ~x + 1 (carry out = no borrow)
    wire        sub = (op == OP_SUB);
    wire [32:0] sum = {1'b0, h[31:0]} + {1'b0, x[31:0] ^ {32{sub}}} + {32'd0, sub};
    assign cy = sum[32] ^ sub;
    assign ne = (h != x);

    function automatic logic [31:0] bswap32(input logic [31:0] v);
        bswap32 = {v[7:0], v[15:8], v[23:16], v[31:24]};
    endfunction

    logic [63:0] u;
    always_comb begin
        u = h;
        unique case (un)
            UN_ID:    u = h;
            UN_NIB:   for (int i = 0; i < 8; i++) u[8*i +: 8] = {h[8*i +: 4], h[8*i + 4 +: 4]};
            UN_BE32:  u = {bswap32(h[63:32]), bswap32(h[31:0])};
            UN_HSWAP: u = {h[31:0], h[63:32]};
            UN_LO32:  u = {32'd0, h[31:0]};
            UN_HI32:  u = {h[63:32], 32'd0};
            UN_SHR1:  u = {1'd0, h[63:1]};
            UN_SHR4:  u = {4'd0, h[63:4]};
            UN_SHR8:  u = {8'd0, h[63:8]};
            UN_SHR16: u = {16'd0, h[63:16]};
            UN_SHL1:  u = {h[62:0], 1'd0};
            UN_SHL4:  u = {h[59:0], 4'd0};
            UN_SHL8:  u = {h[55:0], 8'd0};
            default:  u = h;
        endcase
    end
    assign un_ok = (un < 7'(N_UN));

    always_comb begin
        unique case (op)
            OP_XOR:  y = h ^ x;
            OP_AND:  y = h & x;
            OP_OR:   y = h | x;
            OP_ADD,
            OP_SUB:  y = {32'd0, sum[31:0]};
            OP_CMP:  y = h;
            OP_UN:   y = u;
            default: y = x;
        endcase
    end
endmodule
`default_nettype wire
