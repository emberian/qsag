// x mod p for x < 2^136, p = 2^64 - 2^32 + 1 (Goldilocks). Output is canonical (< p).
//
// With x = lo + m*2^64 + h*2^96 + t*2^128 (lo 64 bits, m and h 32 bits, t 8 bits) and
// 2^64 = 2^32 - 1, 2^96 = -1, 2^128 = -2^32 (mod p):
//     x = lo + m*(2^32 - 1) - h - t*2^32   (mod p).
// Stage 1 forms v = lo + m*2^32 + p - m - h - t*2^32 in one carry chain; 0 < v < 3p.
// Stage 2 selects v, v - p or v - 2p. No division, no multiplier, two register stages.
// The 8 guard bits let callers accumulate up to 256 products before reducing once.
module qsag_gl64_reduce (
    input  logic         clk,
    input  logic [135:0] x,
    output logic [63:0]  r
);
    localparam logic [63:0] GL_P = qsag_ni_pkg::GL_P;

    logic [63:0] lo;
    logic [31:0] m, h;
    logic [7:0]  t;
    assign {t, h, m, lo} = x;

    logic [65:0] v_d, v_q;
    assign v_d = {2'b0, lo} + {2'b0, m, 32'b0} + {2'b0, GL_P}
               - {34'b0, m} - {34'b0, h} - {26'b0, t, 32'b0};
    always_ff @(posedge clk) v_q <= v_d;

    // Bits 65:64 of the differences are implied by the sign bit.
    /* verilator lint_off UNUSEDSIGNAL */
    logic [66:0] v1, v2;
    /* verilator lint_on UNUSEDSIGNAL */
    assign v1 = {1'b0, v_q} - {3'b0, GL_P};
    assign v2 = {1'b0, v_q} - {2'b0, GL_P, 1'b0};
    always_ff @(posedge clk) r <= !v2[66] ? v2[63:0] : !v1[66] ? v1[63:0] : v_q[63:0];
endmodule
