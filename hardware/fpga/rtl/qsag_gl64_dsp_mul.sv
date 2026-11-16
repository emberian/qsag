// Goldilocks modular multiplier: r = (a * b) mod p, p = 2^64 - 2^32 + 1, for every pair of
// 64-bit inputs (canonical or not); r is canonical.
// Default REG_OUT=1: latency GL_MUL_LAT = 5 clocks, one result per clock.
// REG_OUT=0: latency 4 clocks, combinational canonical output for direct capture into DSP AREG/BREG.
module qsag_gl64_dsp_mul #(
    parameter int AW = 26,
    parameter int BW = 17,
    parameter bit REG_OUT = 1'b1
) (
    input  logic        clk,
    input  logic [63:0] a,
    input  logic [63:0] b,
    output logic [63:0] r
);
    logic [127:0] prod;
    qsag_mul64_dsp #(.AW(AW), .BW(BW)) u_mul (.clk(clk), .a(a), .b(b), .p(prod));
    qsag_gl64_reduce #(.REG_OUT(REG_OUT)) u_red (.clk(clk), .x({8'b0, prod}), .r(r));
endmodule
