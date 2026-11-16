// Goldilocks modular multiplier: r = (a * b) mod p, p = 2^64 - 2^32 + 1, for every pair of
// 64-bit inputs (canonical or not); r is canonical. Latency GL_MUL_LAT = 6, one result per clock.
module qsag_gl64_dsp_mul #(
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic        clk,
    input  logic [63:0] a,
    input  logic [63:0] b,
    output logic [63:0] r
);
    logic [127:0] prod;
    qsag_mul64_dsp #(.AW(AW), .BW(BW)) u_mul (.clk(clk), .a(a), .b(b), .p(prod));
    qsag_gl64_reduce u_red (.clk(clk), .x({8'b0, prod}), .r(r));
endmodule
