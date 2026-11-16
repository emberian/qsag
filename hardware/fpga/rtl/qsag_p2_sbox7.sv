// Poseidon2 S-box x^7 mod p as x^7 = (x^2 * x) * (x^2)^2. Four Goldilocks multipliers in three
// levels; latency P2_SBOX_LAT = 3 * GL_MUL_LAT, one result per clock.
module qsag_p2_sbox7 #(
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic        clk,
    input  logic [63:0] x,
    output logic [63:0] y
);
    localparam int GL_MUL_LAT = qsag_ni_pkg::GL_MUL_LAT;

    logic [GL_MUL_LAT*64-1:0] x_dly;
    always_ff @(posedge clk) x_dly <= {x_dly[(GL_MUL_LAT-1)*64-1:0], x};

    logic [63:0] x2, x3, x4;
    qsag_gl64_dsp_mul #(.AW(AW), .BW(BW)) u_x2 (.clk(clk), .a(x), .b(x), .r(x2));
    qsag_gl64_dsp_mul #(.AW(AW), .BW(BW)) u_x3 (
        .clk(clk), .a(x2), .b(x_dly[(GL_MUL_LAT-1)*64 +: 64]), .r(x3));
    qsag_gl64_dsp_mul #(.AW(AW), .BW(BW)) u_x4 (.clk(clk), .a(x2), .b(x2), .r(x4));
    qsag_gl64_dsp_mul #(.AW(AW), .BW(BW)) u_x7 (.clk(clk), .a(x3), .b(x4), .r(y));
endmodule
