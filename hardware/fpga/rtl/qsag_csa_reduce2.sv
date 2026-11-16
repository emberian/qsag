// Balanced 3:2 carry-save (CSA) LUT compressor tree modulo 2^W: compresses N W-bit operands
// to two carry-save vectors (s, c) with zero carry propagation.
module qsag_csa_reduce2 #(
    parameter int W = 128,
    parameter int N = 4
) (
    input  logic [N*W-1:0] x,
    output logic [W-1:0]   s,
    output logic [W-1:0]   c
);
    if (N == 1) begin : g_one
        assign s = x;
        assign c = '0;
    end else if (N == 2) begin : g_two
        assign s = x[0 +: W];
        assign c = x[W +: W];
    end else begin : g_csa
        localparam int G = N / 3;
        localparam int R = N % 3;
        localparam int M = 2 * G + R;
        logic [M*W-1:0] nxt;
        for (genvar i = 0; i < G; i++) begin : g_fa
            wire [W-1:0] a = x[(3*i)*W +: W];
            wire [W-1:0] b = x[(3*i+1)*W +: W];
            wire [W-1:0] d = x[(3*i+2)*W +: W];
            assign nxt[(2*i)*W +: W]   = a ^ b ^ d;
            assign nxt[(2*i+1)*W +: W] = ((a & b) | (a & d) | (b & d)) << 1;
        end
        for (genvar i = 0; i < R; i++) begin : g_rem
            assign nxt[(2*G+i)*W +: W] = x[(3*G+i)*W +: W];
        end
        qsag_csa_reduce2 #(.W(W), .N(M)) u_rec (.x(nxt), .s(s), .c(c));
    end
endmodule
