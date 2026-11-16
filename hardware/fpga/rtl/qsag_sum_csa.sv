// Balanced 3:2 carry-save (CSA) LUT compressor tree followed by one split parallel-prefix
// carry-select adder, modulo 2^W.
module qsag_sum_csa #(
    parameter int W = 128,
    parameter int N = 4,
    parameter int CHUNK = 24
) (
    input  logic [N*W-1:0] x,
    output logic [W-1:0]   y
);
    if (N == 1) begin : g_one
        assign y = x;
    end else begin : g_many
        logic [W-1:0] s, c;
        qsag_csa_reduce2 #(.W(W), .N(N)) u_csa (.x(x), .s(s), .c(c));
        qsag_add_split #(.W(W), .CHUNK(CHUNK)) u_add (.a(s), .b(c), .y(y));
    end
endmodule
