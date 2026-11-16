// Balanced 3:2 compressor tree followed by one carry-select adder, modulo 2^W.
module qsag_sum_csa #(parameter int W = 128, parameter int N = 4) (
    input logic [N*W-1:0] x,
    output logic [W-1:0] y
);
    if (N == 1) begin : g_one
        assign y = x;
    end else if (N == 2) begin : g_two
        qsag_add_split #(.W(W)) u_add (.a(x[0 +: W]), .b(x[W +: W]), .y(y));
    end else begin : g_compress
        localparam int G = N / 3;
        localparam int M = 2*G + N%3;
        logic [M*W-1:0] next_rows;
        for (genvar i = 0; i < G; i++) begin : g_triple
            wire [W-1:0] a = x[(3*i)*W +: W];
            wire [W-1:0] b = x[(3*i+1)*W +: W];
            wire [W-1:0] c = x[(3*i+2)*W +: W];
            assign next_rows[(2*i)*W +: W] = a ^ b ^ c;
            assign next_rows[(2*i+1)*W +: W] = ((a & b) | (a & c) | (b & c)) << 1;
        end
        for (genvar i = 0; i < N%3; i++) begin : g_tail
            assign next_rows[(2*G+i)*W +: W] = x[(3*G+i)*W +: W];
        end
        qsag_sum_csa #(.W(W), .N(M)) u_next (.x(next_rows), .y(y));
    end
endmodule
