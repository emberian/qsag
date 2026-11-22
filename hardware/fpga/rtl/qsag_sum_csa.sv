// Balanced 3:2 carry-save (CSA) LUT compressor tree followed by one split parallel-prefix
// carry-select adder, modulo 2^W.
(* flatten *)
module qsag_sum_csa #(
    parameter int W = 128,
    parameter int N = 4,
    parameter int CHUNK = 24
) (
    input  logic [N*W-1:0] x,
    output logic [W-1:0]   y
);
`ifdef QSAG_ECP5_CARRY
    /* verilator lint_off UNUSEDPARAM */
    localparam int UNUSED_CHUNK = CHUNK;
    /* verilator lint_on UNUSEDPARAM */
    if (N == 1) begin : g_one
        assign y = x;
    end else if (N == 2) begin : g_two
        assign y = x[0 +: W] + x[W +: W];
    end else begin : g_tree
        localparam int NL = N / 2;
        localparam int NH = N - NL;
        logic [W-1:0] yl, yh;
        qsag_sum_csa #(.W(W), .N(NL), .CHUNK(CHUNK)) u_lo (.x(x[0 +: NL*W]),     .y(yl));
        qsag_sum_csa #(.W(W), .N(NH), .CHUNK(CHUNK)) u_hi (.x(x[NL*W +: NH*W]), .y(yh));
        assign y = yl + yh;
    end
`else
    if (N == 1) begin : g_one
        assign y = x;
    end else begin : g_many
        logic [W-1:0] s, c;
        qsag_csa_reduce2 #(.W(W), .N(N)) u_csa (.x(x), .s(s), .c(c));
        qsag_add_split #(.W(W), .CHUNK(CHUNK)) u_add (.a(s), .b(c), .y(y));
    end
`endif
endmodule
