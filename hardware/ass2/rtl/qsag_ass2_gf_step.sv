// Area-minimal 1-bit/cycle Horner step in GF(2^128) = F_2[x] / (x^128 + x^7 + x^2 + x + 1).
module qsag_ass2_gf_step (
    input  logic [127:0] a,
    input  logic [127:0] acc,
    input  logic         bit_in,
    output logic [127:0] result
);
    wire [127:0] sh = {acc[126:0], 1'b0} ^ (acc[127] ? 128'h87 : 128'd0);
    assign result   = sh ^ (bit_in ? a : 128'd0);
endmodule
