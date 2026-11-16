// Reduce a 255-bit GF(2)[x] product modulo x^128 + x^7 + x^2 + x + 1. Combinational XORs.
// x^128 = x^7 + x^2 + x + 1; the six bits the first fold pushes past x^127 are folded again.
module qsag_gf128_reduce (
    input  logic [254:0] c,
    output logic [127:0] r
);
    logic [126:0] hi;
    logic [133:0] f1;
    logic [5:0]   ov;
    logic [12:0]  f2;
    assign hi = c[254:128];
    assign f1 = 134'(hi) ^ (134'(hi) << 1) ^ (134'(hi) << 2) ^ (134'(hi) << 7);
    assign ov = f1[133:128];
    assign f2 = 13'(ov) ^ (13'(ov) << 1) ^ (13'(ov) << 2) ^ (13'(ov) << 7);
    assign r  = c[127:0] ^ f1[127:0] ^ 128'(f2);
endmodule
