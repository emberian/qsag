// 4-bit/cycle Horner step in GF(2^128) = F_2[x] / (x^128 + x^7 + x^2 + x + 1).
// Cuts GF128.MUL latency by 4x (32 steps instead of 128) in 3 XOR levels (< 4 ns SS).
module qsag_ass2_gf_step (
    input  logic [127:0] a,
    input  logic [127:0] acc,
    input  logic [3:0]   bits_in,
    output logic [127:0] result
);
    function automatic logic [127:0] xtime(input logic [127:0] v);
        return {v[126:0], 1'b0} ^ (v[127] ? 128'h87 : 128'd0);
    endfunction

    wire [127:0] s0 = xtime(acc) ^ (bits_in[3] ? a : 128'd0);
    wire [127:0] s1 = xtime(s0)  ^ (bits_in[2] ? a : 128'd0);
    wire [127:0] s2 = xtime(s1)  ^ (bits_in[1] ? a : 128'd0);
    assign result   = xtime(s2)  ^ (bits_in[0] ? a : 128'd0);
endmodule
