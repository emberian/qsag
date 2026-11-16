// GF(2^128) multiplier, GF(2)[x] / (x^128 + x^7 + x^2 + x + 1), bit j of a word is the
// coefficient of x^j (crates/qsag-accel gf2_128_mul, qsag-core rss256 / triple_f2 MAC field).
// Karatsuba carry-less product, then the two-fold reduction. Latency GF128_LAT = 3.
module qsag_gf128_clmul #(
    parameter int BASE = 8
) (
    input  logic         clk,
    input  logic [127:0] a,
    input  logic [127:0] b,
    output logic [127:0] r
);
    logic [127:0] a_q, b_q, red;
    logic [254:0] prod, prod_q;
    qsag_clmul_kara #(.W(128), .BASE(BASE)) u_mul (.a(a_q), .b(b_q), .p(prod));
    qsag_gf128_reduce u_red (.c(prod_q), .r(red));
    always_ff @(posedge clk) begin
        a_q    <= a;
        b_q    <= b;
        prod_q <= prod;
        r      <= red;
    end
endmodule
