// Wiedemann tower product using the existing polynomial-basis multiplier.
// Maps are combinational; the multiplier retains its three-cycle latency.
module qsag_gf128_tower_mul (
    input logic clk,
    input logic [127:0] a, b,
    output logic [127:0] r
);
    logic [127:0] pa, pb, pr;
    qsag_gf128_tower_map u_a (.x(a), .y(pa));
    qsag_gf128_tower_map u_b (.x(b), .y(pb));
    qsag_gf128_clmul u_mul (.clk(clk), .a(pa), .b(pb), .r(pr));
    qsag_gf128_tower_map #(.INVERSE(1)) u_r (.x(pr), .y(r));
endmodule
