// Formal harnesses for qsag_gf128_clmul (used by lec/lec_gf128.sh only).
`default_nettype none

// G1: one digit step against the bit-serial field specification:
//     step(r, h, d) == r * z^D + h * d   in GF(2)[z] / (z^128 + z^7 + z^2 + z + 1)
module lec_gf128_step #(
    parameter int D = 2
) (
    input  wire [127:0] r,
    input  wire [127:0] h,
    input  wire [D-1:0] d,
    output wire         ok
);
    wire [127:0] o, rz, hd;
    qsag_gf128_step #(.D(D)) u_dut (.r(r), .h(h), .d(d), .o(o));
    qsag_gf128_ref u_rz (.a(r), .b(128'd1 << D), .p(rz));
    qsag_gf128_ref u_hd (.a(h), .b({{(128-D){1'b0}}, d}), .p(hd));
    assign ok = (o == (rz ^ hd));
endmodule
`default_nettype wire
