// GoldilocksExt4 multiply-accumulate y = a*b + c in F_p[v]/(v^4 - 7) (crates/qsag-agg
// GoldilocksExt4::mul_add). Limb order is qsag's tower order [c0.c0, c0.c1, c1.c0, c1.c1],
// i.e. coefficients of [1, v^2, v, v^3].
//
// Sixteen DSP-tiled 64x64 products; each output coefficient is the exact integer
//   c_k + sum_{i<=k} a_i*b_{k-i} + 7 * sum_{i>k} a_i*b_{k+4-i}   (< 23 * 2^128)
// formed in one carry-save stage (7x = 8x - x) and reduced once, as the software does.
// Inputs must be canonical; outputs are canonical. Latency EXT4_MAC_LAT = 7, one MAC per clock.
module qsag_ext4_mac #(
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic         clk,
    input  logic [255:0] a,
    input  logic [255:0] b,
    input  logic [255:0] c,
    output logic [255:0] y
);
    localparam int MUL64_LAT = qsag_ni_pkg::MUL64_LAT;

    // Storage limb s holds polynomial coefficient PIDX(s); the map is its own inverse.
    function automatic int pidx(input int s);
        pidx = (s == 1) ? 2 : ((s == 2) ? 1 : s);
    endfunction

    logic [16*128-1:0] prod;   // prod[4*i + j] = a_poly[i] * b_poly[j]
    for (genvar i = 0; i < 4; i++) begin : g_i
        for (genvar j = 0; j < 4; j++) begin : g_j
            qsag_mul64_dsp #(.AW(AW), .BW(BW)) u_mul (
                .clk(clk), .a(a[64*pidx(i) +: 64]), .b(b[64*pidx(j) +: 64]),
                .p(prod[128*(4*i + j) +: 128]));
        end
    end

    logic [MUL64_LAT*256-1:0] c_sr;
    always_ff @(posedge clk) c_sr <= {c_sr[(MUL64_LAT-1)*256-1:0], c};

    for (genvar k = 0; k < 4; k++) begin : g_k
        logic [135:0] acc_d, acc_q;
        always_comb begin
            acc_d = 136'(c_sr[(MUL64_LAT-1)*256 + 64*pidx(k) +: 64]);
            for (int i = 0; i < 4; i++) begin
                if (i <= k) acc_d = acc_d + 136'(prod[128*(4*i + (k - i)) +: 128]);
                else        acc_d = acc_d + (136'(prod[128*(4*i + (k + 4 - i)) +: 128]) << 3)
                                          - 136'(prod[128*(4*i + (k + 4 - i)) +: 128]);
            end
        end
        always_ff @(posedge clk) acc_q <= acc_d;
        qsag_gl64_reduce u_red (.clk(clk), .x(acc_q), .r(y[64*pidx(k) +: 64]));
    end
endmodule
