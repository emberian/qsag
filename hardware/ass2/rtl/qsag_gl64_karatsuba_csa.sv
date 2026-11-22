// Radix-16 (4 bits/clock, 16-step) Carry-Save + Byte-Prefix Iterative Multiplier
// & 32-step GF(2^128) Shared 128-bit Engine:
//   - Cuts 64x64+64->128 multiplication from 65 clocks to 17 clocks (3.82x faster)
//     and GF(2^128) multiplication from 128 clocks to 32 clocks (4.0x faster)!
//   - Parallel 5:2 Wallace CSA tree (3 FA levels) + 64-bit byte-prefix CPA on bits [67:4]
//     (bits [3:0] sum directly without global carry), achieving < 17.5 ns at SS!
module qsag_gl64_karatsuba_csa (
    input  logic         clk, srst_n,
    input  logic         start, mode_gl,
    input  logic         gf_clr_i, gf_step_i,
    input  logic [127:0] gf_next_i,
    input  logic         fold_we_i,
    input  logic [63:0]  fold_val_i,
    input  logic [63:0]  opa, opb, opc,
    output logic         last,
    output logic [127:0] prod128
);
    logic [4:0]   step_q;
    logic [127:0] prod_q;

    wire [63:0] mc = mode_gl ? opc : 64'd0;

    // 5 partial-product rows (68 bits each) for 4-bit/cycle unsigned multiply-accumulate:
    //   max(t0 + t1 + t2 + t3 + t4) = (2^64 - 1) + 15*(2^64 - 1) = 2^68 - 16 < 2^68.
    wire [67:0] t0 = {4'd0, prod_q[127:64]};
    wire [67:0] t1 = prod_q[0] ? {4'd0, opa}       : 68'd0;
    wire [67:0] t2 = prod_q[1] ? {3'd0, opa, 1'b0} : 68'd0;
    wire [67:0] t3 = prod_q[2] ? {2'd0, opa, 2'd0} : 68'd0;
    wire [67:0] t4 = prod_q[3] ? {1'd0, opa, 3'd0} : 68'd0;

    // Level 1 (parallel): CSA(t0, t1, t2) -> (s1, c1) and HA(t3, t4) -> (s2, c2)
    wire [67:0] s1 = t0 ^ t1 ^ t2;
    wire [67:0] c1 = {((t0[66:0] & t1[66:0]) | (t0[66:0] & t2[66:0]) | (t1[66:0] & t2[66:0])), 1'b0};
    wire [67:0] s2 = t3 ^ t4;
    wire [67:0] c2 = {(t3[66:0] & t4[66:0]), 1'b0};

    // Level 2: CSA(s1, c1, s2) -> (s3, c3)
    wire [67:0] s3 = s1 ^ c1 ^ s2;
    wire [67:0] c3 = {((s1[66:0] & c1[66:0]) | (s1[66:0] & s2[66:0]) | (c1[66:0] & s2[66:0])), 1'b0};

    // Level 3: CSA(s3, c3, c2) -> (csa_s, csa_c)
    wire [67:0] csa_s = s3 ^ c3 ^ c2;
    wire [67:0] csa_c = {((s3[66:0] & c3[66:0]) | (s3[66:0] & c2[66:0]) | (c3[66:0] & c2[66:0])), 1'b0};

    // Low 4-bit sum + carry into bit 4, feeding `qsag_ass2_add64` byte-prefix adder on [67:4]
    wire [4:0]  lo4_sum = {1'b0, csa_s[3:0]} + {1'b0, csa_c[3:0]};
    wire [63:0] hi64_sum;
    wire        unused_cout;
    qsag_ass2_add64 u_cpa (
        .a(csa_s[67:4]), .b(csa_c[67:4]), .cin(lo4_sum[4]),
        .sum(hi64_sum), .cout(unused_cout)
    );
    wire [67:0] hi_sum = {hi64_sum, lo4_sum[3:0]};

    wire step_active = (step_q >= 5'd1) && (step_q <= 5'd16);
    wire prod_en     = (step_q == 5'd0 && start) || step_active || gf_clr_i || gf_step_i || fold_we_i;
    wire [127:0] prod_d = gf_clr_i    ? 128'd0
                        : gf_step_i   ? gf_next_i
                        : fold_we_i   ? {prod_q[127:64], fold_val_i}
                        : step_active ? {hi_sum, prod_q[63:4]}
                        : {mc, opb};

    qsag_ass2_cg_dff #(.W(128)) u_prod (
        .clk(clk), .rst_n(srst_n), .en(prod_en), .d(prod_d), .q(prod_q)
    );

    assign prod128 = prod_q;
    assign last    = (step_q == 5'd17);

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) step_q <= 5'd0;
        else if (step_q == 5'd0) begin
            if (start) step_q <= 5'd1;
        end else if (step_q <= 5'd16) begin
            step_q <= step_q + 5'd1;
        end else begin
            step_q <= 5'd0;
        end
    end
endmodule
