// Quintic Goldilocks extension multiply-accumulate y = a*b + c in F_p[X]/(X^5 - 3)
// (`crates/qsag-agg/src/zk_hem/v2/field5.rs` `Fp5::mul_add`, SECURITY.md §V2.10).
// Limb order is the canonical flat power basis [c0, c1, c2, c3, c4] = c0 + c1*X + ... + c4*X^4.
//
// 14-multiply Split-(3,2) Karatsuba architecture (14 x 9 = 126 DSPs on both DSP48E2 & MULT18X18D):
//   Stage 0 (1 clk) : 9 canonical modular pre-sums over {0, +1} subsets (zero pre-subtractions!)
//   Stages 1..3     : 14 x 9-DSP exact 64x64 products m[0..13] (`qsag_mul64_dsp`, MUL64_LAT=3)
//   Stage 4 (1 clk) : unsigned carry-save Karatsuba recombination mod (X^5 - 3) using
//                     ~m = (2^128 - 1) - m and (2^128 - 1) + (2^32 + 1) == 0 (mod p), keeping
//                     every accumulator strictly inside (0, 2^134)
//   Stages 5..6     : five canonical Goldilocks reductions (`qsag_gl64_reduce`, RED_LAT=2)
// Inputs must be canonical (< p); outputs are canonical (< p). Latency EXT5_MAC_LAT = 7, 1 MAC/clk.
module qsag_ext5_mac #(
    parameter int AW = 26,
    parameter int BW = 17
) (
    input  logic         clk,
    input  logic [319:0] a,
    input  logic [319:0] b,
    input  logic [319:0] c,
    output logic [319:0] y
);
    localparam int MUL64_LAT = qsag_ni_pkg::MUL64_LAT;
    localparam int C_DLY     = 1 + MUL64_LAT; // 4 clocks to align with m[0..13]
    localparam int CHUNK     = (AW <= 16) ? 16 : 24;
    localparam logic [65:0] NEG_1P66 = 66'h3_0000_0000_FFFF_FFFF; // 2^66 - GL_P
    localparam logic [66:0] NEG_1P67 = 67'h7_0000_0000_FFFF_FFFF; // 2^67 - GL_P
    localparam logic [66:0] NEG_2P67 = 67'h6_0000_0001_FFFF_FFFE; // 2^67 - 2*GL_P
    localparam logic [66:0] NEG_3P67 = 67'h5_0000_0002_FFFF_FFFD; // 2^67 - 3*GL_P
    localparam logic [135:0] C1      = 136'h0000_0001_0000_0001;  // (2^128 - 1) + C1 == 0 (mod p)

    wire [63:0] a0 = a[0   +: 64], a1 = a[64  +: 64], a2 = a[128 +: 64], a3 = a[192 +: 64], a4 = a[256 +: 64];
    wire [63:0] b0 = b[0   +: 64], b1 = b[64  +: 64], b2 = b[128 +: 64], b3 = b[192 +: 64], b4 = b[256 +: 64];

    // Stage 0a: 12 canonical 2-operand sums:
    //   0: a0+a1, 1: a0+a2, 2: a1+a2, 3: a3+a4, 4: a0+a3, 5: a1+a4 (and 6..11 for b).
    wire [11:0][63:0] p2_lhs = {b1, b0, b3, b1, b0, b0, a1, a0, a3, a1, a0, a0};
    wire [11:0][63:0] p2_rhs = {b4, b3, b4, b2, b2, b1, a4, a3, a4, a2, a2, a1};
    logic [11:0][63:0] p2_sum;
    for (genvar i = 0; i < 12; i++) begin : g_add2
        /* verilator lint_off UNUSEDSIGNAL */
        logic [64:0] s0;
        logic [65:0] s1;
        /* verilator lint_on UNUSEDSIGNAL */
        qsag_add_split #(.W(65), .CHUNK(16)) u_s0 (
            .a({1'b0, p2_lhs[i]}), .b({1'b0, p2_rhs[i]}), .y(s0));
        qsag_sum_csa #(.W(66), .N(3), .CHUNK(16)) u_s1 (
            .x({NEG_1P66, {2'b0, p2_rhs[i]}, {2'b0, p2_lhs[i]}}), .y(s1));
        assign p2_sum[i] = !s1[65] ? s1[63:0] : s0[63:0];
    end

    // Stage 0b: 6 canonical 3/4-operand sums (using x3 = 0 for the 3-operand ones):
    //   0: a0+a1+a3+a4, 1: a0+a2+a3, 2: a1+a2+a4
    //   3: b0+b1+b3+b4, 4: b0+b2+b3, 5: b1+b2+b4
    wire [5:0][255:0] p4_in = {
        {64'd0, b4, b2, b1},
        {64'd0, b3, b2, b0},
        {b4,    b3, b1, b0},
        {64'd0, a4, a2, a1},
        {64'd0, a3, a2, a0},
        {a4,    a3, a1, a0}
    };
    logic [5:0][63:0] p4_sum;
    for (genvar i = 0; i < 6; i++) begin : g_add4
        wire [63:0] x0 = p4_in[i][0   +: 64], x1 = p4_in[i][64  +: 64];
        wire [63:0] x2 = p4_in[i][128 +: 64], x3 = p4_in[i][192 +: 64];
        wire [4*67-1:0] base = {{3'b0, x3}, {3'b0, x2}, {3'b0, x1}, {3'b0, x0}};
        /* verilator lint_off UNUSEDSIGNAL */
        logic [65:0] s0;
        logic [66:0] s1, s2, s3;
        /* verilator lint_on UNUSEDSIGNAL */
        qsag_sum_csa #(.W(66), .N(4), .CHUNK(16)) u_s0 (
            .x({{2'b0, x3}, {2'b0, x2}, {2'b0, x1}, {2'b0, x0}}), .y(s0));
        qsag_sum_csa #(.W(67), .N(5), .CHUNK(16)) u_s1 (.x({NEG_1P67, base}), .y(s1));
        qsag_sum_csa #(.W(67), .N(5), .CHUNK(16)) u_s2 (.x({NEG_2P67, base}), .y(s2));
        qsag_sum_csa #(.W(67), .N(5), .CHUNK(16)) u_s3 (.x({NEG_3P67, base}), .y(s3));
        assign p4_sum[i] = !s3[66] ? s3[63:0] : !s2[66] ? s2[63:0] : !s1[66] ? s1[63:0] : s0[63:0];
    end

    logic [13:0][63:0] ma_q, mb_q;
    always_ff @(posedge clk) begin
        ma_q[0]  <= a0;         mb_q[0]  <= b0;
        ma_q[1]  <= a1;         mb_q[1]  <= b1;
        ma_q[2]  <= a2;         mb_q[2]  <= b2;
        ma_q[3]  <= p2_sum[0];  mb_q[3]  <= p2_sum[6];   // (0+1)
        ma_q[4]  <= p2_sum[1];  mb_q[4]  <= p2_sum[7];   // (0+2)
        ma_q[5]  <= p2_sum[2];  mb_q[5]  <= p2_sum[8];   // (1+2)
        ma_q[6]  <= a3;         mb_q[6]  <= b3;
        ma_q[7]  <= a4;         mb_q[7]  <= b4;
        ma_q[8]  <= p2_sum[3];  mb_q[8]  <= p2_sum[9];   // (3+4)
        ma_q[9]  <= p2_sum[4];  mb_q[9]  <= p2_sum[10];  // (0+3)
        ma_q[10] <= p2_sum[5];  mb_q[10] <= p2_sum[11];  // (1+4)
        ma_q[11] <= p4_sum[0];  mb_q[11] <= p4_sum[3];   // (0+1+3+4)
        ma_q[12] <= p4_sum[1];  mb_q[12] <= p4_sum[4];   // (0+2+3)
        ma_q[13] <= p4_sum[2];  mb_q[13] <= p4_sum[5];   // (1+2+4)
    end

    // Stages 1..3: 14 x 9-DSP exact 64x64 multipliers.
    logic [13:0][127:0] m;
    for (genvar i = 0; i < 14; i++) begin : g_mul
        qsag_mul64_dsp #(.AW(AW), .BW(BW)) u_mul (
            .clk(clk), .a(ma_q[i]), .b(mb_q[i]), .p(m[i]));
    end

    logic [C_DLY*320-1:0] c_sr;
    always_ff @(posedge clk) c_sr <= {c_sr[(C_DLY-1)*320-1:0], c};
    wire [63:0] c0 = c_sr[(C_DLY-1)*320 + 0   +: 64];
    wire [63:0] c1 = c_sr[(C_DLY-1)*320 + 64  +: 64];
    wire [63:0] c2 = c_sr[(C_DLY-1)*320 + 128 +: 64];
    wire [63:0] c3 = c_sr[(C_DLY-1)*320 + 192 +: 64];
    wire [63:0] c4 = c_sr[(C_DLY-1)*320 + 256 +: 64];

    logic [13:0][135:0] pm;
    logic [10:0][135:0] nm;
    for (genvar i = 0; i < 14; i++) begin : g_pm
        assign pm[i] = {8'd0,  m[i]};
    end
    for (genvar i = 0; i < 11; i++) begin : g_nm
        assign nm[i] = {8'd0, ~m[i]};
    end

    // Stage 4: exact Split-(3,2) Karatsuba recombination mod (X^5 - 3).
    logic [4:0][135:0] acc_d, acc_q;

    // y0 = c0 + 4*m0 + 3*m10 + 3*m12 - 3*m1 - 3*m4 - 3*m7 - 3*m9  (+ 12*C1)
    wire [15*136-1:0] t_y0 = {
        136'(12) * C1, 136'(c0), pm[0] << 2,
        pm[10], pm[10] << 1,
        pm[12], pm[12] << 1,
        nm[1],  nm[1]  << 1,
        nm[4],  nm[4]  << 1,
        nm[7],  nm[7]  << 1,
        nm[9],  nm[9]  << 1
    };
    qsag_sum_csa #(.W(136), .N(15), .CHUNK(CHUNK)) u_y0 (.x(t_y0), .y(acc_d[0]));

    // y1 = c1 + m3 + 2*m1 + 3*m6 + 3*m13 - m0 - 3*m5 - 3*m10  (+ 7*C1)
    wire [13*136-1:0] t_y1 = {
        136'(7) * C1, 136'(c1), pm[3], pm[1] << 1,
        pm[6],  pm[6]  << 1,
        pm[13], pm[13] << 1,
        nm[0],
        nm[5],  nm[5]  << 1,
        nm[10], nm[10] << 1
    };
    qsag_sum_csa #(.W(136), .N(13), .CHUNK(CHUNK)) u_y1 (.x(t_y1), .y(acc_d[1]));

    // y2 = c2 + m1 + m4 + 3*m8 - m0 - m2 - 3*m6 - 3*m7  (+ 8*C1)
    wire [12*136-1:0] t_y2 = {
        136'(8) * C1, 136'(c2), pm[1], pm[4],
        pm[8], pm[8] << 1,
        nm[0], nm[2],
        nm[6], nm[6] << 1,
        nm[7], nm[7] << 1
    };
    qsag_sum_csa #(.W(136), .N(12), .CHUNK(CHUNK)) u_y2 (.x(t_y2), .y(acc_d[2]));

    // y3 = c3 + m5 + m9 + 3*m7 - m0 - m1 - m2 - m6  (+ 4*C1)
    wire [10*136-1:0] t_y3 = {
        136'(4) * C1, 136'(c3), pm[5], pm[9],
        pm[7], pm[7] << 1,
        nm[0], nm[1], nm[2], nm[6]
    };
    qsag_sum_csa #(.W(136), .N(10), .CHUNK(CHUNK)) u_y3 (.x(t_y3), .y(acc_d[3]));

    // y4 = c4 + m0 + m1 + m2 + m6 + m7 + m11 - m3 - m8 - m9 - m10  (+ 4*C1)
    wire [12*136-1:0] t_y4 = {
        136'(4) * C1, 136'(c4),
        pm[0], pm[1], pm[2], pm[6], pm[7], pm[11],
        nm[3], nm[8], nm[9], nm[10]
    };
    qsag_sum_csa #(.W(136), .N(12), .CHUNK(CHUNK)) u_y4 (.x(t_y4), .y(acc_d[4]));

    for (genvar k = 0; k < 5; k++) begin : g_red
        always_ff @(posedge clk) acc_q[k] <= acc_d[k];
        qsag_gl64_reduce u_red (.clk(clk), .x(acc_q[k]), .r(y[64*k +: 64]));
    end
endmodule
