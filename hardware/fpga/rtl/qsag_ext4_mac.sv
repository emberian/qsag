// GoldilocksExt4 multiply-accumulate y = a*b + c in F_p[v]/(v^4 - 7) (crates/qsag-agg
// GoldilocksExt4::mul_add). Limb order is qsag's quadratic tower order [c0.c0, c0.c1, c1.c0, c1.c1]
// over F_p[u]/(u^2 - 7) and F_{p^2}[v]/(v^2 - u).
//
// 9-multiply Tower Karatsuba architecture (9 x 12 = 108 DSP48E2 vs 192 schoolbook, -44% DSPs!):
//   Stage 0 (1 clk) : canonical modular pre-sums (a0+a1, a2+a3, a0+a2, a1+a3, a0+a1+a2+a3; same b)
//   Stages 1..3     : nine 64x64 DSP-tiled exact products m00..m22 (qsag_mul64_dsp, MUL64_LAT=3)
//   Stage 4 (1 clk) : unsigned carry-save Karatsuba recombination using ~m = (2^128-1)-m and
//                     (2^128 - 1) + (2^32 + 1) == 0 (mod p), keeping every accumulator in (0, 2^133)
//   Stages 5..6     : four canonical Goldilocks reductions (qsag_gl64_reduce, RED_LAT=2)
// Inputs must be canonical (< p); outputs are canonical (< p). Latency EXT4_MAC_LAT = 7, 1 MAC/clk.
module qsag_ext4_modadd2 (
    input  logic [63:0] a,
    input  logic [63:0] b,
    output logic [63:0] y
);
    localparam logic [65:0] NEG_1P = 66'h3_0000_0000_FFFF_FFFF; // 2^66 - GL_P
    /* verilator lint_off UNUSEDSIGNAL */
    logic [64:0] s0;
    logic [65:0] s1;
    /* verilator lint_on UNUSEDSIGNAL */
    qsag_add_split #(.W(65), .CHUNK(16)) u_s0 (.a({1'b0, a}), .b({1'b0, b}), .y(s0));
    qsag_sum_csa   #(.W(66), .N(3), .CHUNK(16)) u_s1 (.x({NEG_1P, {2'b0, b}, {2'b0, a}}), .y(s1));
    assign y = !s1[65] ? s1[63:0] : s0[63:0];
endmodule

module qsag_ext4_modadd4 (
    input  logic [63:0] a0,
    input  logic [63:0] a1,
    input  logic [63:0] a2,
    input  logic [63:0] a3,
    output logic [63:0] y
);
    localparam logic [66:0] NEG_1P = 67'h7_0000_0000_FFFF_FFFF; // 2^67 - GL_P
    localparam logic [66:0] NEG_2P = 67'h6_0000_0001_FFFF_FFFE; // 2^67 - 2*GL_P
    localparam logic [66:0] NEG_3P = 67'h5_0000_0002_FFFF_FFFD; // 2^67 - 3*GL_P
    /* verilator lint_off UNUSEDSIGNAL */
    logic [65:0] s0;
    logic [66:0] s1, s2, s3;
    /* verilator lint_on UNUSEDSIGNAL */
    wire [4*67-1:0] base = {{3'b0, a3}, {3'b0, a2}, {3'b0, a1}, {3'b0, a0}};
    qsag_sum_csa #(.W(66), .N(4), .CHUNK(16)) u_s0 (.x({{2'b0, a3}, {2'b0, a2}, {2'b0, a1}, {2'b0, a0}}), .y(s0));
    qsag_sum_csa #(.W(67), .N(5), .CHUNK(16)) u_s1 (.x({NEG_1P, base}), .y(s1));
    qsag_sum_csa #(.W(67), .N(5), .CHUNK(16)) u_s2 (.x({NEG_2P, base}), .y(s2));
    qsag_sum_csa #(.W(67), .N(5), .CHUNK(16)) u_s3 (.x({NEG_3P, base}), .y(s3));
    assign y = !s3[66] ? s3[63:0] : !s2[66] ? s2[63:0] : !s1[66] ? s1[63:0] : s0[63:0];
endmodule

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
    localparam int C_DLY     = 1 + MUL64_LAT; // 4 clocks to align with m[0..8]
    localparam int CHUNK     = (AW <= 16) ? 16 : 24;
    // (2^128 - 1) + C1 == 0 (mod p), where C1 = 2^32 + 1.
    localparam logic [135:0] C1 = 136'h0000_0001_0000_0001;

    wire [63:0] a0 = a[0   +: 64], a1 = a[64  +: 64], a2 = a[128 +: 64], a3 = a[192 +: 64];
    wire [63:0] b0 = b[0   +: 64], b1 = b[64  +: 64], b2 = b[128 +: 64], b3 = b[192 +: 64];

    // Stage 0: canonical Karatsuba pre-sums (< p).
    logic [63:0] sa01_d, sa23_d, sa02_d, sa13_d, sa_all_d;
    logic [63:0] sb01_d, sb23_d, sb02_d, sb13_d, sb_all_d;
    qsag_ext4_modadd2 u_sa01 (.a(a0), .b(a1), .y(sa01_d));
    qsag_ext4_modadd2 u_sa23 (.a(a2), .b(a3), .y(sa23_d));
    qsag_ext4_modadd2 u_sa02 (.a(a0), .b(a2), .y(sa02_d));
    qsag_ext4_modadd2 u_sa13 (.a(a1), .b(a3), .y(sa13_d));
    qsag_ext4_modadd4 u_saa  (.a0(a0), .a1(a1), .a2(a2), .a3(a3), .y(sa_all_d));

    qsag_ext4_modadd2 u_sb01 (.a(b0), .b(b1), .y(sb01_d));
    qsag_ext4_modadd2 u_sb23 (.a(b2), .b(b3), .y(sb23_d));
    qsag_ext4_modadd2 u_sb02 (.a(b0), .b(b2), .y(sb02_d));
    qsag_ext4_modadd2 u_sb13 (.a(b1), .b(b3), .y(sb13_d));
    qsag_ext4_modadd4 u_sbb  (.a0(b0), .a1(b1), .a2(b2), .a3(b3), .y(sb_all_d));

    logic [8:0][63:0] ma_q, mb_q;
    always_ff @(posedge clk) begin
        ma_q[0] <= a0;       mb_q[0] <= b0;
        ma_q[1] <= a1;       mb_q[1] <= b1;
        ma_q[2] <= sa01_d;   mb_q[2] <= sb01_d;
        ma_q[3] <= a2;       mb_q[3] <= b2;
        ma_q[4] <= a3;       mb_q[4] <= b3;
        ma_q[5] <= sa23_d;   mb_q[5] <= sb23_d;
        ma_q[6] <= sa02_d;   mb_q[6] <= sb02_d;
        ma_q[7] <= sa13_d;   mb_q[7] <= sb13_d;
        ma_q[8] <= sa_all_d; mb_q[8] <= sb_all_d;
    end

    // Stages 1..3: 9 x 64x64 DSP multipliers (m00, m01, m02, m10, m11, m12, m20, m21, m22).
    logic [8:0][127:0] m;
    for (genvar i = 0; i < 9; i++) begin : g_mul
        qsag_mul64_dsp #(.AW(AW), .BW(BW)) u_mul (
            .clk(clk), .a(ma_q[i]), .b(mb_q[i]), .p(m[i]));
    end

    logic [C_DLY*256-1:0] c_sr;
    always_ff @(posedge clk) c_sr <= {c_sr[(C_DLY-1)*256-1:0], c};
    wire [63:0] c0 = c_sr[(C_DLY-1)*256 + 0   +: 64];
    wire [63:0] c1 = c_sr[(C_DLY-1)*256 + 64  +: 64];
    wire [63:0] c2 = c_sr[(C_DLY-1)*256 + 128 +: 64];
    wire [63:0] c3 = c_sr[(C_DLY-1)*256 + 192 +: 64];

    // Exact non-negative 136-bit complements: nm[i] = (2^128 - 1) - m[i].
    logic [8:0][135:0] pm, nm;
    for (genvar i = 0; i < 9; i++) begin : g_ext
        assign pm[i] = {8'd0,  m[i]};
        assign nm[i] = {8'd0, ~m[i]};
    end

    // Stage 4: carry-save recombination into four 136-bit accumulators.
    logic [3:0][135:0] acc_d, acc_q;

    // y0 = c0 + m00 + 7*m01 + 7*m12 - 7*m10 - 7*m11  (+ 14*C1)
    wire [15*136-1:0] t_y0 = {
        136'(14) * C1, 136'(c0), pm[0],
        pm[1], pm[1] << 1, pm[1] << 2,
        pm[5], pm[5] << 1, pm[5] << 2,
        nm[3], nm[3] << 1, nm[3] << 2,
        nm[4], nm[4] << 1, nm[4] << 2
    };
    qsag_sum_csa #(.W(136), .N(15), .CHUNK(CHUNK)) u_y0 (.x(t_y0), .y(acc_d[0]));

    // y1 = c1 + m02 + m10 + 7*m11 - m00 - m01  (+ 2*C1)
    wire [9*136-1:0] t_y1 = {
        136'(2) * C1, 136'(c1), pm[2], pm[3],
        pm[4], pm[4] << 1, pm[4] << 2,
        nm[0], nm[1]
    };
    qsag_sum_csa #(.W(136), .N(9), .CHUNK(CHUNK)) u_y1 (.x(t_y1), .y(acc_d[1]));

    // y2 = c2 + m20 + 7*m21 - m00 - 7*m01 - m10 - 7*m11  (+ 16*C1)
    wire [14*136-1:0] t_y2 = {
        136'(16) * C1, 136'(c2), pm[6],
        pm[7], pm[7] << 1, pm[7] << 2,
        nm[0],
        nm[1], nm[1] << 1, nm[1] << 2,
        nm[3],
        nm[4], nm[4] << 1, nm[4] << 2
    };
    qsag_sum_csa #(.W(136), .N(14), .CHUNK(CHUNK)) u_y2 (.x(t_y2), .y(acc_d[2]));

    // y3 = c3 + m22 + m00 + m01 + m10 + m11 - m20 - m21 - m02 - m12  (+ 4*C1)
    wire [11*136-1:0] t_y3 = {
        136'(4) * C1, 136'(c3),
        pm[8], pm[0], pm[1], pm[3], pm[4],
        nm[6], nm[7], nm[2], nm[5]
    };
    qsag_sum_csa #(.W(136), .N(11), .CHUNK(CHUNK)) u_y3 (.x(t_y3), .y(acc_d[3]));

    for (genvar k = 0; k < 4; k++) begin : g_red
        always_ff @(posedge clk) acc_q[k] <= acc_d[k];
        qsag_gl64_reduce u_red (.clk(clk), .x(acc_q[k]), .r(y[64*k +: 64]));
    end
endmodule
