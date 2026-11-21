// GoldilocksExt4 multiply-accumulate y = a*b + c in F_p[v]/(v^4 - 7) (crates/qsag-agg
// GoldilocksExt4::mul_add). Limb order is qsag's quadratic tower order [c0.c0, c0.c1, c1.c0, c1.c1]
// over F_p[u]/(u^2 - 7) and F_{p^2}[v]/(v^2 - u).
//
// 9-multiply Tower Karatsuba architecture (9 x 9 = 81 DSPs on both MULT18X18D and DSP48E2):
//   Stage 0 (1 clk) : canonical modular pre-sums (a0+a1, a2+a3, a0+a2, a1+a3, a0+a1+a2+a3; same b)
//   Stages 1..3     : nine 64x64 DSP-tiled exact products m00..m22 (qsag_mul64_dsp, MUL64_LAT=3)
//   Stages 4..6     : carry-save Karatsuba recombination + canonical Goldilocks reduction
//                     (on AW<=16 ECP5: Stage 4 folds 9x128b -> 9x66b v_q < 3p, Stage 5 combines in
//                      72 bits using (2^66-1) + B66 == 5p == 0 (mod p), Stage 6 folds 72b -> 64b < p)
// Inputs must be canonical (< p); outputs are canonical (< p). Latency EXT4_MAC_LAT = 7, 1 MAC/clk.
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
    localparam logic [63:0]  GL_P      = qsag_ni_pkg::GL_P;
    localparam int           MUL64_LAT = qsag_ni_pkg::MUL64_LAT;
    localparam int           CHUNK     = (AW <= 16) ? 72 : 24;
    localparam int           CHUNK16   = (AW <= 16) ? 66 : 16;
    localparam logic [65:0]  NEG_1P66  = 66'h3_0000_0000_FFFF_FFFF; // 2^66 - GL_P
    localparam logic [66:0]  NEG_1P67  = 67'h7_0000_0000_FFFF_FFFF; // 2^67 - GL_P
    localparam logic [66:0]  NEG_2P67  = 67'h6_0000_0001_FFFF_FFFE; // 2^67 - 2*GL_P
    localparam logic [66:0]  NEG_3P67  = 67'h5_0000_0002_FFFF_FFFD; // 2^67 - 3*GL_P
    localparam logic [135:0] C1        = 136'h0000_0001_0000_0001;  // (2^128 - 1) + C1 == 0 (mod p)
    localparam logic [71:0]  B66       = 72'h00_FFFF_FFFB_0000_0006; // (2^66 - 1) + B66 == 5*GL_P == 0 (mod p)
    localparam logic [65:0]  V_BIAS    = {2'b0, GL_P} + 66'd2;

    wire [63:0] a0 = a[0   +: 64], a1 = a[64  +: 64], a2 = a[128 +: 64], a3 = a[192 +: 64];
    wire [63:0] b0 = b[0   +: 64], b1 = b[64  +: 64], b2 = b[128 +: 64], b3 = b[192 +: 64];

    // Stage 0: eight 2-operand canonical modular sums + two 4-operand canonical modular sums.
    wire [7:0][63:0] p2_lhs = {b1, b0, b2, b0, a1, a0, a2, a0};
    wire [7:0][63:0] p2_rhs = {b3, b2, b3, b1, a3, a2, a3, a1};
    logic [7:0][63:0] p2_sum;
    for (genvar i = 0; i < 8; i++) begin : g_add2
        /* verilator lint_off UNUSEDSIGNAL */
        logic [64:0] s0;
        logic [65:0] s1;
        /* verilator lint_on UNUSEDSIGNAL */
        if (AW <= 16) begin : g_a2_ecp5
            assign s0 = {1'b0, p2_lhs[i]} + {1'b0, p2_rhs[i]};
            assign s1 = {1'b0, s0} + NEG_1P66;
        end else begin : g_a2_wide
            qsag_add_split #(.W(65), .CHUNK(CHUNK16)) u_s0 (
                .a({1'b0, p2_lhs[i]}), .b({1'b0, p2_rhs[i]}), .y(s0));
            qsag_sum_csa #(.W(66), .N(3), .CHUNK(CHUNK16)) u_s1 (
                .x({NEG_1P66, {2'b0, p2_rhs[i]}, {2'b0, p2_lhs[i]}}), .y(s1));
        end
        assign p2_sum[i] = !s1[65] ? s1[63:0] : s0[63:0];
    end

    wire  [1:0][63:0]  q4_lhs = {p2_sum[4], p2_sum[0]};
    wire  [1:0][63:0]  q4_rhs = {p2_sum[5], p2_sum[1]};
    wire  [1:0][255:0] p4_in  = {b, a};
    logic [1:0][63:0]  p4_sum;
    if (AW <= 16) begin : g_add4_ecp5
        // Reuse canonical p2_sum[0]=(a0+a1)%p, p2_sum[1]=(a2+a3)%p and p2_sum[4..5].
        for (genvar i = 0; i < 2; i++) begin : g_q2
            /* verilator lint_off UNUSEDSIGNAL */
            logic [64:0] s0;
            logic [65:0] s1;
            /* verilator lint_on UNUSEDSIGNAL */
            assign s0 = {1'b0, q4_lhs[i]} + {1'b0, q4_rhs[i]};
            assign s1 = {1'b0, s0} + NEG_1P66;
            assign p4_sum[i] = !s1[65] ? s1[63:0] : s0[63:0];
        end
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_p4in = &{1'b0, p4_in};
        /* verilator lint_on UNUSEDSIGNAL */
    end else begin : g_add4_wide
        for (genvar i = 0; i < 2; i++) begin : g_add4
            wire [63:0] x0 = p4_in[i][0   +: 64], x1 = p4_in[i][64  +: 64];
            wire [63:0] x2 = p4_in[i][128 +: 64], x3 = p4_in[i][192 +: 64];
            wire [4*67-1:0] base = {{3'b0, x3}, {3'b0, x2}, {3'b0, x1}, {3'b0, x0}};
            /* verilator lint_off UNUSEDSIGNAL */
            logic [65:0] s0;
            logic [66:0] s1, s2, s3;
            /* verilator lint_on UNUSEDSIGNAL */
            qsag_sum_csa #(.W(66), .N(4), .CHUNK(CHUNK16)) u_s0 (
                .x({{2'b0, x3}, {2'b0, x2}, {2'b0, x1}, {2'b0, x0}}), .y(s0));
            qsag_sum_csa #(.W(67), .N(5), .CHUNK(CHUNK16)) u_s1 (.x({NEG_1P67, base}), .y(s1));
            qsag_sum_csa #(.W(67), .N(5), .CHUNK(CHUNK16)) u_s2 (.x({NEG_2P67, base}), .y(s2));
            qsag_sum_csa #(.W(67), .N(5), .CHUNK(CHUNK16)) u_s3 (.x({NEG_3P67, base}), .y(s3));
            assign p4_sum[i] = !s3[66] ? s3[63:0] : !s2[66] ? s2[63:0] : !s1[66] ? s1[63:0] : s0[63:0];
        end
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_q4 = &{1'b0, q4_lhs, q4_rhs};
        /* verilator lint_on UNUSEDSIGNAL */
    end

    logic [8:0][63:0] ma_q, mb_q;
    always_ff @(posedge clk) begin
        ma_q[0] <= a0;        mb_q[0] <= b0;
        ma_q[1] <= a1;        mb_q[1] <= b1;
        ma_q[2] <= p2_sum[0]; mb_q[2] <= p2_sum[4];
        ma_q[3] <= a2;        mb_q[3] <= b2;
        ma_q[4] <= a3;        mb_q[4] <= b3;
        ma_q[5] <= p2_sum[1]; mb_q[5] <= p2_sum[5];
        ma_q[6] <= p2_sum[2]; mb_q[6] <= p2_sum[6];
        ma_q[7] <= p2_sum[3]; mb_q[7] <= p2_sum[7];
        ma_q[8] <= p4_sum[0]; mb_q[8] <= p4_sum[1];
    end

    // Stages 1..3: 9 x 64x64 DSP multipliers (m00, m01, m02, m10, m11, m12, m20, m21, m22).
    logic [8:0][127:0] m;
    for (genvar i = 0; i < 9; i++) begin : g_mul
        qsag_mul64_dsp #(.AW(AW), .BW(BW)) u_mul (
            .clk(clk), .a(ma_q[i]), .b(mb_q[i]), .p(m[i]));
    end

    // Module-scope arrays for Yosys Verilog-2005 frontend compatibility.
    logic [8:0][65:0]  v_d, v_q;
    logic [8:0][71:0]  pv;
    logic [7:0][71:0]  nv;
    logic [67:0]       s0_68, s2_68;
    logic [3:0][71:0]  acc72_d, acc72_q;
    logic [8:0][135:0] pm;
    logic [7:0][135:0] nm;
    logic [3:0][135:0] acc_d, acc_q;

    if (AW <= 16) begin : g_ecp5_post
        // Stage 4 (1 clk): fold each 128-bit product m[i] = {h32, mid32, lo64} into 66-bit v_q[i] in (0, 3p).
        localparam int C_DLY5 = 2 + MUL64_LAT; // 5 clocks to align with v_q[0..8]
        for (genvar i = 0; i < 9; i++) begin : g_vf
            wire [63:0] lo  = m[i][63:0];
            wire [31:0] mid = m[i][95:64];
            wire [31:0] hi  = m[i][127:96];
            wire [5*66-1:0] v_terms = {
                V_BIAS,
                ~{34'b0, hi},
                ~{34'b0, mid},
                {2'b0, mid, 32'b0},
                {2'b0, lo}
            };
            qsag_sum_csa #(.W(66), .N(5), .CHUNK(66)) u_vf (.x(v_terms), .y(v_d[i]));
            always_ff @(posedge clk) v_q[i] <= v_d[i];
        end

        logic [C_DLY5*256-1:0] c_sr;
        always_ff @(posedge clk) c_sr <= {c_sr[(C_DLY5-1)*256-1:0], c};
        wire [63:0] c0 = c_sr[(C_DLY5-1)*256 + 0   +: 64];
        wire [63:0] c1 = c_sr[(C_DLY5-1)*256 + 64  +: 64];
        wire [63:0] c2 = c_sr[(C_DLY5-1)*256 + 128 +: 64];
        wire [63:0] c3 = c_sr[(C_DLY5-1)*256 + 192 +: 64];

        // Stage 5 (1 clk): factored 72-bit carry-save Karatsuba recombination (< 113 * 2^64 < 2^71).
        for (genvar i = 0; i < 9; i++) begin : g_pv
            assign pv[i] = {6'd0,  v_q[i]};
        end
        for (genvar i = 0; i < 8; i++) begin : g_nv
            assign nv[i] = {6'd0, ~v_q[i]};
        end

        // Factor 7*(pv[1] + pv[5] + nv[3] + nv[4]) = 8*s0_68 - s0_68
        qsag_sum_csa #(.W(68), .N(4), .CHUNK(68)) u_s0_68 (
            .x({{2'b0, ~v_q[4]}, {2'b0, ~v_q[3]}, {2'b0, v_q[5]}, {2'b0, v_q[1]}}),
            .y(s0_68));
        wire [5*72-1:0] t_y0 = {
            72'(14) * B66 + 72'd1, 72'(c0), pv[0],
            {1'b0, s0_68, 3'b0}, ~{4'b0, s0_68}
        };
        qsag_sum_csa #(.W(72), .N(5), .CHUNK(72)) u_y0 (.x(t_y0), .y(acc72_d[0]));

        wire [8*72-1:0] t_y1 = {
            72'(2) * B66 + 72'd1, 72'(c1), pv[2], pv[3],
            pv[4] << 3, nv[4],
            nv[0], nv[1]
        };
        qsag_sum_csa #(.W(72), .N(8), .CHUNK(72)) u_y1 (.x(t_y1), .y(acc72_d[1]));

        // Factor 7*(pv[7] + nv[1] + nv[4]) = 8*s2_68 - s2_68
        qsag_sum_csa #(.W(68), .N(3), .CHUNK(68)) u_s2_68 (
            .x({{2'b0, ~v_q[4]}, {2'b0, ~v_q[1]}, {2'b0, v_q[7]}}),
            .y(s2_68));
        wire [7*72-1:0] t_y2 = {
            72'(16) * B66 + 72'd1, 72'(c2), pv[6],
            nv[0], nv[3],
            {1'b0, s2_68, 3'b0}, ~{4'b0, s2_68}
        };
        qsag_sum_csa #(.W(72), .N(7), .CHUNK(72)) u_y2 (.x(t_y2), .y(acc72_d[2]));

        wire [11*72-1:0] t_y3 = {
            72'(4) * B66, 72'(c3),
            pv[8], pv[0], pv[1], pv[3], pv[4],
            nv[6], nv[7], nv[2], nv[5]
        };
        qsag_sum_csa #(.W(72), .N(11), .CHUNK(72)) u_y3 (.x(t_y3), .y(acc72_d[3]));

        // Stage 6 (1 clk): canonicalize 72-bit acc72_q = {m8, lo64} via V = lo64 + m8*(2^32 - 1) in [0, 2p).
        for (genvar k = 0; k < 4; k++) begin : g_red72
            always_ff @(posedge clk) acc72_q[k] <= acc72_d[k];
            wire [63:0] lo64 = acc72_q[k][63:0];
            wire [7:0]  m8   = acc72_q[k][71:64];
            wire [39:0] m8_f = (m8 == 8'd0) ? 40'd0 : {m8 - 8'd1, 24'hFF_FFFF, 8'd0 - m8};
            /* verilator lint_off UNUSEDSIGNAL */
            wire [64:0] r0 = {1'b0, lo64} + {25'd0, m8_f};
            wire [65:0] r1 = {1'b0, r0}   + NEG_1P66;
            /* verilator lint_on UNUSEDSIGNAL */
            always_ff @(posedge clk) y[64*k +: 64] <= !r1[65] ? r1[63:0] : r0[63:0];
        end
        assign pm    = '0;
        assign nm    = '0;
        assign acc_d = '0;
        assign acc_q = '0;
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_wide = &{1'b0, pm, nm, acc_d, acc_q, pv[5], pv[7]};
        /* verilator lint_on UNUSEDSIGNAL */
    end else begin : g_wide_post
        localparam int C_DLY = 1 + MUL64_LAT; // 4 clocks to align with m[0..8]
        logic [C_DLY*256-1:0] c_sr;
        always_ff @(posedge clk) c_sr <= {c_sr[(C_DLY-1)*256-1:0], c};
        wire [63:0] c0 = c_sr[(C_DLY-1)*256 + 0   +: 64];
        wire [63:0] c1 = c_sr[(C_DLY-1)*256 + 64  +: 64];
        wire [63:0] c2 = c_sr[(C_DLY-1)*256 + 128 +: 64];
        wire [63:0] c3 = c_sr[(C_DLY-1)*256 + 192 +: 64];

        for (genvar i = 0; i < 9; i++) begin : g_pm
            assign pm[i] = {8'd0,  m[i]};
        end
        for (genvar i = 0; i < 8; i++) begin : g_nm
            assign nm[i] = {8'd0, ~m[i]};
        end

        wire [15*136-1:0] t_y0 = {
            136'(14) * C1, 136'(c0), pm[0],
            pm[1], pm[1] << 1, pm[1] << 2,
            pm[5], pm[5] << 1, pm[5] << 2,
            nm[3], nm[3] << 1, nm[3] << 2,
            nm[4], nm[4] << 1, nm[4] << 2
        };
        qsag_sum_csa #(.W(136), .N(15), .CHUNK(CHUNK)) u_y0 (.x(t_y0), .y(acc_d[0]));

        wire [9*136-1:0] t_y1 = {
            136'(2) * C1, 136'(c1), pm[2], pm[3],
            pm[4], pm[4] << 1, pm[4] << 2,
            nm[0], nm[1]
        };
        qsag_sum_csa #(.W(136), .N(9), .CHUNK(CHUNK)) u_y1 (.x(t_y1), .y(acc_d[1]));

        wire [14*136-1:0] t_y2 = {
            136'(16) * C1, 136'(c2), pm[6],
            pm[7], pm[7] << 1, pm[7] << 2,
            nm[0],
            nm[1], nm[1] << 1, nm[1] << 2,
            nm[3],
            nm[4], nm[4] << 1, nm[4] << 2
        };
        qsag_sum_csa #(.W(136), .N(14), .CHUNK(CHUNK)) u_y2 (.x(t_y2), .y(acc_d[2]));

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
        assign v_d     = '0;
        assign v_q     = '0;
        assign pv      = '0;
        assign nv      = '0;
        assign s0_68   = '0;
        assign s2_68   = '0;
        assign acc72_d = '0;
        assign acc72_q = '0;
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_ecp5 = &{1'b0, v_d, v_q, pv, nv, s0_68, s2_68, acc72_d, acc72_q};
        /* verilator lint_on UNUSEDSIGNAL */
    end
endmodule
