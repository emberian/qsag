// Poseidon2 width-12 linear layers with zero multipliers, carry-save compression, and one
// lazy reduction per lane.
//
//   M_E = M4 (x) P3 : M4 on the lane triples (0,3,6,9), (1,4,7,10), (2,5,8,11), then every
//                     contiguous triple gets its own sum added (crates/qsag-accel poseidon2_apply_me).
//   M_I = J + diag(-64, 1, 2, 4, ..., 1024).
//
// Both linear layers stay in carry-save (s, c) form through the M_E/M_I mux and addend merge,
// propagating only ONE 76-bit split carry-select adder in Stage 1 and parallel speculative
// modular reduction in Stage 2. Latency P2_LIN_LAT = 2, depth <= 17 LUT+CARRY4 levels.
// FIXED = 0 builds M_E only, FIXED = 1 builds M_I only, FIXED = -1 selects per cycle with `mi`.
module qsag_p2_linear #(
    parameter int FIXED = -1
) (
    input  logic             clk,
    input  logic [767:0]     x,
    input  logic             mi,
    input  logic [12*67-1:0] addend,
    output logic [767:0]     y
);
    localparam logic [63:0] GL_P   = qsag_ni_pkg::GL_P;
    localparam int          LW     = 76;
    // -64*x0 = 64*(2p - x0) = 64*(2p - (2^64 - 1 - ~x0)) = 64*(~x0) + 64*(2p - 2^64 + 1)
    // Since 2p - 2^64 + 1 = 2^64 - 2^33 + 3:
    localparam logic [LW-1:0] MI0_BIAS = LW'(128'(2) * 128'(GL_P) - (128'd1 << 64) + 128'd1) << 6;
    localparam logic [65:0]   NEG_1P66 = 66'h3_0000_0000_FFFF_FFFF; // 2^66 - GL_P

    logic unused_ok;
    assign unused_ok = &{1'b0, mi};

    logic [12*LW-1:0] sel_s, sel_c;

    if (FIXED != 1) begin : g_me
        logic [12*LW-1:0] me_s, me_c;
        // m4_s, m4_c: row k of M4 on column c in 67-bit carry-save form (zero carry chains!).
        // Row 0 = 2*b0 + 3*b1 + b2 + b3 = (b0<<1) + (b1<<1) + b1 + b2 + b3 (5 terms), cyclic.
        logic [12*67-1:0] m4_s, m4_c;
        for (genvar c = 0; c < 3; c++) begin : g_col
            wire [66:0] b [4];
            assign b[0] = 67'(x[64*(c)     +: 64]);
            assign b[1] = 67'(x[64*(c + 3) +: 64]);
            assign b[2] = 67'(x[64*(c + 6) +: 64]);
            assign b[3] = 67'(x[64*(c + 9) +: 64]);
            for (genvar k = 0; k < 4; k++) begin : g_m4
                wire [5*67-1:0] t5 = {
                    b[(k + 3) % 4],
                    b[(k + 2) % 4],
                    b[(k + 1) % 4],
                    b[(k + 1) % 4] << 1,
                    b[k] << 1
                };
                qsag_csa_reduce2 #(.W(67), .N(5)) u_m4_csa (
                    .x(t5), .s(m4_s[67*(4*c + k) +: 67]), .c(m4_c[67*(4*c + k) +: 67]));
            end
        end
        // me[3*k + c] + addend = 2*m4[c,k] + m4[c1,k] + m4[c2,k] + addend (7 vectors -> 2 vectors).
        for (genvar k = 0; k < 4; k++) begin : g_row
            for (genvar c = 0; c < 3; c++) begin : g_out
                localparam int C1 = (c + 1) % 3;
                localparam int C2 = (c + 2) % 3;
                wire [7*LW-1:0] t7 = {
                    LW'(addend[67*(3*k + c) +: 67]),
                    LW'(m4_c[67*(4*C2 + k) +: 67]),
                    LW'(m4_s[67*(4*C2 + k) +: 67]),
                    LW'(m4_c[67*(4*C1 + k) +: 67]),
                    LW'(m4_s[67*(4*C1 + k) +: 67]),
                    LW'(m4_c[67*(4*c + k) +: 67]) << 1,
                    LW'(m4_s[67*(4*c + k) +: 67]) << 1
                };
                qsag_csa_reduce2 #(.W(LW), .N(7)) u_me_csa (
                    .x(t7), .s(me_s[LW*(3*k + c) +: LW]), .c(me_c[LW*(3*k + c) +: LW]));
            end
        end
    end

    if (FIXED != 0) begin : g_mi
        logic [12*LW-1:0] mi_s, mi_c;
        logic [12*LW-1:0] x_ext;
        logic [LW-1:0]    sum_s, sum_c;
        for (genvar i = 0; i < 12; i++) begin : g_xext
            assign x_ext[LW*i +: LW] = LW'(x[64*i +: 64]);
        end
        qsag_csa_reduce2 #(.W(LW), .N(12)) u_sum12 (.x(x_ext), .s(sum_s), .c(sum_c));

        // Lane 0: sum + 64*(~x0) + MI0_BIAS + addend[0] (5 vectors -> 2 vectors).
        wire [5*LW-1:0] t0 = {
            LW'(addend[0 +: 67]),
            MI0_BIAS,
            LW'(~x[63:0]) << 6,
            sum_c,
            sum_s
        };
        qsag_csa_reduce2 #(.W(LW), .N(5)) u_mi0 (
            .x(t0), .s(mi_s[0 +: LW]), .c(mi_c[0 +: LW]));

        // Lanes 1..11: sum + (x[i] << shift) + addend[i] (4 vectors -> 2 vectors).
        for (genvar i = 1; i < 12; i++) begin : g_lane
            localparam int SH = (i == 1) ? 0 : (i - 1);
            wire [4*LW-1:0] ti = {
                LW'(addend[67*i +: 67]),
                LW'(x[64*i +: 64]) << SH,
                sum_c,
                sum_s
            };
            qsag_csa_reduce2 #(.W(LW), .N(4)) u_mii (
                .x(ti), .s(mi_s[LW*i +: LW]), .c(mi_c[LW*i +: LW]));
        end
    end

    if (FIXED == 0) begin : g_sel_me
        assign sel_s = g_me.me_s;
        assign sel_c = g_me.me_c;
    end else if (FIXED == 1) begin : g_sel_mi
        assign sel_s = g_mi.mi_s;
        assign sel_c = g_mi.mi_c;
    end else begin : g_sel_dy
        assign sel_s = mi ? g_mi.mi_s : g_me.me_s;
        assign sel_c = mi ? g_mi.mi_c : g_me.me_c;
    end

    logic [12*LW-1:0] lazy_q;
    for (genvar i = 0; i < 12; i++) begin : g_red
        logic [LW-1:0] lazy_d;
        qsag_add_split #(.W(LW), .CHUNK(20)) u_add1 (
            .a(sel_s[LW*i +: LW]), .b(sel_c[LW*i +: LW]), .y(lazy_d));
        always_ff @(posedge clk) lazy_q[LW*i +: LW] <= lazy_d;

        // Stage 2: r = lo + (t << 32) - t, and rm = r - GL_P, evaluated in parallel!
        // Note: r >= 0 always (if t == 0, lo >= 0; if t >= 1, (t<<32) - t > 0).
        // In Z / 2^66 Z: -t = ~{54'b0, t} + 1 = {54'h3F_FFFF_FFFF_FFFF, ~t} + 1.
        // And -t - GL_P = ~{54'b0, t} + 1 + NEG_1P66.
        logic [63:0] lo;
        logic [11:0] t;
        assign {t, lo} = lazy_q[LW*i +: LW];

        /* verilator lint_off UNUSEDSIGNAL */
        logic [65:0] r, rm;
        /* verilator lint_on UNUSEDSIGNAL */
        wire [4*66-1:0] tr0 = {66'd1, ~{54'b0, t}, {22'b0, t, 32'b0}, {2'b0, lo}};
        wire [4*66-1:0] tr1 = {NEG_1P66 + 66'd1, ~{54'b0, t}, {22'b0, t, 32'b0}, {2'b0, lo}};
        qsag_sum_csa #(.W(66), .N(4), .CHUNK(16)) u_r0 (.x(tr0), .y(r));
        qsag_sum_csa #(.W(66), .N(4), .CHUNK(16)) u_r1 (.x(tr1), .y(rm));
        always_ff @(posedge clk) y[64*i +: 64] <= rm[65] ? r[63:0] : rm[63:0];
    end
endmodule
