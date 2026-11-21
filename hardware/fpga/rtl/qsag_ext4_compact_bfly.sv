// Pipelined single-multiplier 9-Mul Tower Karatsuba Ext4 MAC and in-place BRAM fold for ECP5_COMPACT.
// Instantiates ONE dedicated pipelined 9-DSP Goldilocks multiplier (`qsag_gl64_dsp_mul`: 9 MULT18X18D),
// streaming only 9 Tower Karatsuba products over F_p[u]/(u^2 - 7) and F_{p^2}[v]/(v^2 - u) instead
// of 16 schoolbook products (17 clocks per Ext4 MAC vs 24 clocks, 9 DSPs vs 16 DSPs).
//
// While steps 0..3 stream the four diagonal products (a0*b0, a1*b1, a2*b2, a3*b3), ONE shared pair
// of 64-bit modular adders computes the five Karatsuba pre-sums (0+1, 2+3, 0+2, 1+3, all) for a and b
// on the fly with zero extra cycles!
module qsag_ext4_compact_bfly #(
    parameter int TAW = 11,
    parameter int AW  = 16,
    parameter int BW  = 16
) (
    input  logic           clk,
    input  logic           rst,
    input  logic           tw_en,
    input  logic [TAW-1:0] tw_idx,
    input  logic [255:0]   tw_data,
    input  logic           fold_start,
    input  logic [5:0]     fold_log2n,
    input  logic [255:0]   fold_r,
    output logic           fold_busy,
    output logic           fold_done,
    output logic [255:0]   fold_res,
    input  logic           mac_valid,
    input  logic [255:0]   mac_a,
    input  logic [255:0]   mac_b,
    input  logic [255:0]   mac_c,
    output logic           mac_done,
    output logic [255:0]   mac_y
);
    localparam logic [63:0]  GL_P     = qsag_ni_pkg::GL_P;
    localparam int           ML       = qsag_ni_pkg::GL_MUL_LAT; // 5
    localparam int           CHUNK22  = (AW <= 16) ? 34 : 22;
    localparam int           CHUNK24  = (AW <= 16) ? 36 : 24;
    localparam logic [65:0]  NEG_1P66 = 66'h3_0000_0000_FFFF_FFFF;
    // ~x + C64_72 == (2^64 - 1 - x) + (2*p - (2^64 - 1)) == 2*p - x == -x (mod p).
    localparam logic [71:0] C64_72   = 72'h00_FFFF_FFFE_0000_0003;

    typedef enum logic [2:0] {IDLE, RD_WAIT, RD_REG, SUB_REG, STREAM_MAC, WRITE} state_t;
    state_t st;

    logic [TAW-2:0]   pair_idx, last_pair;
    logic [255:0]     a_q, b_q, c_q, r_q, ev_rd, od_rd, ev_q, od_q;
    logic [4:0]       step;
    logic [63:0]      sa_01, sa_23, sa_02, sa_13, sb_01, sb_23, sb_02, sb_13;
    logic [8:0][63:0] m_q;
    logic [63:0]      mul_r, red_r;
    logic [71:0]      red_in_q;

    wire [63:0] a0 = a_q[0   +: 64], a1 = a_q[64  +: 64], a2 = a_q[128 +: 64], a3 = a_q[192 +: 64];
    wire [63:0] b0 = b_q[0   +: 64], b1 = b_q[64  +: 64], b2 = b_q[128 +: 64], b3 = b_q[192 +: 64];
    wire [63:0] c0 = c_q[0   +: 64], c1 = c_q[64  +: 64], c2 = c_q[128 +: 64], c3 = c_q[192 +: 64];

    // One shared modular pre-adder pair computing Karatsuba sums during steps 0..4:
    //   step 0: sa_01 <= a0+a1, sb_01 <= b0+b1
    //   step 1: sa_23 <= a2+a3, sb_23 <= b2+b3
    //   step 2: sa_02 <= a0+a2, sb_02 <= b0+b2
    //   step 3: sa_13 <= a1+a3, sb_13 <= b1+b3
    //   step 4: used directly as (sa_01+sa_23), (sb_01+sb_23) on step 8 (latched in sa_02/sb_02 after step 6!)
    logic [63:0] add_al, add_ar, add_bl, add_br, add_ay, add_by;
    always_comb begin
        case (step[2:0])
            3'd0:    begin add_al = a0;    add_ar = a1;    add_bl = b0;    add_br = b1;    end
            3'd1:    begin add_al = a2;    add_ar = a3;    add_bl = b2;    add_br = b3;    end
            3'd2:    begin add_al = a0;    add_ar = a2;    add_bl = b0;    add_br = b2;    end
            3'd3:    begin add_al = a1;    add_ar = a3;    add_bl = b1;    add_br = b3;    end
            default: begin add_al = sa_01; add_ar = sa_23; add_bl = sb_01; add_br = sb_23; end
        endcase
    end
    for (genvar g = 0; g < 2; g++) begin : g_pre_add
        wire [63:0] lhs = (g == 0) ? add_al : add_bl;
        wire [63:0] rhs = (g == 0) ? add_ar : add_br;
        /* verilator lint_off UNUSEDSIGNAL */
        logic [64:0] s0;
        logic [65:0] s1;
        /* verilator lint_on UNUSEDSIGNAL */
        qsag_add_split #(.W(65), .CHUNK(CHUNK22)) u_s0 (.a({1'b0, lhs}), .b({1'b0, rhs}), .y(s0));
        qsag_sum_csa #(.W(66), .N(3), .CHUNK(CHUNK22)) u_s1 (
            .x({NEG_1P66, {2'b0, rhs}, {2'b0, lhs}}), .y(s1));
        if (g == 0) begin : g_ay
            assign add_ay = !s1[65] ? s1[63:0] : s0[63:0];
        end else begin : g_by
            assign add_by = !s1[65] ? s1[63:0] : s0[63:0];
        end
    end

    // Multiplier issue schedule across steps 0..8 (matching qsag_ext4_mac index order m[0..8]):
    //   0: a0*b0 (m0), 1: a1*b1 (m1), 2: a2*b2 (m3), 3: a3*b3 (m4),
    //   4: sa_01*sb_01 (m2), 5: sa_23*sb_23 (m5), 6: sa_02*sb_02 (m6),
    //   7: sa_13*sb_13 (m7), 8: sa_all*sb_all (m8, held in sa_01/sb_01 after step 4!).
    logic [63:0] mul_a_in, mul_b_in;
    always_comb begin
        case (step[3:0])
            4'd0:    begin mul_a_in = a0;    mul_b_in = b0;    end
            4'd1:    begin mul_a_in = a1;    mul_b_in = b1;    end
            4'd2:    begin mul_a_in = a2;    mul_b_in = b2;    end
            4'd3:    begin mul_a_in = a3;    mul_b_in = b3;    end
            4'd4:    begin mul_a_in = sa_01; mul_b_in = sb_01; end
            4'd5:    begin mul_a_in = sa_23; mul_b_in = sb_23; end
            4'd6:    begin mul_a_in = sa_02; mul_b_in = sb_02; end
            4'd7:    begin mul_a_in = sa_13; mul_b_in = sb_13; end
            default: begin mul_a_in = sa_01; mul_b_in = sb_01; end
        endcase
    end

    qsag_gl64_dsp_mul #(.AW(AW), .BW(BW)) u_mul (
        .clk(clk), .a(mul_a_in), .b(mul_b_in), .r(mul_r));

    // Products arrive at step = ML + 0..8:
    //   step ML+0 -> m[0], ML+1 -> m[1], ML+2 -> m[3], ML+3 -> m[4],
    //   ML+4 -> m[2], ML+5 -> m[5] (ready to emit limb 0 & 1!),
    //   ML+6 -> m[6], ML+7 -> m[7] (ready to emit limb 2!),
    //   ML+8 -> m[8] (ready to emit limb 3!).
    // Using ~x = (2^64 - 1) - x and (2^64 - 1) + 2^32 == GL_P == 0 (mod p), every 72-bit Karatsuba
    // limb combination fits in (0, 2^70) and streams into `qsag_gl64_reduce` on steps ML+5..ML+8!
    wire [71:0] p0 = {8'd0, m_q[0]}, p1 = {8'd0, m_q[1]}, p2 = {8'd0, m_q[2]};
    wire [71:0] p3 = {8'd0, m_q[3]}, p4 = {8'd0, m_q[4]}, p6 = {8'd0, m_q[6]};
    wire [71:0] n0 = {8'd0, ~m_q[0]}, n1 = {8'd0, ~m_q[1]}, n2 = {8'd0, ~m_q[2]};
    wire [71:0] n3 = {8'd0, ~m_q[3]}, n4 = {8'd0, ~m_q[4]}, n5 = {8'd0, ~m_q[5]};
    wire [71:0] n6 = {8'd0, ~m_q[6]}, n7 = {8'd0, ~m_q[7]};
    wire [71:0] cur_m = {8'd0, mul_r};

    // Streamed 15-term 72-bit CSA shared across the 4 output limbs on steps ML+5, ML+6, ML+7, ML+8:
    //   step ML+5 (`mul_r` == m5): y0 = c0 + m0 + 7*m1 + 7*m5 - 7*m3 - 7*m4 (+ 14*C64)
    //   step ML+6 (`mul_r` == m6): y1 = c1 + m2 + m3 + 7*m4 - m0 - m1 (+ 2*C64)
    //   step ML+7 (`mul_r` == m7): y2 = c2 + m6 + 7*m7 - m0 - 7*m1 - m3 - 7*m4 (+ 16*C64)
    //   step ML+8 (`mul_r` == m8): y3 = c3 + m8 + m0 + m1 + m3 + m4 - m6 - m7 - m2 - m5 (+ 4*C64)
    logic [15*72-1:0] limb_terms;
    always_comb begin
        case (step - 5'(ML + 5))
            5'd0: limb_terms = {
                72'(14) * C64_72, {8'd0, c0}, p0,
                p1, p1 << 1, p1 << 2,
                cur_m, cur_m << 1, cur_m << 2,
                n3, n3 << 1, n3 << 2,
                n4, n4 << 1, n4 << 2
            };
            5'd1: limb_terms = {
                72'(2) * C64_72, {8'd0, c1}, p2, p3,
                p4, p4 << 1, p4 << 2,
                n0, n1,
                72'd0, 72'd0, 72'd0, 72'd0, 72'd0, 72'd0
            };
            5'd2: limb_terms = {
                72'(16) * C64_72, {8'd0, c2}, p6,
                cur_m, cur_m << 1, cur_m << 2,
                n0,
                n1, n1 << 1, n1 << 2,
                n3,
                n4, n4 << 1, n4 << 2,
                72'd0
            };
            default: limb_terms = {
                72'(4) * C64_72, {8'd0, c3},
                cur_m, p0, p1, p3, p4,
                n6, n7, n2, n5,
                72'd0, 72'd0, 72'd0, 72'd0
            };
        endcase
    end
    logic [71:0] limb_acc;
    qsag_sum_csa #(.W(72), .N(15), .CHUNK(CHUNK24)) u_comb (.x(limb_terms), .y(limb_acc));

    // `red_in_q` latches `limb_acc` at steps ML+5..ML+8; `red_r` arrives 2 clocks later at ML+8..ML+11.
    qsag_gl64_reduce u_red (.clk(clk), .x({64'd0, red_in_q}), .r(red_r));
    wire [4:0] red_idx = step - 5'(ML + 8);

    wire           we_int = (st == WRITE);
    wire [TAW-1:0] wr_idx = we_int ? {1'b0, pair_idx} : tw_idx;
    wire [255:0]   wr_dat = we_int ? mac_y : tw_data;

    qsag_sdp_bram #(.AW(TAW-1), .DW(256)) u_ev (
        .clk(clk), .we((we_int || tw_en) && !wr_idx[0]),
        .wa(wr_idx[TAW-1:1]), .wd(wr_dat), .ra(pair_idx), .rd(ev_rd));
    qsag_sdp_bram #(.AW(TAW-1), .DW(256)) u_od (
        .clk(clk), .we((we_int || tw_en) &&  wr_idx[0]),
        .wa(wr_idx[TAW-1:1]), .wd(wr_dat), .ra(pair_idx), .rd(od_rd));

    logic [255:0] diff_d;
    for (genvar n = 0; n < 4; n++) begin : g_sub
        wire [63:0] od_n = od_q[64*n +: 64];
        wire [63:0] ev_n = ev_q[64*n +: 64];
        /* verilator lint_off UNUSEDSIGNAL */
        logic [64:0] dr, dp;
        /* verilator lint_on UNUSEDSIGNAL */
        qsag_sum_csa #(.W(65), .N(3), .CHUNK(CHUNK24)) u_dr (
            .x({65'd1, ~{1'b0, ev_n}, {1'b0, od_n}}), .y(dr));
        qsag_sum_csa #(.W(65), .N(3), .CHUNK(CHUNK24)) u_dp (
            .x({{1'b0, GL_P} + 65'd1, ~{1'b0, ev_n}, {1'b0, od_n}}), .y(dp));
        assign diff_d[64*n +: 64] = dr[64] ? dp[63:0] : dr[63:0];
    end

    always_ff @(posedge clk) begin
        fold_done <= 1'b0;
        mac_done  <= 1'b0;
        if (rst) begin
            st        <= IDLE;
            fold_busy <= 1'b0;
        end else begin
            case (st)
                IDLE: begin
                    if (fold_start) begin
                        fold_busy <= 1'b1;
                        pair_idx  <= '0;
                        last_pair <= (TAW-1)'((64'd1 << (fold_log2n - 6'd1)) - 64'd1);
                        r_q       <= fold_r;
                        st        <= RD_WAIT;
                    end else if (mac_valid) begin
                        a_q  <= mac_a;
                        b_q  <= mac_b;
                        c_q  <= mac_c;
                        step <= 5'd0;
                        st   <= STREAM_MAC;
                    end
                end
                RD_WAIT: st <= RD_REG;
                RD_REG: begin
                    ev_q <= ev_rd;
                    od_q <= od_rd;
                    st   <= SUB_REG;
                end
                SUB_REG: begin
                    a_q  <= r_q;
                    b_q  <= diff_d;
                    c_q  <= ev_q;
                    step <= 5'd0;
                    st   <= STREAM_MAC;
                end
                STREAM_MAC: begin
                    case (step)
                        5'd0: begin sa_01 <= add_ay; sb_01 <= add_by; end
                        5'd1: begin sa_23 <= add_ay; sb_23 <= add_by; end
                        5'd2: begin sa_02 <= add_ay; sb_02 <= add_by; end
                        5'd3: begin sa_13 <= add_ay; sb_13 <= add_by; end
                        5'd4: begin sa_01 <= add_ay; sb_01 <= add_by; end // holds sa_all, sb_all for step 8
                        default: ;
                    endcase

                    case (step)
                        5'(ML + 0): m_q[0] <= mul_r;
                        5'(ML + 1): m_q[1] <= mul_r;
                        5'(ML + 2): m_q[3] <= mul_r;
                        5'(ML + 3): m_q[4] <= mul_r;
                        5'(ML + 4): m_q[2] <= mul_r;
                        5'(ML + 5): begin m_q[5] <= mul_r; red_in_q <= limb_acc; end
                        5'(ML + 6): begin m_q[6] <= mul_r; red_in_q <= limb_acc; end
                        5'(ML + 7): begin m_q[7] <= mul_r; red_in_q <= limb_acc; end
                        5'(ML + 8): begin m_q[8] <= mul_r; red_in_q <= limb_acc; end
                        default: ;
                    endcase

                    if (step >= 5'(ML + 8) && step <= 5'(ML + 11)) begin
                        mac_y[64*red_idx[1:0] +: 64] <= red_r;
                    end

                    if (step == 5'(ML + 11)) begin
                        if (fold_busy) begin
                            st <= WRITE;
                        end else begin
                            mac_done <= 1'b1;
                            st       <= IDLE;
                        end
                    end else begin
                        step <= step + 5'd1;
                    end
                end
                WRITE: begin
                    fold_res <= mac_y;
                    if (pair_idx == last_pair) begin
                        fold_busy <= 1'b0;
                        fold_done <= 1'b1;
                        st        <= IDLE;
                    end else begin
                        pair_idx <= pair_idx + (TAW-1)'(1);
                        st       <= RD_WAIT;
                    end
                end
                default: st <= IDLE;
            endcase
        end
    end

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_ok = &{1'b0, m_q[8], red_idx[4:2]};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
