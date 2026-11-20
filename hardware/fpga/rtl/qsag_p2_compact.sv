// Compact rotating-ring Poseidon2 width-12 core for ECP5:
//   - USE_PIPE_SBOX=0 (`ECP5_COMPACT`): ONE pipelined Goldilocks multiplier (`qsag_gl64_dsp_mul`:
//     9 MULT18X18D) reused across 4 S-box stages (`x^2, x^3, x^6, x^7`), 1,878 clks/perm;
//   - USE_PIPE_SBOX=1 (`ECP5_FULLRATE`): ONE full-rate pipelined `qsag_p2_sbox7` (`4 x 9 = 36`
//     MULT18X18D, 1 `x^7` per clock!), streaming all 12 lanes in 25 clocks on external rounds
//     and lane 0 in 13 clocks on internal rounds (1,290 clks/perm; paired with 81-DSP 1-MAC/clk
//     `qsag_ext4_mac_bfly` = 117 / 156 DSPs = 75.0% on ONE $45 Lattice ECP5-85F!).
module qsag_p2_compact #(
    parameter int TAGW          = 7,
    parameter int AW            = 16,
    parameter int BW            = 16,
    parameter bit USE_PIPE_SBOX = 1'b0
) (
    input  logic            clk,
    input  logic            rst,
    input  logic            in_valid,
    output logic            in_ready,
    input  logic [767:0]    in_state,
    input  logic            in_jive,
    input  logic [TAGW-1:0] in_tag,
    output logic            out_valid,
    output logic [767:0]    out_state,
    output logic            out_jive,
    output logic [TAGW-1:0] out_tag,
    output logic            busy
);
    localparam int            MUL_LAT  = qsag_ni_pkg::GL_MUL_LAT;  // 5 clocks
    localparam int            SBOX_LAT = qsag_ni_pkg::P2_SBOX_LAT; // 13 clocks
    localparam int            CHUNK34  = 34;
    localparam int            CHUNK26  = (AW <= 16) ? 38 : 26;
    localparam logic [63:0]   GL_P     = qsag_ni_pkg::GL_P;
    localparam int            LW       = 76;
    localparam logic [LW-1:0] MI0_BIAS = LW'(128'(2) * 128'(GL_P) - (128'd1 << 64) + 128'd1) << 6;
    localparam logic [65:0]   NEG_1P66 = 66'h3_0000_0000_FFFF_FFFF; // 2^66 - GL_P

    typedef enum logic [1:0] {IDLE, LIN_PREP, LIN_STREAM, SBOX} state_t;
    state_t st;

    logic [767:0]  x, x_base, rc;
    logic [267:0]  ff, m4_col0, m4_col1, m4_col2;
    logic [4:0]    pass, sb_cnt;
    logic [3:0]    p_cnt, lstep;
    logic [1:0]    lc, sb_stage;
    logic [67:0]   sum12_q, sum12_next;
    logic [LW-1:0] lazy_d, lazy_q;
    logic [63:0]   rc_lane_q, red_y_q, mul_r;
    logic          mi;

    assign busy     = (st != IDLE) || out_valid;
    assign in_ready = !rst && (st == IDLE);

    logic [66:0] ff_one;
    qsag_sum_csa #(.W(67), .N(3), .CHUNK(CHUNK34)) u_ff1 (
        .x({67'(x[64*8 +: 64]) << 2, 67'(x[64*4 +: 64]) << 1, 67'(x[0 +: 64])}),
        .y(ff_one));

    qsag_add_split #(.W(68), .CHUNK(CHUNK34)) u_sum_acc (
        .a(sum12_q), .b(68'(x[63:0])), .y(sum12_next));

    wire [66:0] mb [4];
    assign mb[0] = 67'(x[64*0 +: 64]);
    assign mb[1] = 67'(x[64*3 +: 64]);
    assign mb[2] = 67'(x[64*6 +: 64]);
    assign mb[3] = 67'(x[64*9 +: 64]);

    logic [267:0] m4_d;
    for (genvar k = 0; k < 4; k++) begin : g_m4
        wire [5*67-1:0] m4_terms = {
            mb[(k + 3) % 4],
            mb[(k + 2) % 4],
            mb[(k + 1) % 4],
            mb[(k + 1) % 4] << 1,
            mb[k] << 1
        };
        qsag_sum_csa #(.W(67), .N(5), .CHUNK(CHUNK34)) u_m4 (
            .x(m4_terms), .y(m4_d[67*k +: 67]));
    end

    qsag_p2_rc u_rc (.pass(pass), .rc(rc));
    wire [3:0]  next_rc_idx = (lstep < 4'd11) ? (lstep + 4'd1) : 4'd0;
    wire [63:0] rc_next     = rc[64*next_rc_idx +: 64];
    wire [3:0]  safe_lstep  = (lstep < 4'd12) ? lstep : 4'd0;
    wire [66:0] add_i       = (pass == 5'd30)
                            ? ((out_jive && lstep < 4'd4) ? ff[66:0] : 67'd0)
                            : 67'(rc_lane_q);

    wire [66:0] m4_cur = (lc == 2'd0) ? m4_col0[66:0]
                       : (lc == 2'd1) ? m4_col1[66:0]
                                      : m4_col2[66:0];
    wire [3:0]  sh_amt = (safe_lstep <= 4'd1) ? 4'd0 : (safe_lstep - 4'd1);
    logic [5*LW-1:0] lin_terms;

    always_comb begin
        if (!mi) begin
            lin_terms = {
                LW'(add_i),
                LW'(m4_cur),
                LW'(m4_col2[66:0]),
                LW'(m4_col1[66:0]),
                LW'(m4_col0[66:0])
            };
        end else if (safe_lstep == 4'd0) begin
            lin_terms = {
                LW'(add_i),
                MI0_BIAS,
                {12'b0, ~x[63:0]} << 6,
                LW'(sum12_q),
                LW'(0)
            };
        end else begin
            lin_terms = {
                LW'(add_i),
                LW'(x[63:0]) << sh_amt,
                LW'(sum12_q),
                LW'(0),
                LW'(0)
            };
        end
    end

    qsag_sum_csa #(.W(LW), .N(5), .CHUNK(CHUNK26)) u_lin_s1 (.x(lin_terms), .y(lazy_d));

    logic [63:0] lo;
    logic [11:0] t_hi;
    assign {t_hi, lo} = lazy_q;
    /* verilator lint_off UNUSEDSIGNAL */
    logic [65:0] r0, r1;
    /* verilator lint_on UNUSEDSIGNAL */
    wire [4*66-1:0] tr0 = {66'd1,            ~{54'b0, t_hi}, {22'b0, t_hi, 32'b0}, {2'b0, lo}};
    wire [4*66-1:0] tr1 = {NEG_1P66 + 66'd1, ~{54'b0, t_hi}, {22'b0, t_hi, 32'b0}, {2'b0, lo}};
    qsag_sum_csa #(.W(66), .N(4), .CHUNK(CHUNK34)) u_lin_r0 (.x(tr0), .y(r0));
    qsag_sum_csa #(.W(66), .N(4), .CHUNK(CHUNK34)) u_lin_r1 (.x(tr1), .y(r1));
    wire [63:0] red_y_d = r1[65] ? r0[63:0] : r1[63:0];

    if (USE_PIPE_SBOX) begin : g_pipe_sbox
        qsag_p2_sbox7 #(.AW(AW), .BW(BW)) u_sbox (.clk(clk), .x(x[63:0]), .y(mul_r));
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_p = &{1'b0, x_base, sb_stage};
        /* verilator lint_on UNUSEDSIGNAL */
    end else begin : g_seq_sbox
        wire [63:0] mul_a = x[63:0];
        wire [63:0] mul_b = (sb_stage == 2'd0 || sb_stage == 2'd2) ? x[63:0] : x_base[63:0];
        qsag_gl64_dsp_mul #(.AW(AW), .BW(BW), .REG_OUT(1)) u_mul (
            .clk(clk), .a(mul_a), .b(mul_b), .r(mul_r));
    end

    always_ff @(posedge clk) begin
        lazy_q  <= lazy_d;
        red_y_q <= red_y_d;
        case (st)
            IDLE: if (!rst && in_valid) begin
                x        <= in_state;
                out_tag  <= in_tag;
                out_jive <= in_jive;
            end
            LIN_PREP: begin
                x       <= {x[63:0], x[767:64]};
                sum12_q <= (p_cnt == 4'd0) ? 68'(x[63:0]) : sum12_next;
                if (pass == 5'd0 && p_cnt < 4'd4) ff <= {ff_one, ff[267:67]};
                if (p_cnt < 4'd3) begin
                    m4_col0 <= m4_col1;
                    m4_col1 <= m4_col2;
                    m4_col2 <= m4_d;
                end
                if (p_cnt == 4'd11) rc_lane_q <= rc[0 +: 64];
            end
            LIN_STREAM: begin
                rc_lane_q <= rc_next;
                if (pass == 5'd30 && lstep < 4'd4) ff <= {67'd0, ff[267:67]};
                if (lstep < 4'd2)        x <= {x[63:0], x[767:64]};
                else if (lstep < 4'd12)  x <= {x[63:0], x[767:704], red_y_q, x[639:64]};
                else if (lstep == 4'd12) x[703:640] <= red_y_q;
                else                     x[767:704] <= red_y_q;

                if (lstep < 4'd12 && lc == 2'd2) begin
                    m4_col0 <= {67'd0, m4_col0[267:67]};
                    m4_col1 <= {67'd0, m4_col1[267:67]};
                    m4_col2 <= {67'd0, m4_col2[267:67]};
                end
                if (lstep == 4'd13) begin
                    if (pass == 5'd30) out_state <= {red_y_q, x[703:0]};
                    else if (!USE_PIPE_SBOX) x_base <= {red_y_q, x[703:0]};
                end
            end
            SBOX: begin
                if (USE_PIPE_SBOX) begin
                    if (mi) begin
                        if (sb_cnt == 5'(SBOX_LAT)) x[63:0] <= mul_r;
                    end else begin
                        // Stream 12 lanes into u_sbox on sb_cnt = 0..11; capture outputs on
                        // sb_cnt = SBOX_LAT .. SBOX_LAT+11 into x[767:704] shifting right 12 times!
                        if (sb_cnt < 5'd12)
                            x <= {x[63:0], x[767:64]};
                        else if (sb_cnt >= 5'(SBOX_LAT))
                            x <= {mul_r, x[767:64]};
                    end
                end else begin
                    if (mi) begin
                        if (sb_cnt == 5'(MUL_LAT)) x[63:0] <= mul_r;
                    end else begin
                        if (sb_cnt < 5'(MUL_LAT)) x <= {x[63:0], x[767:64]};
                        else                      x <= {mul_r, x[767:64]};
                        if (sb_cnt < 5'd12)       x_base <= {x_base[63:0], x_base[767:64]};
                    end
                end
            end
            default: ;
        endcase
    end

    always_ff @(posedge clk) begin
        out_valid <= 1'b0;
        if (rst) begin
            st        <= IDLE;
            out_valid <= 1'b0;
        end else begin
            case (st)
                IDLE: if (in_valid) begin
                    pass  <= 5'd0;
                    mi    <= 1'b0;
                    p_cnt <= 4'd0;
                    st    <= LIN_PREP;
                end
                LIN_PREP: begin
                    if (p_cnt == 4'd11) begin
                        lstep <= 4'd0;
                        lc    <= 2'd0;
                        st    <= LIN_STREAM;
                    end else begin
                        p_cnt <= p_cnt + 4'd1;
                    end
                end
                LIN_STREAM: begin
                    if (lstep < 4'd12) lc <= (lc == 2'd2) ? 2'd0 : (lc + 2'd1);
                    if (lstep == 4'd13) begin
                        if (pass == 5'd30) begin
                            out_valid <= 1'b1;
                            st        <= IDLE;
                        end else begin
                            pass     <= pass + 5'd1;
                            mi       <= (pass >= 5'd4) && (pass <= 5'd25);
                            sb_stage <= 2'd0;
                            sb_cnt   <= 5'd0;
                            st       <= SBOX;
                        end
                    end else begin
                        lstep <= lstep + 4'd1;
                    end
                end
                SBOX: begin
                    if (USE_PIPE_SBOX) begin
                        if (mi) begin
                            if (sb_cnt == 5'(SBOX_LAT)) begin
                                p_cnt <= 4'd0;
                                st    <= LIN_PREP;
                            end else begin
                                sb_cnt <= sb_cnt + 5'd1;
                            end
                        end else begin
                            if (sb_cnt == 5'(SBOX_LAT + 11)) begin
                                p_cnt <= 4'd0;
                                st    <= LIN_PREP;
                            end else begin
                                sb_cnt <= sb_cnt + 5'd1;
                            end
                        end
                    end else if (mi) begin
                        if (sb_cnt == 5'(MUL_LAT)) begin
                            sb_cnt <= 5'd0;
                            if (sb_stage == 2'd3) begin
                                p_cnt <= 4'd0;
                                st    <= LIN_PREP;
                            end else begin
                                sb_stage <= sb_stage + 2'd1;
                            end
                        end else begin
                            sb_cnt <= sb_cnt + 5'd1;
                        end
                    end else begin
                        if (sb_cnt == 5'(MUL_LAT + 11)) begin
                            sb_cnt <= 5'd0;
                            if (sb_stage == 2'd3) begin
                                p_cnt <= 4'd0;
                                st    <= LIN_PREP;
                            end else begin
                                sb_stage <= sb_stage + 2'd1;
                            end
                        end else begin
                            sb_cnt <= sb_cnt + 5'd1;
                        end
                    end
                end
                default: st <= IDLE;
            endcase
        end
    end
endmodule
