// Compact Poseidon2 width-12 core for ECP5_COMPACT: instantiates ONE pipelined S-box unit
// (`qsag_p2_sbox7`: 4 multipliers = 64 MULT18X18D on ECP5) and ONE single-lane pipelined carry-save
// linear reducer (saving ~25,000 LUT4 vs 12 parallel linear lanes). External rounds stream all 12
// S-box lanes at 1 lane/clock (25 clocks); internal rounds stream lane 0 alone (14 clocks).
// Total latency: 992 clocks/permutation (3.4x faster than single-multiplier serial, 12x fewer DSPs
// than the 12-lane ring, <= 18 logic levels).
module qsag_p2_compact #(
    parameter int TAGW = 7,
    parameter int AW   = 16,
    parameter int BW   = 16
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
    localparam int          SB_LAT   = qsag_ni_pkg::P2_SBOX_LAT; // 13 clocks
    localparam logic [63:0] GL_P     = qsag_ni_pkg::GL_P;
    localparam int          LW       = 76;
    localparam logic [LW-1:0] MI0_BIAS = LW'(128'(2) * 128'(GL_P) - (128'd1 << 64) + 128'd1) << 6;
    localparam logic [65:0]   NEG_1P66 = 66'h3_0000_0000_FFFF_FFFF; // 2^66 - GL_P

    typedef enum logic [1:0] {IDLE, LIN_PREP, LIN_STREAM, SBOX} state_t;
    state_t st;

    logic [767:0]     x, rc;
    logic [267:0]     ff;
    logic [803:0]     addend;
    logic [4:0]       pass, sb_cnt;
    logic [1:0]       m4_cnt, lk, lc;
    logic [3:0]       lstep, in_idx, idx_q1, idx_q2;
    logic [67:0]      sum12_d, sum12_q;
    logic [11:0][66:0] m4_q;
    logic [LW-1:0]    lazy_d, lazy_q;
    logic [63:0]      red_y_q;
    logic             mi;

    assign busy     = (st != IDLE) || out_valid;
    assign in_ready = !rst && (st == IDLE);
    assign mi       = (pass >= 5'd5) && (pass <= 5'd26);

    // Shallow carry-save + split-add feed-forward precompute: l + 2*r + 4*t (< 7 * 2^64).
    logic [267:0] ff_d;
    for (genvar i = 0; i < 4; i++) begin : g_ff
        wire [3*67-1:0] f_terms = {
            67'(in_state[64*(i+8) +: 64]) << 2,
            67'(in_state[64*(i+4) +: 64]) << 1,
            67'(in_state[64*i     +: 64])
        };
        qsag_sum_csa #(.W(67), .N(3), .CHUNK(24)) u_ff (
            .x(f_terms), .y(ff_d[67*i +: 67]));
    end

    qsag_p2_rc u_rc (.pass(pass), .rc(rc));
    always_comb begin
        for (int i = 0; i < 12; i++) addend[67*i +: 67] = 67'(rc[64*i +: 64]);
        if (pass == 5'd30) begin
            addend = '0;
            if (out_jive) addend[267:0] = ff;
        end
    end

    // ---- Compact Linear Prep: 12-lane sum (for M_I) and 1-column-per-clock M4 (for M_E).
    logic [12*68-1:0] x_ext68;
    for (genvar i = 0; i < 12; i++) begin : g_x68
        assign x_ext68[68*i +: 68] = 68'(x[64*i +: 64]);
    end
    qsag_sum_csa #(.W(68), .N(12), .CHUNK(24)) u_sum12 (.x(x_ext68), .y(sum12_d));

    wire [1:0]  col_c = (m4_cnt < 2'd3) ? m4_cnt : 2'd0;
    wire [66:0] mb [4];
    assign mb[0] = 67'(x[64*(32'(col_c))      +: 64]);
    assign mb[1] = 67'(x[64*(32'(col_c) + 3)  +: 64]);
    assign mb[2] = 67'(x[64*(32'(col_c) + 6)  +: 64]);
    assign mb[3] = 67'(x[64*(32'(col_c) + 9)  +: 64]);

    logic [3:0][66:0] m4_d;
    for (genvar k = 0; k < 4; k++) begin : g_m4
        wire [5*67-1:0] m4_terms = {
            mb[(k + 3) % 4],
            mb[(k + 2) % 4],
            mb[(k + 1) % 4],
            mb[(k + 1) % 4] << 1,
            mb[k] << 1
        };
        qsag_sum_csa #(.W(67), .N(5), .CHUNK(24)) u_m4 (
            .x(m4_terms), .y(m4_d[k]));
    end

    // ---- Compact Single-Lane Linear Stream (Stage 1 CSA+add -> Stage 2 Goldilocks fold).
    wire [3:0]    safe_idx = (in_idx < 4'd12) ? in_idx : 4'd0;
    wire [66:0]   add_i    = addend[67*safe_idx +: 67];
    wire [63:0]   x_lane   = x[64*safe_idx +: 64];
    wire [3:0]    sh_amt   = (safe_idx <= 4'd1) ? 4'd0 : (safe_idx - 4'd1);
    wire [1:0]    safe_lc  = (lc < 2'd3) ? lc : 2'd0;
    logic [5*LW-1:0] lin_terms;

    always_comb begin
        if (!mi) begin
            lin_terms = {
                LW'(add_i),
                LW'(m4_q[{safe_lc, lk}]),
                LW'(m4_q[{2'd2, lk}]),
                LW'(m4_q[{2'd1, lk}]),
                LW'(m4_q[{2'd0, lk}])
            };
        end else if (safe_idx == 4'd0) begin
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
                LW'(x_lane) << sh_amt,
                LW'(sum12_q),
                LW'(0),
                LW'(0)
            };
        end
    end

    qsag_sum_csa #(.W(LW), .N(5), .CHUNK(24)) u_lin_s1 (.x(lin_terms), .y(lazy_d));

    logic [63:0] lo;
    logic [11:0] t_hi;
    assign {t_hi, lo} = lazy_q;
    /* verilator lint_off UNUSEDSIGNAL */
    logic [65:0] r0, r1;
    /* verilator lint_on UNUSEDSIGNAL */
    wire [4*66-1:0] tr0 = {66'd1, ~{54'b0, t_hi}, {22'b0, t_hi, 32'b0}, {2'b0, lo}};
    wire [4*66-1:0] tr1 = {NEG_1P66 + 66'd1, ~{54'b0, t_hi}, {22'b0, t_hi, 32'b0}, {2'b0, lo}};
    qsag_sum_csa #(.W(66), .N(4), .CHUNK(24)) u_lin_r0 (.x(tr0), .y(r0));
    qsag_sum_csa #(.W(66), .N(4), .CHUNK(24)) u_lin_r1 (.x(tr1), .y(r1));
    wire [63:0] red_y_d = r1[65] ? r0[63:0] : r1[63:0];

    // ---- S-box datapath.
    wire [4:0]  n_lanes   = mi ? 5'd1 : 5'd12;
    wire [3:0]  sb_in_idx = (sb_cnt < n_lanes) ? sb_cnt[3:0] : 4'd0;
    wire [3:0]  sb_out_k  = sb_cnt[3:0] - 4'(SB_LAT);
    logic [63:0] sb_y;
    qsag_p2_sbox7 #(.AW(AW), .BW(BW)) u_sbox (
        .clk(clk), .x(x[64*sb_in_idx +: 64]), .y(sb_y));

    always_ff @(posedge clk) begin
        out_valid <= 1'b0;
        lazy_q    <= lazy_d;
        idx_q1    <= safe_idx;
        red_y_q   <= red_y_d;
        idx_q2    <= idx_q1;

        if (rst) begin
            st        <= IDLE;
            out_valid <= 1'b0;
        end else begin
            case (st)
                IDLE: begin
                    if (in_valid) begin
                        x        <= in_state;
                        out_tag  <= in_tag;
                        out_jive <= in_jive;
                        ff       <= ff_d;
                        pass     <= 5'd0;
                        m4_cnt   <= 2'd0;
                        st       <= LIN_PREP;
                    end
                end
                LIN_PREP: begin
                    if (mi) begin
                        sum12_q <= sum12_d;
                        lstep   <= 4'd0;
                        in_idx  <= 4'd0;
                        lk      <= 2'd0;
                        lc      <= 2'd0;
                        st      <= LIN_STREAM;
                    end else begin
                        for (int k = 0; k < 4; k++)
                            m4_q[{col_c, 2'(k)}] <= m4_d[k];
                        if (m4_cnt == 2'd2) begin
                            lstep  <= 4'd0;
                            in_idx <= 4'd0;
                            lk     <= 2'd0;
                            lc     <= 2'd0;
                            st     <= LIN_STREAM;
                        end else begin
                            m4_cnt <= m4_cnt + 2'd1;
                        end
                    end
                end
                LIN_STREAM: begin
                    if (lstep >= 4'd2 && idx_q2 < 4'd12) begin
                        x[64*idx_q2 +: 64] <= red_y_q;
                    end
                    if (lstep == 4'd13) begin
                        if (pass == 5'd30) begin
                            out_state <= {red_y_q, x[703:0]};
                            out_valid <= 1'b1;
                            st        <= IDLE;
                        end else begin
                            pass   <= pass + 5'd1;
                            sb_cnt <= 5'd0;
                            st     <= SBOX;
                        end
                    end else begin
                        lstep <= lstep + 4'd1;
                        if (lstep < 4'd11) begin
                            in_idx <= in_idx + 4'd1;
                            if (lc == 2'd2) begin
                                lc <= 2'd0;
                                lk <= lk + 2'd1;
                            end else begin
                                lc <= lc + 2'd1;
                            end
                        end
                    end
                end
                SBOX: begin
                    if (sb_cnt >= 5'(SB_LAT)) begin
                        x[64*sb_out_k +: 64] <= sb_y;
                    end
                    if (sb_cnt == 5'(SB_LAT) + n_lanes - 5'd1) begin
                        m4_cnt <= 2'd0;
                        st     <= LIN_PREP;
                    end else begin
                        sb_cnt <= sb_cnt + 5'd1;
                    end
                end
                default: st <= IDLE;
            endcase
        end
    end
endmodule
