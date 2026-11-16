// Compact rotating-ring Poseidon2 width-12 core for ECP5_COMPACT:
//   - Instantiates ONE pipelined S-box (`qsag_p2_sbox7`: 64 MULT18X18D on ECP5) fed directly from
//     `x[63:0]` with zero 12:1 read/write muxes;
//   - Rotates the 768-bit state register `x` (`x <= {..., x[767:64]}`) through ONE single-lane
//     pipelined carry-save linear reducer and ONE single-column M4 unit, eliminating ~18,000 LUT4
//     of wide dynamic multiplexers while keeping reg-to-reg logic depth <= 18 levels.
//   - Latency: 1,314 clocks/permutation (2.6x faster than single-multiplier serial, 12x fewer DSPs
//     than the 12-lane ring).
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
    localparam int            SB_LAT   = qsag_ni_pkg::P2_SBOX_LAT; // 13 clocks
    localparam logic [63:0]   GL_P     = qsag_ni_pkg::GL_P;
    localparam int            LW       = 76;
    localparam logic [LW-1:0] MI0_BIAS = LW'(128'(2) * 128'(GL_P) - (128'd1 << 64) + 128'd1) << 6;
    localparam logic [65:0]   NEG_1P66 = 66'h3_0000_0000_FFFF_FFFF; // 2^66 - GL_P

    typedef enum logic [1:0] {IDLE, LIN_PREP, LIN_STREAM, SBOX} state_t;
    state_t st;

    logic [767:0] x, rc;
    logic [267:0] ff, m4_col0, m4_col1, m4_col2;
    logic [4:0]   pass, sb_cnt;
    logic [3:0]   p_cnt, lstep;
    logic [1:0]   lc;
    logic [67:0]  sum12_q, sum12_next;
    logic [LW-1:0] lazy_d, lazy_q;
    logic [63:0]  red_y_q;
    logic         mi;

    assign busy     = (st != IDLE) || out_valid;
    assign in_ready = !rst && (st == IDLE);
    assign mi       = (pass >= 5'd5) && (pass <= 5'd26);

    // Single-lane feed-forward adder: during pass 0 LIN_PREP p_cnt=0..3, x[0], x[4], x[8] present
    // lanes (i, i+4, i+8) as `x` rotates!
    logic [66:0] ff_one;
    qsag_sum_csa #(.W(67), .N(3), .CHUNK(34)) u_ff1 (
        .x({67'(x[64*8 +: 64]) << 2, 67'(x[64*4 +: 64]) << 1, 67'(x[0 +: 64])}),
        .y(ff_one));

    // Sequential 12-lane accumulator during LIN_PREP (p_cnt = 0..11).
    qsag_add_split #(.W(68), .CHUNK(34)) u_sum_acc (
        .a(sum12_q), .b(68'(x[63:0])), .y(sum12_next));

    // Hardwired column M4 on x[0], x[3], x[6], x[9] (during p_cnt = 0, 1, 2, rotating `x` presents
    // columns 0, 1, 2 with zero column muxes).
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
        qsag_sum_csa #(.W(67), .N(5), .CHUNK(34)) u_m4 (
            .x(m4_terms), .y(m4_d[67*k +: 67]));
    end

    // Round constant lookup for current streamed lane.
    qsag_p2_rc u_rc (.pass(pass), .rc(rc));
    wire [3:0]  safe_lstep = (lstep < 4'd12) ? lstep : 4'd0;
    wire [63:0] rc_lane    = rc[64*safe_lstep +: 64];
    wire [66:0] add_i      = (pass == 5'd30)
                           ? ((out_jive && lstep < 4'd4) ? ff[66:0] : 67'd0)
                           : 67'(rc_lane);

    // Single-lane linear stream (Stage 1 CSA+add -> Stage 2 Goldilocks fold).
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

    qsag_sum_csa #(.W(LW), .N(5), .CHUNK(38)) u_lin_s1 (.x(lin_terms), .y(lazy_d));

    logic [63:0] lo;
    logic [11:0] t_hi;
    assign {t_hi, lo} = lazy_q;
    /* verilator lint_off UNUSEDSIGNAL */
    logic [65:0] r0, r1;
    /* verilator lint_on UNUSEDSIGNAL */
    wire [4*66-1:0] tr0 = {66'd1,            ~{54'b0, t_hi}, {22'b0, t_hi, 32'b0}, {2'b0, lo}};
    wire [4*66-1:0] tr1 = {NEG_1P66 + 66'd1, ~{54'b0, t_hi}, {22'b0, t_hi, 32'b0}, {2'b0, lo}};
    qsag_sum_csa #(.W(66), .N(4), .CHUNK(34)) u_lin_r0 (.x(tr0), .y(r0));
    qsag_sum_csa #(.W(66), .N(4), .CHUNK(34)) u_lin_r1 (.x(tr1), .y(r1));
    wire [63:0] red_y_d = r1[65] ? r0[63:0] : r1[63:0];

    // S-box hardwired directly to lane 0 (`x[63:0]`) with zero input mux!
    logic [63:0] sb_y;
    qsag_p2_sbox7 #(.AW(AW), .BW(BW)) u_sbox (.clk(clk), .x(x[63:0]), .y(sb_y));

    always_ff @(posedge clk) begin
        out_valid <= 1'b0;
        lazy_q    <= lazy_d;
        red_y_q   <= red_y_d;

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
                        pass     <= 5'd0;
                        p_cnt    <= 4'd0;
                        st       <= LIN_PREP;
                    end
                end
                LIN_PREP: begin
                    x       <= {x[63:0], x[767:64]};
                    sum12_q <= (p_cnt == 4'd0) ? 68'(x[63:0]) : sum12_next;
                    if (pass == 5'd0 && p_cnt < 4'd4) begin
                        ff <= {ff_one, ff[267:67]};
                    end
                    if (p_cnt < 4'd3) begin
                        m4_col0 <= m4_col1;
                        m4_col1 <= m4_col2;
                        m4_col2 <= m4_d;
                    end
                    if (p_cnt == 4'd11) begin
                        lstep <= 4'd0;
                        lc    <= 2'd0;
                        st    <= LIN_STREAM;
                    end else begin
                        p_cnt <= p_cnt + 4'd1;
                    end
                end
                LIN_STREAM: begin
                    if (pass == 5'd30 && lstep < 4'd4) begin
                        ff <= {67'd0, ff[267:67]};
                    end
                    if (lstep < 4'd2) begin
                        x <= {x[63:0], x[767:64]};
                    end else if (lstep < 4'd12) begin
                        x <= {x[63:0], x[767:704], red_y_q, x[639:64]};
                    end else if (lstep == 4'd12) begin
                        x[703:640] <= red_y_q;
                    end else begin
                        x[767:704] <= red_y_q;
                    end

                    if (lstep < 4'd12) begin
                        if (lc == 2'd2) begin
                            lc      <= 2'd0;
                            m4_col0 <= {67'd0, m4_col0[267:67]};
                            m4_col1 <= {67'd0, m4_col1[267:67]};
                            m4_col2 <= {67'd0, m4_col2[267:67]};
                        end else begin
                            lc <= lc + 2'd1;
                        end
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
                    end
                end
                SBOX: begin
                    if (mi) begin
                        if (sb_cnt == 5'(SB_LAT)) begin
                            x[63:0] <= sb_y;
                            p_cnt   <= 4'd0;
                            st      <= LIN_PREP;
                        end else begin
                            sb_cnt <= sb_cnt + 5'd1;
                        end
                    end else begin
                        if (sb_cnt < 5'd12) begin
                            x <= {x[63:0], x[767:64]};
                        end else if (sb_cnt >= 5'(SB_LAT)) begin
                            x <= {sb_y, x[767:64]};
                        end
                        if (sb_cnt == 5'(SB_LAT + 11)) begin
                            p_cnt <= 4'd0;
                            st    <= LIN_PREP;
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
