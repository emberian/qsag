// Compact rotating-ring Poseidon2 width-12 core for ECP5:
//   - USE_PIPE_SBOX=0 (`ECP5_COMPACT`): ONE pipelined Goldilocks multiplier (`qsag_gl64_dsp_mul`:
//     9 MULT18X18D) reused across 4 S-box stages (`x^2, x^3, x^6, x^7`) with `DP16KD`-backed
//     `xbase_mem`, 1,878 clks/perm;
//   - USE_PIPE_SBOX=1 (`ECP5_FULLRATE`): ONE full-rate pipelined `qsag_p2_sbox7` (`4 x 9 = 36`
//     MULT18X18D, 1 `x^7` per clock!), streaming all 12 lanes in 25 clocks on external rounds
//     and lane 0 in 13 clocks on internal rounds (1,314 clks/perm; paired with the 45-DSP five-lane
//     `qsag_fp5_compact_bfly` = 81 / 156 DSPs = 51.9% on ONE $45 Lattice ECP5-85F!).
//   - Supports both 1-cycle `in_state` load (`P2_PERM` / `P2_JIVE`) and 64-bit streamed
//     `in_lane_*` / `out_lane_*` (`qsag_p2_chain_engine` & `g_y_bram`), eliminating 768-bit
//     cross-chip output and chain multiplexers.
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
    input  logic            in_lane_valid,
    input  logic            in_lane_last,
    input  logic [63:0]     in_lane_data,
    output logic            out_valid,
    output logic            out_jive,
    output logic [TAGW-1:0] out_tag,
    output logic            out_lane_valid,
    output logic [3:0]      out_lane_idx,
    output logic [63:0]     out_lane_data,
    output logic            busy
);
    localparam int            MUL_LAT  = qsag_ni_pkg::GL_MUL_LAT;  // 5 clocks
    localparam int            SBOX_LAT = qsag_ni_pkg::P2_SBOX_LAT; // 13 clocks
    localparam int            CHUNK34  = (AW <= 16) ? 68 : 34;
    localparam int            CHUNK26  = (AW <= 16) ? 76 : 26;
    localparam logic [63:0]   GL_P     = qsag_ni_pkg::GL_P;
    localparam int            LW       = 76;
    localparam logic [LW-1:0] MI0_BIAS = LW'(128'(2) * 128'(GL_P) - (128'd1 << 64) + 128'd1) << 6;
    localparam logic [65:0]   NEG_1P66 = 66'h3_0000_0000_FFFF_FFFF; // 2^66 - GL_P

    typedef enum logic [1:0] {IDLE, LIN_PREP, LIN_STREAM, SBOX} state_t;
    state_t st;

    logic [767:0]  x, rc;
    logic [267:0]  ff, m4_col0, m4_col1, m4_col2;
    logic [4:0]    pass, sb_cnt;
    logic [3:0]    p_cnt, lstep, drain_cnt;
    logic [1:0]    lc, sb_stage;
    logic [67:0]   sum12_q, sum12_next;
    logic [LW-1:0] lazy_d, lazy_q;
    logic [63:0]   rc_lane_q, red_y_q, mul_r;
    logic          mi, draining;

    assign busy           = (st != IDLE) || out_valid || draining;
    assign in_ready       = !rst && (st == IDLE) && !draining;
    assign out_lane_valid = draining;
    assign out_lane_idx   = drain_cnt;
    assign out_lane_data  = x[63:0];

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

    wire [3:0] next_rc_idx = (lstep < 4'd11) ? (lstep + 4'd1) : 4'd0;
    if (AW <= 16) begin : g_rc_bram
        function automatic logic [767:0] p2_rc_full(input logic [4:0] p);
            case (p)
                5'd0: p2_rc_full = {64'hF71A7A990ECFCB5D, 64'hAC92EC4A1B06E950, 64'h304981CCA391AAEA, 64'h8E3B30EC8A038FF1, 64'h1EED28365F7E78DE, 64'hA580070372A07498, 64'h5162A1B8704BEA74, 64'hAB50796FBF5FE8E4, 64'h21478BBCDAD17885, 64'h9D4A1D75CA56751F, 64'hED0FC745B9C6495B, 64'hFDA3872AFF6CE05D};
                5'd1: p2_rc_full = {64'hC7E9E09CCCCCA51D, 64'h25EA832EEDD17175, 64'h10E2A54EACF5A642, 64'h2281D230035AD8B1, 64'h1B1F313E73474D0C, 64'h52D5E98EBFFCAF99, 64'h027799AD325D72D4, 64'hF0FCF63D66B6F91B, 64'hC13FA1980F8B3B3E, 64'h55430D5E3FA8777F, 64'h12831554DC6B2FA0, 64'hEF0CA3A081E3B2CD};
                5'd2: p2_rc_full = {64'hB689B16D245DD00F, 64'h51AD3DD41EF12666, 64'h4EABDD085645BBD8, 64'h59057FBA3D66EFA5, 64'hC8DCE552B55B7C92, 64'h6DBB327EE8D91842, 64'hE50ADB5D20EA41E7, 64'h1E87AAAE642CAA37, 64'h17048E4CD8752C18, 64'h7603BA7D318F36C7, 64'h1A7AB33C5331C21C, 64'h80409B59EA5A74D4};
                5'd3: p2_rc_full = {64'hD8F199768234A623, 64'h7747FF82D3E3CAD7, 64'hDC1F27243FACB794, 64'h37C7DF185CC152DD, 64'h882608EBDEAD786D, 64'h3A2C0C2D2D286512, 64'h4B28370115DB8D54, 64'h8391AAC6F90B7908, 64'h7F17B925BC78BE59, 64'hE4C329CD958F137D, 64'hD1C8D36A42924DC1, 64'h1BD072659A8FF2C9};
                5'd4:  p2_rc_full = {704'd0, 64'hF731924A2CAB81C3};
                5'd5:  p2_rc_full = {704'd0, 64'h255089C3FAB8168D};
                5'd6:  p2_rc_full = {704'd0, 64'h3A3D76511C74EBA8};
                5'd7:  p2_rc_full = {704'd0, 64'h48EADF244FC82AD4};
                5'd8:  p2_rc_full = {704'd0, 64'hE30F632AC44C7191};
                5'd9:  p2_rc_full = {704'd0, 64'h5FDC66FDC64EC0CD};
                5'd10: p2_rc_full = {704'd0, 64'h6803C41A69874702};
                5'd11: p2_rc_full = {704'd0, 64'hC5C38296FA52132F};
                5'd12: p2_rc_full = {704'd0, 64'hBAD3E9CF2FDDCD81};
                5'd13: p2_rc_full = {704'd0, 64'h3AF68FF700854AA8};
                5'd14: p2_rc_full = {704'd0, 64'h4D8D3C348A3EE863};
                5'd15: p2_rc_full = {704'd0, 64'hA5BDA13ACAD01E85};
                5'd16: p2_rc_full = {704'd0, 64'h28182BBAFEBD907E};
                5'd17: p2_rc_full = {704'd0, 64'h13BCC0B1EEEEBEE8};
                5'd18: p2_rc_full = {704'd0, 64'h265109DE178C26A2};
                5'd19: p2_rc_full = {704'd0, 64'h3B225DF36DE85CE1};
                5'd20: p2_rc_full = {704'd0, 64'h3ACF9E9164C55E09};
                5'd21: p2_rc_full = {704'd0, 64'h90B166953084A6CA};
                5'd22: p2_rc_full = {704'd0, 64'h8AB96AAE41B50F8E};
                5'd23: p2_rc_full = {704'd0, 64'hF7C88906BE121CF6};
                5'd24: p2_rc_full = {704'd0, 64'hF3CB9E9367497B0B};
                5'd25: p2_rc_full = {704'd0, 64'h0B8BCB26CD19E5FA};
                5'd26: p2_rc_full = {64'h631246D895542634, 64'hF4293F809DC78676, 64'h1FBE6A7B16CB5A5A, 64'hE3CA05DD13AA415A, 64'hE84A6FA369462250, 64'h31B03974AF5BA20A, 64'hF7EC2DA54B00B0D6, 64'h553810B2DE6A7215, 64'h6CCE1772A93FC829, 64'h177C074EE0CC5FCE, 64'hCB6713D4200E5452, 64'hB70495E46A559CEC};
                5'd27: p2_rc_full = {64'h8BDF12E530D0A748, 64'hF46592330118C9F8, 64'h98A2067776D1B323, 64'h234AEEBCAAAA8BC3, 64'h9C3DA97122A82287, 64'h2CDF4BC6B240EB9B, 64'hFC5F6B1A8CCFE5E0, 64'h39E821566741B4A4, 64'h09BCC7B4B0181300, 64'hDF2C27C73649ECF8, 64'hF873C49F77E7721A, 64'hB76AB8647401EE88};
                5'd28: p2_rc_full = {64'hA8C29664619D5FD6, 64'h49C0707C765CAEEB, 64'hE24F6CB7E1E1CDDF, 64'h6FC27EB618A7A546, 64'h49B9067B47E1C79A, 64'hD576672AEE7D43EA, 64'hE88F37D72A053DC9, 64'h480703C5F50F18B3, 64'h0C7E07A6681F782F, 64'h7A566184C747CD1E, 64'hBBBEB66FDDEB378B, 64'h0A57706D0A935206};
                5'd29: p2_rc_full = {64'h675ED63C2A5DE772, 64'h317619AB4F0393DC, 64'h9AD521BC0C7F82B1, 64'hD3FF6275F9809F74, 64'h31D92A0350814968, 64'hA2E965EC082BD11E, 64'h2ED4EAC1C05A2FAD, 64'hD88DBAC1FEA4410D, 64'h201069A2F920FF25, 64'hA2B9A1FC2877F03F, 64'h4721CE08A39255B0, 64'hFAE6F26D3EB5538B};
                default: p2_rc_full = 768'd0;
            endcase
        endfunction
        (* rom_style = "block" *) logic [63:0] rc_rom [0:511];
        logic [767:0] rc_init_row;
        initial begin
            for (int p = 0; p < 32; p++) begin
                rc_init_row = p2_rc_full(5'(p));
                for (int l = 0; l < 16; l++)
                    rc_rom[p * 16 + l] = (l < 12) ? rc_init_row[64*l +: 64] : 64'd0;
            end
        end
        wire [3:0] rc_addr_lo = (st == LIN_PREP) ? 4'd0 : next_rc_idx;
        always_ff @(posedge clk) rc_lane_q <= rc_rom[{pass, rc_addr_lo}];
        assign rc = '0;
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_rc = &{1'b0, rc};
        /* verilator lint_on UNUSEDSIGNAL */
    end else begin : g_rc_comb
        qsag_p2_rc u_rc (.pass(pass), .rc(rc));
        always_ff @(posedge clk) begin
            if (st == LIN_PREP && p_cnt == 4'd11) rc_lane_q <= rc[0 +: 64];
            else if (st == LIN_STREAM)            rc_lane_q <= rc[64*next_rc_idx +: 64];
        end
    end
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
    logic [63:0] red_y_d;
    if (AW <= 16) begin : g_red_ecp5
        wire [43:0] t_f44 = (t_hi == 12'd0) ? 44'd0 : {t_hi - 12'd1, 20'hFFFFF, 12'd0 - t_hi};
        /* verilator lint_off UNUSEDSIGNAL */
        wire [64:0] r0 = {1'b0, lo} + {21'd0, t_f44};
        wire [65:0] r1 = {1'b0, r0} + NEG_1P66;
        /* verilator lint_on UNUSEDSIGNAL */
        assign red_y_d = r1[65] ? r0[63:0] : r1[63:0];
    end else begin : g_red_wide
        /* verilator lint_off UNUSEDSIGNAL */
        logic [65:0] r0, r1;
        /* verilator lint_on UNUSEDSIGNAL */
        wire [4*66-1:0] tr0 = {66'd1,            ~{54'b0, t_hi}, {22'b0, t_hi, 32'b0}, {2'b0, lo}};
        wire [4*66-1:0] tr1 = {NEG_1P66 + 66'd1, ~{54'b0, t_hi}, {22'b0, t_hi, 32'b0}, {2'b0, lo}};
        qsag_sum_csa #(.W(66), .N(4), .CHUNK(CHUNK34)) u_lin_r0 (.x(tr0), .y(r0));
        qsag_sum_csa #(.W(66), .N(4), .CHUNK(CHUNK34)) u_lin_r1 (.x(tr1), .y(r1));
        assign red_y_d = r1[65] ? r0[63:0] : r1[63:0];
    end

    if (USE_PIPE_SBOX) begin : g_pipe_sbox
        qsag_p2_sbox7 #(.AW(AW), .BW(BW)) u_sbox (.clk(clk), .x(x[63:0]), .y(mul_r));
        /* verilator lint_off UNUSEDSIGNAL */
        wire unused_p = &{1'b0, sb_stage};
        /* verilator lint_on UNUSEDSIGNAL */
    end else begin : g_seq_sbox
        (* ram_style = "block", no_rw_check *) logic [63:0] xbase_mem [0:511];
        logic [63:0] xbase_rd_q;
        wire       xbase_we = (st == LIN_STREAM) && (lstep >= 4'd2) && (pass != 5'd30);
        wire [3:0] xbase_wa = lstep - 4'd2;
        wire [3:0] xbase_ra = ((st == SBOX) && !mi && sb_stage[0] && (sb_cnt < 5'd11))
                            ? (sb_cnt[3:0] + 4'd1)
                            : 4'd0;
        always_ff @(posedge clk) begin
            if (xbase_we) xbase_mem[{5'd0, xbase_wa}] <= red_y_q;
            xbase_rd_q <= xbase_mem[{5'd0, xbase_ra}];
        end
        wire [63:0] mul_a = x[63:0];
        wire [63:0] mul_b = (sb_stage == 2'd0 || sb_stage == 2'd2) ? x[63:0] : xbase_rd_q;
        qsag_gl64_dsp_mul #(.AW(AW), .BW(BW), .REG_OUT(1)) u_mul (
            .clk(clk), .a(mul_a), .b(mul_b), .r(mul_r));
    end

    always_ff @(posedge clk) begin
        lazy_q  <= lazy_d;
        red_y_q <= red_y_d;
        case (st)
            IDLE: begin
                if (draining) begin
                    x <= {x[63:0], x[767:64]};
                end else if (!rst && in_valid) begin
                    x        <= in_state;
                    out_tag  <= in_tag;
                    out_jive <= in_jive;
                end else if (!rst && in_lane_valid) begin
                    x <= {in_lane_data, x[767:64]};
                    if (in_lane_last) begin
                        out_tag  <= in_tag;
                        out_jive <= in_jive;
                    end
                end
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
            end
            LIN_STREAM: begin
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
            end
            SBOX: begin
                if (USE_PIPE_SBOX) begin
                    if (mi) begin
                        if (sb_cnt == 5'(SBOX_LAT)) x[63:0] <= mul_r;
                    end else begin
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
            draining  <= 1'b0;
            drain_cnt <= 4'd0;
        end else begin
            case (st)
                IDLE: begin
                    if (draining) begin
                        if (drain_cnt == 4'd11) draining  <= 1'b0;
                        else                    drain_cnt <= drain_cnt + 4'd1;
                    end else if (in_valid || (in_lane_valid && in_lane_last)) begin
                        pass  <= 5'd0;
                        mi    <= 1'b0;
                        p_cnt <= 4'd0;
                        st    <= LIN_PREP;
                    end
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
                            draining  <= 1'b1;
                            drain_cnt <= 4'd0;
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
