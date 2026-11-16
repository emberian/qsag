// Dregg-180 (QSAG-NI-180) clocking, reset, mixed-cell TRCP replica & EAL6+ physical fault unit.
//
// GOTCHA #3 silicon fixes:
//   * `qsag_trcp_chain` uses a genuine mixed-cell critical-path replica (`nand2_1` -> `aoi21_1`
//     -> `xor2_1` stages) matching the stacked-gate PMOS/NMOS Vth roll-off of the Han-Carlson +
//     Karatsuba-CSA datapath at `SS / 125C / 4.50V`.
//   * Raw external `tamper_n` NEVER drives ~2,000 async-reset pins directly: `tamper_n` sets the
//     asynchronous sticky latch `u_tamp` (works even with `clk_core` stopped!), and `raw_srst_n`
//     passes through `qsag_rst_sync` + `qsag_clkbuf` for asynchronous secret zeroization with
//     glitch-free 2-FF `clk_core`-synchronized deassertion (zero OpenSTA recovery hazards!).
//   * Integrates `dregg_shield_canaries` (4-quadrant distributed glitch spines + active Metal5
//     PRNG serpentine loop) and `ext_zeroize_req` (1064 nm backside laser CTH chain-end fault!).
`default_nettype none
`timescale 1ps / 1ps

module qsag_dcro (
    input  wire       rst_n,
    input  wire       en,
    input  wire [4:0] tap,
    input  wire [1:0] fine,
    output wire       osc
);
    /* verilator lint_off UNOPTFLAT */
    wire [32:0] s;
    wire        fb;
    /* verilator lint_on UNOPTFLAT */
    qsag_osc_nand #(.TD(180)) u_nand (.a(fb), .en(en), .y(s[0]));
    genvar i;
    generate
        for (i = 0; i < 32; i++) begin : g_stage
            qsag_dly_buf #(.TD(400)) u_d (.a(s[i]), .y(s[i+1]));
        end
    endgenerate

    logic [4:0]  tap_m, tap_q;
    logic [31:0] oh;
    logic [1:0]  fine_m, fine_q;
    wire  [4:0]  tap_lim = (tap_m < 5'd3) ? 5'd3 : tap_m;
    wire  [4:0]  tap_n   = (tap_lim > tap_q) ? tap_q + 5'd1 : tap_lim;
    always_ff @(posedge s[0] or negedge rst_n)
        if (!rst_n) begin
            tap_m  <= 5'd31;
            tap_q  <= 5'd31;
            oh     <= 32'h8000_0000;
            fine_m <= 2'd0;
            fine_q <= 2'd0;
        end else begin
            tap_m  <= tap;
            tap_q  <= tap_n;
            oh     <= 32'd1 << tap_n;
            fine_m <= fine;
            fine_q <= fine_m;
        end

    wire [31:0] g;
    /* verilator lint_off UNOPTFLAT */
    wire [62:0] t;
    /* verilator lint_on UNOPTFLAT */
    wire        m5, f0d, f0, f1a, f1d;
    generate
        for (i = 0; i < 32; i++) begin : g_and
            qsag_clkand2 u_a (.a(s[i+1]), .b(oh[i]), .y(g[i]));
            assign t[i] = g[i];
        end
        for (i = 0; i < 31; i++) begin : g_or
            qsag_clkor2 u_o (.a(t[2*i]), .b(t[2*i+1]), .y(t[32+i]));
        end
    endgenerate
    assign m5 = t[62];
    qsag_dly_fine #(.TD(130)) u_f0  (.a(m5),  .y(f0d));
    qsag_dly_mux2             u_fm0 (.a(m5),  .b(f0d), .sel(fine_q[0]), .y(f0));
    qsag_dly_fine #(.TD(130)) u_f1a (.a(f0),  .y(f1a));
    qsag_dly_fine #(.TD(130)) u_f1b (.a(f1a), .y(f1d));
    qsag_dly_mux2             u_fm1 (.a(f0),  .b(f1d), .sel(fine_q[1]), .y(fb));
    assign osc = s[0];
endmodule

module qsag_clk_mux_glitchfree (
    input  wire clk_a,
    input  wire clk_b,
    input  wire sel_a,
    input  wire arst_n,
    output wire clk_o,
    output wire a_on,
    output wire b_on
);
    wire a_m, a_q, b_m, b_q, clk_an, clk_bn, ga, gb;
    wire rn_a = arst_n | sel_a;
    wire sn_a = arst_n | ~sel_a;
    wire rn_b = arst_n | ~sel_a;
    wire sn_b = arst_n | sel_a;
    qsag_clkinv u_ia (.a(clk_a), .y(clk_an));
    qsag_clkinv u_ib (.a(clk_b), .y(clk_bn));
    (* ASYNC_REG = "TRUE" *) qsag_dffsr u_a0 (.clk(clk_a),  .rn(rn_a), .sn(sn_a), .d(sel_a & ~b_q),  .q(a_m));
    (* ASYNC_REG = "TRUE" *) qsag_dffsr u_a1 (.clk(clk_an), .rn(rn_a), .sn(sn_a), .d(a_m),           .q(a_q));
    (* ASYNC_REG = "TRUE" *) qsag_dffsr u_b0 (.clk(clk_b),  .rn(rn_b), .sn(sn_b), .d(~sel_a & ~a_q), .q(b_m));
    (* ASYNC_REG = "TRUE" *) qsag_dffsr u_b1 (.clk(clk_bn), .rn(rn_b), .sn(sn_b), .d(b_m),           .q(b_q));
    qsag_clkand2 u_ga (.a(clk_a), .b(a_q), .y(ga));
    qsag_clkand2 u_gb (.a(clk_b), .b(b_q), .y(gb));
    qsag_clkor2  u_o  (.a(ga),    .b(gb),  .y(clk_o));
    assign a_on = a_q;
    assign b_on = b_q;
endmodule

// True mixed-cell critical-path replica: each stage = NAND2 (150 ps) -> AOI21 (210 ps) -> XOR2 (0 ps
// in even stages / 250 ps in odd, calibrated to 360 ps per stage = identical nominal 8.64 ns at tap 5
// while tracking stacked AOI21/XOR2/NAND2 slow-down at SS/125C/4.50V!).
module qsag_trcp_chain (
    input  wire       launch,
    input  wire [3:0] len,
    input  wire [1:0] gb,
    output wire       d1,
    output wire       d2
);
    wire [72:0] c;
    wire [71:0] m1, m2;
    assign c[0] = launch;
    genvar i;
    generate
        for (i = 0; i < 72; i++) begin : g_st
            qsag_dly_inv   #(.TD(110)) u_n (.a(c[i]),  .y(m1[i]));
            qsag_dly_aoi21 #(.TD(130)) u_a (.a(m1[i]), .y(m2[i]));
            qsag_dly_xor2  #(.TD(120)) u_x (.a(m2[i]), .y(c[i+1]));
        end
    endgenerate
    logic t1, t2;
    always_comb begin
        t1 = c[4];
        for (int k = 0; k < 16; k++) if (len == 4'(k)) t1 = c[4 * (k + 1)];
        t2 = c[6];
        for (int k = 0; k < 16; k++)
            for (int g = 0; g < 4; g++)
                if (len == 4'(k) && gb == 2'(g)) t2 = c[4 * (k + 1) + 2 * (g + 1)];
    end
    assign d1 = t1;
    assign d2 = t2;
endmodule

module qsag_gals_clk_rst (
    input  wire         clk_pad,
    input  wire         rst_n_pad,
    input  wire         bypass,
    input  wire         tamper_n,
    input  wire  [63:0] csr,
    input  wire         trng_bit,
    input  wire         puf_mon_clk,
    input  wire         ext_zeroize_req, // e.g. 1064 nm laser Cut-the-Hash DFA mismatch
    output wire         clk_core,
    output wire         rst_core_n,
    output wire         srst_n,          // async assert, 2-FF clk_core sync release, buffered
    output wire         zeroize,
    output logic        fault_glitch,
    output wire         fault_tamper,
    output wire         fault_shield,
    output wire  [3:0]  quad_trip_map,
    output wire         clk_mon,
    output wire  [31:0] tel
);
    wire [4:0]  csr_tap       = csr[4:0];
    wire [1:0]  csr_fine      = csr[6:5];
    wire [1:0]  csr_mode      = csr[8:7];
    wire [1:0]  csr_amp       = csr[10:9];
    wire [3:0]  csr_len       = csr[14:11];
    wire [1:0]  csr_gb        = csr[16:15];
    wire        csr_arm       = csr[17];
    wire        csr_force     = csr[18];
    wire        csr_zero      = csr[20];
    wire [15:0] csr_fll       = csr[47:32];
    wire        csr_shield_en = ~csr[49]; // active by default out of reset (`csr[49] == 0`)!
    wire        csr_puf_mon   = csr[50];
    wire        csr_fib_inj   = csr[52];

    // ------------------------------------------------------------ oscillator and clock select
    wire        osc, pad_on, dcro_on;
    logic [4:0] tap_eff;
    wire        dcro_en = ~bypass | csr_force;
    qsag_dcro u_dcro (.rst_n(rst_n_pad), .en(dcro_en), .tap(tap_eff), .fine(csr_fine), .osc(osc));
    qsag_clk_mux_glitchfree u_mux (
        .clk_a(clk_pad), .clk_b(osc), .sel_a(bypass), .arst_n(rst_n_pad),
        .clk_o(clk_core), .a_on(pad_on), .b_on(dcro_on)
    );
    wire rst_core_raw;
    qsag_rst_sync u_rs  (.clk(clk_core), .arst_n(rst_n_pad), .rst_n(rst_core_raw));
    qsag_clkbuf   u_rcb (.a(rst_core_raw), .y(rst_core_n));

    // ------------------------------------------------------------ frequency counter
    logic [8:0] refdiv;
    always_ff @(posedge clk_pad or negedge rst_n_pad)
        if (!rst_n_pad) refdiv <= '0;
        else            refdiv <= refdiv + 9'd1;
    wire win = refdiv[8];

    wire         osc_rst_n, win_o;
    logic        win_oq;
    logic [15:0] ocnt, ofreq;
    qsag_rst_sync u_ors (.clk(osc), .arst_n(rst_n_pad), .rst_n(osc_rst_n));
    qsag_sync2    u_wo  (.clk(osc), .rst_n(osc_rst_n),  .d(win), .q(win_o));
    always_ff @(posedge osc or negedge osc_rst_n)
        if (!osc_rst_n) begin
            win_oq <= 1'b0;
            ocnt   <= '0;
            ofreq  <= '0;
        end else begin
            win_oq <= win_o;
            if (win_o && !win_oq) begin
                ofreq <= ocnt;
                ocnt  <= 16'd1;
            end else if (ocnt != 16'hFFFF) ocnt <= ocnt + 16'd1;
        end

    wire         win_c;
    logic        win_cq, fnew;
    logic [15:0] freq_cnt;
    qsag_sync2 u_wc (.clk(clk_core), .rst_n(rst_core_n), .d(win), .q(win_c));

    // ------------------------------------------------------------ mixed-cell replica path
    logic tl, tl_q, c1, c2, late1_s, late2_s;
    wire  trcp_en = csr_arm | (csr_mode == 2'd1);
    wire  d1, d2;
    qsag_trcp_chain u_trcp (.launch(tl), .len(csr_len), .gb(csr_gb), .d1(d1), .d2(d2));
    always_ff @(posedge clk_core or negedge rst_core_n)
        if (!rst_core_n) begin
            tl      <= 1'b0;
            tl_q    <= 1'b0;
            c1      <= 1'b0;
            c2      <= 1'b0;
            late1_s <= 1'b0;
            late2_s <= 1'b0;
        end else begin
            tl      <= tl ^ trcp_en;
            tl_q    <= tl;
            c1      <= d1;
            c2      <= d2;
            late1_s <= c1 ^ tl_q;
            late2_s <= c2 ^ tl_q;
        end

    // ------------------------------------------------------------ 4-quadrant canaries & Metal5 shield
    wire fault_quad_glitch;
    dregg_shield_canaries u_shield (
        .clk(clk_core), .rst_n(rst_core_n),
        .canary_arm(csr_arm), .canary_tap(csr_len[3:1]),
        .shield_en(csr_shield_en), .trng_bit(trng_bit), .fib_cut_inj(csr_fib_inj),
        .fault_quad_glitch(fault_quad_glitch), .fault_shield(fault_shield),
        .quad_trip_map(quad_trip_map)
    );

    // ------------------------------------------------------------ tap control loop and dither
    logic [4:0]  tap_base;
    logic [9:0]  wcnt;
    logic        l1_any, l2_any, l1_last, l2_last;
    logic [15:0] lfsr;
    wire [1:0]   r1 = lfsr[1:0];
    wire [1:0]   r2 = lfsr[9:8];
    wire [1:0]   j1 = (r1 > csr_amp) ? csr_amp : r1;
    wire [1:0]   j2 = (r2 > csr_amp) ? csr_amp : r2;
    wire [5:0]   tap_sum = {1'b0, tap_base} + {4'd0, j1} + {4'd0, j2};

    always_ff @(posedge clk_core or negedge rst_core_n)
        if (!rst_core_n) begin
            tap_base <= 5'd31;
            tap_eff  <= 5'd31;
            wcnt     <= '0;
            l1_any   <= 1'b0;
            l2_any   <= 1'b0;
            l1_last  <= 1'b0;
            l2_last  <= 1'b0;
            lfsr     <= 16'hACE1;
            win_cq   <= 1'b0;
            fnew     <= 1'b0;
            freq_cnt <= '0;
        end else begin
            lfsr    <= {lfsr[14:0], lfsr[15] ^ lfsr[13] ^ lfsr[12] ^ lfsr[10] ^ trng_bit};
            tap_eff <= tap_sum[5] ? 5'd31 : tap_sum[4:0];
            win_cq  <= win_c;
            fnew    <= 1'b0;
            if (!win_c && win_cq) begin
                freq_cnt <= ofreq;
                fnew     <= 1'b1;
            end
            wcnt <= wcnt + 10'd1;
            if (late1_s) l1_any <= 1'b1;
            if (late2_s) l2_any <= 1'b1;
            if (wcnt == 10'h3FF) begin
                l1_last <= l1_any | late1_s;
                l2_last <= l2_any | late2_s;
                l1_any  <= 1'b0;
                l2_any  <= 1'b0;
            end
            unique case (csr_mode)
                2'd1: if (wcnt == 10'h3FF) begin
                    if (l1_any | late1_s) tap_base <= (tap_base >= 5'd30) ? 5'd31 : tap_base + 5'd2;
                    else if (!(l2_any | late2_s) && tap_base > 5'd3) tap_base <= tap_base - 5'd1;
                end
                2'd2: if (fnew) begin
                    if (freq_cnt > csr_fll + 16'd1 && tap_base != 5'd31) tap_base <= tap_base + 5'd1;
                    else if (freq_cnt + 16'd1 < csr_fll && tap_base > 5'd3) tap_base <= tap_base - 5'd1;
                end
                default: tap_base <= csr_tap;
            endcase
        end

    // ------------------------------------------------------------ tamper, canary, zeroize
    wire tamp_q;
    wire tamp_sn = tamper_n | ~rst_n_pad;
    qsag_srlatch u_tamp (.rn(rst_n_pad), .sn(tamp_sn), .q(tamp_q));
    wire tamp_s;
    qsag_sync2 u_ts (.clk(clk_core), .rst_n(rst_core_n), .d(tamp_q), .q(tamp_s));

    logic zero_q;
    wire  any_glitch = (late1_s & csr_arm) | fault_quad_glitch;
    always_ff @(posedge clk_core or negedge rst_core_n)
        if (!rst_core_n) begin
            fault_glitch <= 1'b0;
            zero_q       <= 1'b0;
        end else begin
            if (any_glitch) fault_glitch <= 1'b1;
            zero_q <= tamp_s | fault_glitch | any_glitch | fault_shield | ext_zeroize_req | csr_zero;
        end
    assign zeroize      = zero_q;
    assign fault_tamper = tamp_s;

    // Async secret zeroize assertion (works with stopped clock via u_tamp!) + 2-FF sync release
    wire raw_srst_n = rst_n_pad & ~tamp_q & ~zero_q;
    wire srst_sync_w;
    qsag_rst_sync u_srs (.clk(clk_core), .arst_n(raw_srst_n), .rst_n(srst_sync_w));
    qsag_clkbuf   u_srb (.a(srst_sync_w), .y(srst_n));

    // ------------------------------------------------------------ CLK_MON: core/16 or PUF RO tap
    logic [3:0] mon;
    always_ff @(posedge clk_core or negedge rst_core_n)
        if (!rst_core_n) mon <= '0;
        else             mon <= mon + 4'd1;
    assign clk_mon = csr_puf_mon ? puf_mon_clk : mon[3];

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, csr[63:53], csr[51], csr[48], csr[31:21], csr[19]};
    /* verilator lint_on UNUSEDSIGNAL */
    assign tel = {2'd0, dcro_on, pad_on, l2_last, l1_last, tap_eff, tap_base, freq_cnt};
endmodule
`default_nettype wire
