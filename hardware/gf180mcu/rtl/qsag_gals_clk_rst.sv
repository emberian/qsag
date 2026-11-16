// QSAG-NI-180 clocking, reset and physical-fault unit.
//
//   clk_core = EXT_CLK_BYPASS ? clk_pad : DCRO          (glitch-free, interlocked switch-over)
//
//   DCRO   ring oscillator: enable NAND + 32 delay stages + one-hot AND-OR tap select + 2 fine
//          stages. The select is registered on the ring's own edge and moves up by at most one
//          tap per cycle (down by any amount), which keeps the feedback node glitch-free.
//   TRCP   tunable replica critical path. While the replica loop or the canary is enabled, a
//          toggle launched every cycle travels through a
//          replica chain (tap `trcp_len`) and then a guard chain (`trcp_gb`):
//              late1 = the replica missed the cycle   -> clock too fast / clock glitch
//              late2 = replica + guard missed         -> inside the guard band (locked)
//          Loop mode 1 walks the DCRO tap until late2 fires and late1 does not.
//   FLL    loop mode 2 holds freq_cnt (core cycles per 512 clk_pad cycles) at `fll_target`.
//   Dither tap += d1 + d2, d1, d2 in [0, amp] from an LFSR stirred with raw TRNG bits; only
//          ever slower than the locked tap, so it never eats timing margin.
//   Canary when armed, late1 raises `zeroize` (the replica is the 15 % over-margined path).
//
// CSR fields (wire engine `csr`):
//   [4:0] tap  [6:5] fine  [8:7] loop mode (0 manual, 1 TRCP, 2 FLL)  [10:9] dither amplitude
//   [14:11] trcp_len  [16:15] trcp_gb  [17] canary arm  [18] DCRO force on  [19] pad slew slow
//   [20] zeroize command  [24:21] anchor SPI divider  [25] TRNG enable  [47:32] FLL target
`default_nettype none
`timescale 1ps / 1ps

module qsag_dcro (
    input  wire       rst_n,
    input  wire       en,
    input  wire [4:0] tap,      // requested tap (any domain, quasi-static or core-synchronous)
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

    // Tap select: registered one-hot, AND-OR combined, updated on the ring's own rising edge.
    // At that instant the low half-wave has passed every tap up to the selected one and, during
    // the return path through the fine stages and the NAND, at least the next tap as well. The
    // select may therefore move down by any amount but up by one tap per cycle only: the tap
    // being left and the tap being entered are both low, and no other AND gate is enabled, so
    // the feedback node cannot glitch whatever the skew between the select flops.
    logic [4:0]  tap_m, tap_q;
    logic [31:0] oh;                  // oh[i] selects s[i+1]
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
    wire [62:0] t;                    // OR tree: t[0..31] leaves, t[62] root
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
    // fine steps of one and two plain buffers (shorter than the mux + NAND that follow them,
    // so a fine change at the ring edge also finds both multiplexer inputs low)
    qsag_dly_fine #(.TD(130)) u_f0 (.a(m5), .y(f0d));
    qsag_dly_mux2 u_fm0 (.a(m5), .b(f0d), .sel(fine_q[0]), .y(f0));
    qsag_dly_fine #(.TD(130)) u_f1a (.a(f0),  .y(f1a));
    qsag_dly_fine #(.TD(130)) u_f1b (.a(f1a), .y(f1d));
    qsag_dly_mux2 u_fm1 (.a(f0), .b(f1d), .sel(fine_q[1]), .y(fb));
    assign osc = s[0];
endmodule

// Glitch-free two-input clock multiplexer. Each leg is enabled by two flip-flops (rising then
// falling edge of its own clock) and may only turn on once the other leg has turned off, so
// the output is always whole pulses of one clock. Out of reset the legs already match `sel`,
// so a board with only one of the two clocks present starts correctly.
module qsag_clk_mux_glitchfree (
    input  wire clk_a,
    input  wire clk_b,
    input  wire sel_a,      // 1: clk_a
    input  wire arst_n,
    output wire clk_o,
    output wire a_on,
    output wire b_on
);
    wire a_m, a_q, b_m, b_q, clk_an, clk_bn, ga, gb;
    wire rn_a = arst_n | sel_a;       // reset when in reset and not selected
    wire sn_a = arst_n | ~sel_a;      // set when in reset and selected
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
    qsag_clkor2  u_o  (.a(ga), .b(gb), .y(clk_o));
    assign a_on = a_q;
    assign b_on = b_q;
endmodule

// Replica delay chain: 64 stages of two NAND2 (the dominant cell of the mapped datapath),
// 16 taps, then a guard chain of 2/4/6/8 further stages.
module qsag_trcp_chain (
    input  wire       launch,
    input  wire [3:0] len,
    input  wire [1:0] gb,
    output wire       d1,
    output wire       d2
);
    wire [72:0] c;
    wire [71:0] h;
    assign c[0] = launch;
    genvar i;
    generate
        for (i = 0; i < 72; i++) begin : g_st
            qsag_dly_inv #(.TD(180)) u_a (.a(c[i]), .y(h[i]));
            qsag_dly_inv #(.TD(180)) u_b (.a(h[i]), .y(c[i+1]));
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
    input  wire         bypass,          // inputs[0] EXT_CLK_BYPASS
    input  wire         tamper_n,        // TAMPER_ZEROIZE_N pad
    input  wire  [63:0] csr,
    input  wire         trng_bit,
    output wire         clk_core,
    output wire         rst_core_n,
    output wire         srst_n,          // asynchronous secret clear
    output wire         zeroize,         // level, core domain
    output logic        fault_glitch,
    output wire         fault_tamper,
    output wire         clk_mon,
    output wire  [31:0] tel
);
    wire [4:0]  csr_tap   = csr[4:0];
    wire [1:0]  csr_fine  = csr[6:5];
    wire [1:0]  csr_mode  = csr[8:7];
    wire [1:0]  csr_amp   = csr[10:9];
    wire [3:0]  csr_len   = csr[14:11];
    wire [1:0]  csr_gb    = csr[16:15];
    wire        csr_arm   = csr[17];
    wire        csr_force = csr[18];
    wire        csr_zero  = csr[20];
    wire [15:0] csr_fll   = csr[47:32];

    // ------------------------------------------------------------ oscillator and clock select
    wire        osc, pad_on, dcro_on;
    logic [4:0] tap_eff;
    wire        dcro_en = ~bypass | csr_force;
    qsag_dcro u_dcro (.rst_n(rst_n_pad), .en(dcro_en), .tap(tap_eff), .fine(csr_fine), .osc(osc));
    qsag_clk_mux_glitchfree u_mux (
        .clk_a(clk_pad), .clk_b(osc), .sel_a(bypass), .arst_n(rst_n_pad),
        .clk_o(clk_core), .a_on(pad_on), .b_on(dcro_on)
    );
    qsag_rst_sync u_rs (.clk(clk_core), .arst_n(rst_n_pad), .rst_n(rst_core_n));

    // ------------------------------------------------------------ frequency counter
    // window = 512 clk_pad cycles; DCRO cycles counted in the oscillator's own domain
    logic [8:0] refdiv;
    always_ff @(posedge clk_pad or negedge rst_n_pad)
        if (!rst_n_pad) refdiv <= '0;
        else refdiv <= refdiv + 9'd1;
    wire win = refdiv[8];

    wire         osc_rst_n, win_o;
    logic        win_oq;
    logic [15:0] ocnt, ofreq;
    qsag_rst_sync u_ors (.clk(osc), .arst_n(rst_n_pad), .rst_n(osc_rst_n));
    qsag_sync2 u_wo (.clk(osc), .rst_n(osc_rst_n), .d(win), .q(win_o));
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

    // the core takes the count half a window after the oscillator domain wrote it
    wire         win_c;
    logic        win_cq, fnew;
    logic [15:0] freq_cnt;
    qsag_sync2 u_wc (.clk(clk_core), .rst_n(rst_core_n), .d(win), .q(win_c));

    // ------------------------------------------------------------ replica path
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
            tl      <= tl ^ trcp_en;   // the replica only toggles while something observes it
            tl_q    <= tl;
            c1      <= d1;
            c2      <= d2;
            late1_s <= c1 ^ tl_q;
            late2_s <= c2 ^ tl_q;
        end

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
                2'd1: if (wcnt == 10'h3FF) begin  // replica loop
                    if (l1_any | late1_s) tap_base <= (tap_base >= 5'd30) ? 5'd31 : tap_base + 5'd2;
                    else if (!(l2_any | late2_s) && tap_base > 5'd3) tap_base <= tap_base - 5'd1;
                end
                2'd2: if (fnew) begin             // frequency lock (bang-bang, +/-1 dead band)
                    if (freq_cnt > csr_fll + 16'd1 && tap_base != 5'd31) tap_base <= tap_base + 5'd1;
                    else if (freq_cnt + 16'd1 < csr_fll && tap_base > 5'd3) tap_base <= tap_base - 5'd1;
                end
                default: tap_base <= csr_tap;
            endcase
        end

    // ------------------------------------------------------------ tamper, canary, zeroize
    // tamper latch: asynchronous set straight from the pad (works with the clock stopped)
    wire tamp_q;
    wire tamp_sn = tamper_n | ~rst_n_pad;
    qsag_srlatch u_tamp (.rn(rst_n_pad), .sn(tamp_sn), .q(tamp_q));
    wire  tamp_s;
    qsag_sync2 u_ts (.clk(clk_core), .rst_n(rst_core_n), .d(tamp_q), .q(tamp_s));
    logic zero_q;
    always_ff @(posedge clk_core or negedge rst_core_n)
        if (!rst_core_n) begin
            fault_glitch <= 1'b0;
            zero_q       <= 1'b0;
        end else begin
            if (late1_s && csr_arm) fault_glitch <= 1'b1;
            zero_q <= tamp_s | fault_glitch | (late1_s & csr_arm) | csr_zero;
        end
    assign zeroize      = zero_q;
    assign fault_tamper = tamp_s;
    // keys and the other secret registers clear asynchronously on reset and on the raw tamper
    // pad, and one clock after any synchronous cause
    assign srst_n = rst_core_n & tamper_n & ~zero_q;

    // ------------------------------------------------------------ CLK_MON = clk_core / 16
    logic [3:0] mon;
    always_ff @(posedge clk_core or negedge rst_core_n)
        if (!rst_core_n) mon <= '0;
        else mon <= mon + 4'd1;
    assign clk_mon = mon[3];

    wire unused = &{1'b0, csr[63:48], csr[31:21], csr[19]};
    assign tel = {2'd0, dcro_on, pad_on, l2_last, l1_last, tap_eff, tap_base, freq_cnt};
endmodule
`default_nettype wire
