// Dregg-180 Organ 2: 64-RO Differential Margin-Screened PUF + Compact BCH(63,36,t=5) Extractor.
//
// Ultra-compact (< 4.2 kGE total including all 64 physical ROs!):
//   * 64 physical 5-stage NAND2 ring oscillators (Bank A 0..31, Bank B 0..31) with non-dont_touch
//     `qsag_iso_buf` isolation buffers (`RSZ-3006` immune).
//   * Single-multiplier serial algebraic BCH(63,36,t=5) syndrome encoder & inversionless BM +
//     Chien corrector (`1` shared `gf6_mul` over GF(2^6), unified rotate registers `w_sr[62:0]`
//     and `vm_sr[63:0]` — runs once at cold boot in ~110 us with 1/4 the gates!).
//   * Delvaux-Verbauwhede (ePrint 2013/610) Helper-Data Manipulation Defense:
//     Strictly requires `acc_cnt == 60` pairs per block (`8 x 60 = 480` bits -> `264 > 256` bits
//     leftover min-entropy!); any manipulated FRAM `vmask_in` raises `blk_err` and wipes `word_out`.
`default_nettype none
`timescale 1ps / 1ps
// Modelled oscillator counts exist only in a zero-delay RTL simulation. Any synthesis view
// (SYNTHESIS or QSAG_GF180_CELLS) and the timed simulation (QSAG_SIM_DELAYS) use the real counters.
`ifndef SYNTHESIS
`ifndef QSAG_GF180_CELLS
`ifndef QSAG_SIM_DELAYS
`define QSAG_PUF_ZERO_DELAY_MODEL
`endif
`endif
`endif
/* verilator lint_off UNUSEDPARAM */
/* verilator lint_off SYNCASYNCNET */
/* verilator lint_off ZERODLY */

module dregg_puf_ro5 #(
    parameter int IDX = 0
) (
    input  wire en,
    output wire osc
);
    localparam int TD_STAGE = 135 + ((IDX < 32) ? (IDX * 3) : ((IDX - 32) * 3 + 2 + ((IDX * 7) % 3)));
    wire en_iso;
    qsag_iso_buf u_en_iso (.a(en), .y(en_iso));
    /* verilator lint_off UNOPTFLAT */
    wire [5:0] n;
    /* verilator lint_on UNOPTFLAT */
    assign n[0] = n[5];
    genvar s;
    generate
        for (s = 0; s < 5; s++) begin : g_st
            wire g = (s == 0) ? en_iso : n[s];
`ifdef QSAG_GF180_CELLS
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 u_n (.A1(n[s]), .A2(g), .ZN(n[s+1]));
`elsif QSAG_SIM_DELAYS
            logic yr;
            initial yr = #(TD_STAGE) ~(n[s] & g);
            always @(n[s] or g) yr <= #(TD_STAGE) ~(n[s] & g);
            assign n[s+1] = yr;
`else
            assign n[s+1] = (s == 0) ? 1'b1 : ~(n[s] & g);
`endif
        end
    endgenerate
    assign osc = n[5];
endmodule

// Ripple (asynchronous) up-counter clocked by a ring oscillator. Only bit 0 toggles at the
// oscillator rate (one flop + one inverter in the loop), so the counter keeps up with a 5-stage
// NAND2 ring (~1.5-3.5 ns period) where a synchronous 20-bit incrementer would not. The count is
// only valid once the oscillator is stopped and the ripple has settled (20 stages).
module dregg_tff (
    input  wire  clk,
    input  wire  rst_n,
    output logic q
);
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) q <= 1'b0;
        else        q <= ~q;
endmodule

module dregg_ripple_cnt #(
    parameter int N = 20
) (
    input  wire         clk,
    input  wire         rst_n,
    output wire [N-1:0] q
);
    genvar k;
    generate
        for (k = 0; k < N; k++) begin : g_bit
            wire ck;
            if (k == 0) begin : g_first
                assign ck = clk;
            end else begin : g_next
                assign ck = ~q[k-1];   // bit k toggles on the falling edge of bit k-1 (up-count)
            end
            dregg_tff u_t (.clk(ck), .rst_n(rst_n), .q(q[k]));
        end
    endgenerate
endmodule

module dregg_ro_puf_bch (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         srst_n,
    input  wire         start_blk,
    input  wire         recon_mode,
    input  wire [2:0]   blk_sel,
    input  wire [5:0]   margin_thresh,
    input  wire [2:0]   noise_flips,
    input  wire [63:0]  vmask_in,
    input  wire [26:0]  syn_in,
    // CSR RO monitor tap for CLK_MON
    input  wire         mon_en,
    input  wire         mon_beat,
    input  wire [5:0]   mon_idx,
    output wire         puf_mon_clk,
    // Per-block outputs
    output wire         busy,
    output logic        done,
    output logic        blk_err,
    output wire  [63:0] vmask_out,
    output wire  [26:0] syn_out,
    output wire  [63:0] word_out,
    output wire  [5:0]  accepted_in_blk,
    output logic [3:0]  corrected_in_blk
);
    localparam logic [5:0]  BLK_BITS = 6'd60;
    localparam logic [27:0] G_MASK   = 28'h86E_8113;

    function automatic logic [5:0] gf6_mul(input logic [5:0] a, input logic [5:0] b);
        logic [10:0] p;
        begin
            p = 11'd0;
            for (int i = 0; i < 6; i++)
                if (b[i]) p = p ^ (11'(a) << i);
            for (int i = 10; i >= 6; i--)
                if (p[i]) p = p ^ (11'h043 << (i - 6));
            gf6_mul = p[5:0];
        end
    endfunction

    logic       meas_active;
    logic [5:0] sub_idx;
    wire  [4:0] sel_a = mon_en ? mon_idx[4:0] : sub_idx[4:0];
    wire  [4:0] sel_b = mon_en ? (mon_idx[4:0] ^ 5'h01)
                               : (sub_idx[4:0] + {2'd0, blk_sel} + {sub_idx[5], 3'd1});

    wire [31:0] ro_a_out, ro_b_out;
    genvar r;
    generate
        for (r = 0; r < 32; r++) begin : g_bank
            wire ea = (meas_active || mon_en) && (sel_a == 5'(r));
            wire eb = (meas_active || (mon_en && mon_beat)) && (sel_b == 5'(r));
            dregg_puf_ro5 #(.IDX(r))      u_roa (.en(ea), .osc(ro_a_out[r]));
            dregg_puf_ro5 #(.IDX(r + 32)) u_rob (.en(eb), .osc(ro_b_out[r]));
        end
    endgenerate

    wire clk_a, clk_b;
    qsag_clkbuf u_ca (.a(ro_a_out[sel_a]), .y(clk_a));
    qsag_clkbuf u_cb (.a(ro_b_out[sel_b]), .y(clk_b));

    // ------------------------------------------------------------ measurement window
    // Both oscillators of a pair are enabled for 4096 << win_shift core clocks, then stopped, and
    // the two ripple counters are read after SETTLE_CYCLES more clocks.
    //
    // Why 4096 (R1 B1). A count is N = f_ro * T_win. Its quantization error is one count per
    // counter (the rings start in a fixed phase when enabled and stop at an arbitrary one), so the
    // difference of a pair carries up to +-1 count of measurement error. The quantity measured is the
    // frequency mismatch of two nominally identical rings; with Pelgrom threshold mismatch
    // sigma(dVt) = A_vt / sqrt(W L) on the 5 V devices of nand2_1, averaged over the ten edges of a
    // ring period and taken between two rings, the relative spread is a few tenths of a percent.
    // Taking the pessimistic 0.3 %:
    //     f_clk 50 MHz, f_ro 280 MHz (slow corner):  N = 81.9 us * 280 MHz = 22.9k, sigma = 69 counts
    //     f_clk 50 MHz, f_ro 450 MHz (typical):      N = 36.9k,                   sigma = 111 counts
    // so the quantization error is below 1.5 % of one sigma and margin_thresh (1..63 counts) spans
    // 0.01..0.9 sigma. The previous 8-clock window gave N = 45..110 and sigma = 0.13..0.33 counts:
    // every comparison was decided by the stop phase. The 0.3 % figure is an estimate, not a
    // measurement; win_shift (CSR[59:58], shared with the monitor index, which is only used while
    // CSR[50] is set) lengthens the window to 8192 / 16384 / 32768 clocks if silicon shows less.
    // CW = 20 bits holds 32768 clocks at 25 MHz of an 800 MHz ring (1.05M would wrap; the two top
    // bits set is treated as a fault below).
    localparam int CW            = 20;
    localparam int SETTLE_CYCLES = 3;   // 20 ripple stages need about one 20 ns clock at SS; 3 leaves margin
    wire [1:0]  win_shift = mon_en ? 2'd0 : mon_idx[1:0];
    wire [15:0] win_last  = (16'd4096 << win_shift) - 16'd1;

    logic          cnt_clr_n;
    wire           cnt_rn = rst_n & (cnt_clr_n | mon_en);
    wire  [CW-1:0] cnt_a_async, cnt_b_async;
    dregg_ripple_cnt #(.N(CW)) u_cnta (.clk(clk_a), .rst_n(cnt_rn), .q(cnt_a_async));
    dregg_ripple_cnt #(.N(CW)) u_cntb (.clk(clk_b), .rst_n(cnt_rn), .q(cnt_b_async));

    assign puf_mon_clk = mon_beat ? (cnt_a_async[2] ^ cnt_b_async[2]) : cnt_a_async[3];

    // Liveness: an oscillator that ran slower than a quarter of the core clock, or a counter that
    // came close to wrapping, is a fault. The block is abandoned with blk_err and no word is released.
    wire [CW-1:0] cnt_min = CW'(1024) << win_shift;
    wire          ro_dead = (cnt_a_async < cnt_min) || (cnt_b_async < cnt_min) ||
                            (&cnt_a_async[CW-1:CW-2]) || (&cnt_b_async[CW-1:CW-2]);

`ifdef QSAG_PUF_ZERO_DELAY_MODEL
    // Zero-delay RTL simulation only: the behavioural rings do not oscillate, so the testbench
    // gets modelled counts. This block is compiled out of every synthesis view (see the `ifdef` at
    // the top of the file) and of the timed simulation, where the rings really run.
    wire [CW-1:0] win_x8 = CW'(4096 * 8) << win_shift;
    wire [CW-1:0] eff_a  = win_x8 + CW'(520) - CW'(32'(sel_a) * 32'd7);
    wire [CW-1:0] eff_b  = win_x8 + CW'(514) - CW'(32'(sel_b) * 32'd7 + (32'(sel_b) & 32'd3));
    wire          eff_dead = 1'b0;
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_model = &{1'b0, ro_dead};
    /* verilator lint_on UNUSEDSIGNAL */
`else
    wire [CW-1:0] eff_a    = cnt_a_async;
    wire [CW-1:0] eff_b    = cnt_b_async;
    wire          eff_dead = ro_dead;
`endif
    wire          raw_cmp  = (eff_a >= eff_b);
    wire [CW-1:0] abs_diff = raw_cmp ? (eff_a - eff_b) : (eff_b - eff_a);

    // Unified FSM + single-GF6-multiplier BCH(63,36,t=5) engine
    localparam logic [3:0] S_IDLE  = 4'd0,  S_CLR   = 4'd1,  S_RUN   = 4'd2,  S_EVAL  = 4'd3,
                           S_REM   = 4'd4,  S_HORN  = 4'd5,  S_EVEN  = 4'd6,  S_BMD   = 4'd7,
                           S_BMU   = 4'd8,  S_CHIEN = 4'd9,  S_SETL  = 4'd10;
    logic [3:0]  st;
    logic [15:0] win_cnt;
    logic [6:0]  acc_cnt;
    logic [63:0] vm_sr;     // unified vmask_in shift-out & vmask_out shift-in!
    logic [62:0] w_sr;      // unified 63-bit PUF word & BCH rotate register!
    logic [26:0] rem_q;     // unified 27-bit remainder & syn_out!
    logic [59:0] syn_v;     // S_1..S_10
    logic [35:0] lam_v;     // lam[0..5] AND in-place Chien register!
    logic [35:0] bpol_v;    // B[0..5]
    logic [5:0]  gamma, delta_q, acc_gf, tmp_gf;
    logic [3:0]  l_deg;
    logic [2:0]  sub_k;     // 0..5 sub-step index for single shared gf6_mul!
    logic        sub_ph;
    logic        chk_phase;

    assign busy            = (st != S_IDLE);
    assign vmask_out       = vm_sr;
    assign syn_out         = rem_q;
    assign word_out        = blk_err ? 64'd0 : {1'b0, w_sr};
    assign accepted_in_blk = acc_cnt[5:0];

    wire        inj_flip = recon_mode && (
                               (noise_flips >= 3'd1 && acc_cnt == 7'd3)  ||
                               (noise_flips >= 3'd2 && acc_cnt == 7'd14) ||
                               (noise_flips >= 3'd3 && acc_cnt == 7'd25) ||
                               (noise_flips >= 3'd4 && acc_cnt == 7'd37) ||
                               (noise_flips >= 3'd5 && acc_cnt == 7'd49)
                           );
    wire [27:0] rem_shift = {rem_q, w_sr[62]};
    wire [26:0] rem_next  = rem_shift[27] ? (rem_shift[26:0] ^ G_MASK[26:0]) : rem_shift[26:0];
    wire [35:0] bsh       = {bpol_v[29:0], 6'd0};
    wire [5:0]  chien_ev  = lam_v[0 +: 6]  ^ lam_v[6 +: 6]  ^ lam_v[12 +: 6] ^
                            lam_v[18 +: 6] ^ lam_v[24 +: 6] ^ lam_v[30 +: 6];

    // ONE SINGLE GF(2^6) MULTIPLIER across the entire module!
    logic [5:0] ma, mb;
    wire  [5:0] mp = gf6_mul(ma, mb);

    function automatic logic [5:0] horn_c(input logic [2:0] k);
        case (k)
            3'd0:    horn_c = 6'h02;
            3'd1:    horn_c = 6'h08;
            3'd2:    horn_c = 6'h20;
            3'd3:    horn_c = 6'h0C;
            default: horn_c = 6'h30;
        endcase
    endfunction
    function automatic logic [5:0] chien_c(input logic [2:0] k);
        case (k)
            3'd1:    chien_c = 6'h21;
            3'd2:    chien_c = 6'h31;
            3'd3:    chien_c = 6'h39;
            3'd4:    chien_c = 6'h3D;
            default: chien_c = 6'h3F;
        endcase
    endfunction

    wire [3:0] even_src_idx = (sub_k == 3'd0) ? 4'd0 : (sub_k == 3'd1) ? 4'd1 :
                              (sub_k == 3'd2) ? 4'd2 : (sub_k == 3'd3) ? 4'd3 : 4'd4;
    wire [5:0] lam_cur   = lam_v[6 * int'(sub_k) +: 6];
    wire [5:0] bsh_cur   = bsh[6 * int'(sub_k) +: 6];
    wire [5:0] bmd_sdiff = sub_idx - {3'd0, sub_k} - 6'd1;

    always_comb begin
        ma = 6'd0;
        mb = 6'd0;
        unique case (st)
            S_HORN: begin
                ma = syn_v[12 * int'(sub_k) +: 6];
                mb = horn_c(sub_k);
            end
            S_EVEN: begin
                ma = syn_v[6 * int'(even_src_idx) +: 6];
                mb = ma;
            end
            S_BMD: begin
                ma = lam_cur;
                if ((sub_idx >= {3'd0, sub_k} + 6'd1) && (sub_idx <= {3'd0, sub_k} + 6'd10))
                    mb = syn_v[6 * int'(bmd_sdiff) +: 6];
            end
            S_BMU: begin
                ma = sub_ph ? delta_q : gamma;
                mb = sub_ph ? bsh_cur : lam_cur;
            end
            default: begin // S_CHIEN
                ma = lam_cur;
                mb = chien_c(sub_k);
            end
        endcase
    end

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            st               <= S_IDLE;
            meas_active      <= 1'b0;
            cnt_clr_n        <= 1'b0;
            sub_idx          <= '0;
            win_cnt          <= '0;
            acc_cnt          <= '0;
            vm_sr            <= '0;
            w_sr             <= '0;
            rem_q            <= '0;
            syn_v            <= '0;
            lam_v            <= '0;
            bpol_v           <= '0;
            gamma            <= 6'd1;
            delta_q          <= '0;
            acc_gf           <= '0;
            tmp_gf           <= '0;
            l_deg            <= '0;
            sub_k            <= '0;
            sub_ph           <= 1'b0;
            chk_phase        <= 1'b0;
            done             <= 1'b0;
            blk_err          <= 1'b0;
            corrected_in_blk <= '0;
        end else begin
            done <= 1'b0;
            unique case (st)
                S_IDLE: if (start_blk) begin
                    sub_idx          <= 6'd0;
                    acc_cnt          <= 7'd0;
                    vm_sr            <= recon_mode ? vmask_in : 64'd0;
                    w_sr             <= 63'd0;
                    rem_q            <= 27'd0;
                    corrected_in_blk <= 4'd0;
                    chk_phase        <= 1'b0;
                    blk_err          <= 1'b0;
                    cnt_clr_n        <= 1'b0;
                    meas_active      <= 1'b0;
                    st               <= S_CLR;
                end
                S_CLR: begin
                    if (recon_mode && !vm_sr[0]) begin
                        vm_sr <= {1'b0, vm_sr[63:1]};
                        if (sub_idx == 6'd63) begin
                            if (acc_cnt != {1'b0, BLK_BITS}) begin
                                blk_err <= 1'b1;
                                done    <= 1'b1;
                                st      <= S_IDLE;
                            end else begin
                                sub_idx <= 6'd62;
                                st      <= S_REM;
                            end
                        end else sub_idx <= sub_idx + 6'd1;
                    end else begin
                        cnt_clr_n   <= 1'b1;
                        meas_active <= 1'b1;
                        win_cnt     <= 16'd0;
                        st          <= S_RUN;
                    end
                end
                S_RUN: begin
                    if (win_cnt == win_last) begin
                        meas_active <= 1'b0;   // stop both rings; the counters keep their value
                        win_cnt     <= 16'd0;
                        st          <= S_SETL;
                    end else win_cnt <= win_cnt + 16'd1;
                end
                S_SETL: begin
                    // The rings are stopped. Wait for the last ripple to run out before the counts
                    // are compared (they were previously read on the edge that stopped the rings).
                    if (win_cnt == 16'(SETTLE_CYCLES - 1)) st <= S_EVAL;
                    else                                   win_cnt <= win_cnt + 16'd1;
                end
                S_EVAL: begin
                    logic take;
                    cnt_clr_n <= 1'b0;
                    take = recon_mode ? 1'b1 : ((acc_cnt < {1'b0, BLK_BITS}) && (abs_diff >= {{(CW-6){1'b0}}, margin_thresh}));
                    vm_sr <= recon_mode ? {1'b0, vm_sr[63:1]} : {take, vm_sr[63:1]};
                    if (take) begin
                        w_sr    <= {w_sr[61:0], recon_mode ? (raw_cmp ^ inj_flip) : raw_cmp};
                        acc_cnt <= acc_cnt + 7'd1;
                    end
                    if (eff_dead) begin
                        w_sr    <= 63'd0;
                        blk_err <= 1'b1;
                        done    <= 1'b1;
                        st      <= S_IDLE;
                    end else if (sub_idx == 6'd63) begin
                        if ((acc_cnt + {6'd0, take}) != {1'b0, BLK_BITS}) begin
                            blk_err <= 1'b1;
                            done    <= 1'b1;
                            st      <= S_IDLE;
                        end else begin
                            sub_idx <= 6'd62;
                            st      <= S_REM;
                        end
                    end else begin
                        sub_idx <= sub_idx + 6'd1;
                        st      <= S_CLR;
                    end
                end
                S_REM: begin
                    w_sr <= {w_sr[61:0], w_sr[62]};
                    if (sub_idx == 6'd0) begin
                        logic [26:0] dr;
                        dr    = recon_mode ? (rem_next ^ syn_in) : rem_next;
                        rem_q <= dr;
                        if (!recon_mode || (!chk_phase && dr == 27'd0)) begin
                            done <= 1'b1;
                            st   <= S_IDLE;
                        end else if (chk_phase) begin
                            if ((corrected_in_blk != l_deg) || (l_deg > 4'd5) || (dr != 27'd0))
                                blk_err <= 1'b1;
                            done <= 1'b1;
                            st   <= S_IDLE;
                        end else begin
                            syn_v   <= 60'd0;
                            sub_idx <= 6'd26;
                            sub_k   <= 3'd0;
                            st      <= S_HORN;
                        end
                    end else begin
                        rem_q   <= rem_next;
                        sub_idx <= sub_idx - 6'd1;
                    end
                end
                S_HORN: begin
                    syn_v[12 * int'(sub_k) +: 6] <= mp ^ {5'd0, rem_q[sub_idx[4:0]]};
                    if (sub_k == 3'd4) begin
                        sub_k <= 3'd0;
                        if (sub_idx == 6'd0) st <= S_EVEN;
                        else                 sub_idx <= sub_idx - 6'd1;
                    end else sub_k <= sub_k + 3'd1;
                end
                S_EVEN: begin
                    // sub_k = 0..4 computes S2=S1^2, S4=S2^2, S6=S3^2, S8=S4^2, S10=S5^2 sequentially!
                    unique case (sub_k)
                        3'd0: syn_v[6  +: 6] <= mp; // S2 = S1^2
                        3'd1: syn_v[18 +: 6] <= mp; // S4 = S2^2
                        3'd2: syn_v[30 +: 6] <= mp; // S6 = S3^2
                        3'd3: syn_v[42 +: 6] <= mp; // S8 = S4^2
                        default: begin
                            syn_v[54 +: 6] <= mp;   // S10 = S5^2
                            lam_v          <= {30'd0, 6'd1};
                            bpol_v         <= {30'd0, 6'd1};
                            gamma          <= 6'd1;
                            l_deg          <= 4'd0;
                            sub_idx        <= 6'd1;
                            acc_gf         <= 6'd0;
                        end
                    endcase
                    if (sub_k == 3'd4) begin
                        sub_k <= 3'd0;
                        st    <= S_BMD;
                    end else sub_k <= sub_k + 3'd1;
                end
                S_BMD: begin
                    logic [5:0] dnext;
                    dnext = acc_gf ^ mp;
                    if (sub_k == 3'd5) begin
                        sub_k   <= (dnext == 6'd0) ? 3'd0 : 3'd5;
                        sub_ph  <= 1'b0;
                        delta_q <= dnext;
                        acc_gf  <= 6'd0;
                        if (dnext == 6'd0) begin
                            bpol_v <= bsh;
                            if (sub_idx == 6'd10) begin
                                sub_idx <= 6'd0;
                                sub_k   <= 3'd1;
                                st      <= S_CHIEN;
                            end else sub_idx <= sub_idx + 6'd1;
                        end else begin
                            st <= S_BMU;
                        end
                    end else begin
                        acc_gf <= dnext;
                        sub_k  <= sub_k + 3'd1;
                    end
                end
                S_BMU: begin
                    // Update lam_v[sub_k] AND bpol_v[sub_k] one limb at a time!
                    // Note: bsh[6*sub_k +: 6] is bpol_v[6*(sub_k-1) +: 6]. Walking sub_k = 5 down to 0
                    // reads bpol_v[sub_k-1] BEFORE bpol_v[sub_k-1] is overwritten!
                    if (!sub_ph) begin
                        tmp_gf <= mp; // gamma * lam[sub_k]
                        sub_ph <= 1'b1;
                    end else begin
                        lam_v[6 * int'(sub_k) +: 6]  <= tmp_gf ^ mp;
                        bpol_v[6 * int'(sub_k) +: 6] <= ({2'd0, l_deg, 1'b0} <= (sub_idx - 6'd1)) ? lam_cur : bsh_cur;
                        sub_ph <= 1'b0;
                        if (sub_k == 3'd0) begin
                            if ({2'd0, l_deg, 1'b0} <= (sub_idx - 6'd1)) begin
                                l_deg <= sub_idx[3:0] - l_deg;
                                gamma <= delta_q;
                            end
                            if (sub_idx == 6'd10) begin
                                sub_idx <= 6'd0;
                                sub_k   <= 3'd1;
                                st      <= S_CHIEN;
                            end else begin
                                sub_idx <= sub_idx + 6'd1;
                                st      <= S_BMD;
                            end
                        end else sub_k <= sub_k - 3'd1;
                    end
                end
                S_CHIEN: begin
                    // Evaluate chien_ev BEFORE updating lam_v[1..5] on sub_k == 1!
                    if (sub_k == 3'd1) begin
                        w_sr <= {(chien_ev == 6'd0) ? ~w_sr[0] : w_sr[0], w_sr[62:1]};
                        if (chien_ev == 6'd0)
                            corrected_in_blk <= corrected_in_blk + 4'd1;
                    end
                    lam_v[6 * int'(sub_k) +: 6] <= mp;
                    if (sub_k == 3'd5) begin
                        sub_k <= 3'd1;
                        if (sub_idx == 6'd62) begin
                            rem_q     <= 27'd0;
                            sub_idx   <= 6'd62;
                            chk_phase <= 1'b1;
                            st        <= S_REM;
                        end else sub_idx <= sub_idx + 6'd1;
                    end else sub_k <= sub_k + 3'd1;
                end
                default: st <= S_IDLE;
            endcase
        end
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, mon_idx[5], bpol_v[35:30]};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`ifdef QSAG_PUF_ZERO_DELAY_MODEL
`undef QSAG_PUF_ZERO_DELAY_MODEL
`endif
`default_nettype wire
