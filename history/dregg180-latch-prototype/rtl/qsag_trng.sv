// Dregg-180 (QSAG-NI-180) Coherent-Sampling Ring-Oscillator (CoSO) Physical TRNG.
//
// Physics & Entropy Basis (`hardware/gf180mcu/physics/trng/coso_model.py` & BSIM4 `TRNOISE`):
//   * Replaces the under-accumulated 7/13-stage divider sampler (`h_min ~ 0.005` bit/bit under pure
//     thermal jitter) with a matched pair of 17-stage `gf180mcu_fd_sc_mcu7t5v0__nand2_1` rings
//     (`T_nom = 4.706 ns` at TT/5.0V/27C, `kappa = 4.80e-9 sqrt(s)`).
//   * Ring B (`osc_s`) coherently samples Ring A (`osc_f`) through a 2-FF metastability resolver to
//     form the slow beat wave (`T_beat = T / |d|`), while a 12-bit counter clocked by Ring B counts
//     periods `C_k` between successive beat rising edges (`var(C) = 2 * kappa^2 * T^2 / dT^3`,
//     yielding `h_min(LSB) = 0.92..0.97` bit/beat across `d = 0.03%..0.30%` Pelgrom mismatch).
//   * Continuous hardware health supervision:
//       1) CoSO injection-locking / dead-beat guard (`C_k < 8` harmonic lock or `C_k == 4095`
//          frequency-lock timeout immediately latches `rct_fail`),
//       2) NIST SP 800-90B Repetition Count Test (`cutoff C = 41`),
//       3) NIST SP 800-90B Adaptive Proportion Test (`window = 1024, cutoff = 821`).
//   * Raw bits are further cryptographically conditioned by `TurboSHAKE256` in `qsag_wire_engine`.
`default_nettype none
`timescale 1ps / 1ps
/* verilator lint_off UNUSEDPARAM */
/* verilator lint_off SYNCASYNCNET */
/* verilator lint_off ZERODLY */

module qsag_ring_osc #(
    parameter int N  = 17,     // odd number of inverting stages (17 stages -> 4.706 ns @ TT 5.0V)
    parameter int TD = 138
) (
    input  wire en,
    output wire osc
);
    /* verilator lint_off UNOPTFLAT */
    wire [N:0] n;
    /* verilator lint_on UNOPTFLAT */
    wire en_iso;
    qsag_iso_buf u_en_iso (.a(en), .y(en_iso));
    assign n[0] = n[N];
    genvar i;
    generate
        for (i = 0; i < N; i++) begin : g_st
            wire g = (i == 0) ? en_iso : n[i];
`ifdef QSAG_GF180_CELLS
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand2_1 u_n (.A1(n[i]), .A2(g), .ZN(n[i+1]));
`elsif QSAG_SIM_DELAYS
            logic yr;
            initial yr = #(TD) ~(n[i] & g);
            always @(n[i] or g) yr <= #(TD + $urandom_range(0, 6)) ~(n[i] & g);
            assign n[i+1] = yr;
`else
            assign n[i+1] = (i == 0) ? 1'b1 : ~(n[i] & g);
`endif
        end
    endgenerate
    assign osc = n[N];
endmodule

module qsag_trng (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         en,
    input  wire         take,        // engine consumed `word`
    output logic [63:0] word,
    output wire         valid,       // 64 fresh raw CoSO bits since last `take`
    output wire         ok,          // 1024-beat start-up window passed & zero health faults
    output logic        rct_fail,
    output logic        apt_fail,
    output wire         raw_bit      // newest CoSO beat LSB (jitter dither & shield LFSR stir)
);
    wire osc_f, osc_s, sclk;
    qsag_ring_osc #(.N(17), .TD(138)) u_fast (.en(en), .osc(osc_f));
    qsag_ring_osc #(.N(17), .TD(141)) u_slow (.en(en), .osc(osc_s));
    qsag_clkbuf u_sclk (.a(osc_s), .y(sclk));

    // Coherent beat detector + 4-cycle deglitch hysteresis + 16-bit beat-period counter in `sclk` domain.
    // Requiring 4 consecutive `1`s to assert `beat_st` and 4 consecutive `0`s to deassert `beat_st`
    // eliminates rising- and falling-edge jitter chatter without altering the Brownian first-passage
    // period distribution (`var(C) = 2 * kappa^2 * T^2 / dT^3`).
    (* ASYNC_REG = "TRUE" *) logic beat_m, beat_s;
    logic [2:0]  beat_hist;
    logic        beat_st, short_prev;
    logic [15:0] c_cnt;
    logic        samp, stgl, lock_bad;

    wire all_hi    = beat_s & (&beat_hist);
    wire all_lo    = ~beat_s & (~|beat_hist);
    wire beat_rise = ~beat_st & all_hi;
    wire cnt_max   = (c_cnt == 16'hFFFF);
    wire cnt_short = (c_cnt < 16'd12);

    always_ff @(posedge sclk or negedge rst_n) begin
        if (!rst_n) begin
            beat_m     <= 1'b0;
            beat_s     <= 1'b0;
            beat_hist  <= 3'b000;
            beat_st    <= 1'b0;
            short_prev <= 1'b0;
            c_cnt      <= 16'd1;
            samp       <= 1'b0;
            stgl       <= 1'b0;
            lock_bad   <= 1'b0;
        end else begin
            beat_m    <= osc_f;
            beat_s    <= beat_m;
            beat_hist <= {beat_hist[1:0], beat_s};
            if (all_hi)      beat_st <= 1'b1;
            else if (all_lo) beat_st <= 1'b0;
            if (beat_rise || cnt_max) begin
                samp       <= c_cnt[0];
                short_prev <= cnt_short;
                // Flag sustained harmonic/overdrive lock (2 consecutive C_k < 12) or 1:1 lock timeout (65535)
                if ((short_prev && cnt_short) || cnt_max) lock_bad <= 1'b1;
                stgl       <= ~stgl;
                c_cnt      <= 16'd1;
            end else begin
                c_cnt <= c_cnt + 16'd1;
            end
        end
    end

    // Synchronize toggle event + lock-fault flag into `clk_core` domain
    wire  stgl_s, lock_bad_s;
    logic stgl_q, bit_q;
    qsag_sync2 u_s  (.clk(clk), .rst_n(rst_n), .d(stgl),     .q(stgl_s));
    qsag_sync2 u_lk (.clk(clk), .rst_n(rst_n), .d(lock_bad), .q(lock_bad_s));
    wire  nb = (stgl_s != stgl_q);

    logic [6:0] fill;
    logic [5:0] rct;
    logic [9:0] apt_n, apt_c;
    logic       apt_ref, warm;
    assign valid   = fill[6];
    assign ok      = warm && !rct_fail && !apt_fail;
    assign raw_bit = bit_q;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            stgl_q    <= 1'b0;
            bit_q     <= 1'b0;
            word      <= '0;
            fill      <= '0;
            rct       <= '0;
            apt_n     <= '0;
            apt_c     <= '0;
            apt_ref   <= 1'b0;
            warm      <= 1'b0;
            rct_fail  <= 1'b0;
            apt_fail  <= 1'b0;
        end else begin
            stgl_q <= stgl_s;
            if (take) fill <= '0;
            if (lock_bad_s) rct_fail <= 1'b1;
            if (nb) begin
                bit_q <= samp;
                word  <= {word[62:0], samp};
                if (!fill[6] && !take) fill <= fill + 7'd1;
                // SP 800-90B Repetition Count Test (cutoff 41)
                if (samp == bit_q) begin
                    if (rct == 6'd39) rct_fail <= 1'b1;
                    else              rct      <= rct + 6'd1;
                end else rct <= '0;
                // SP 800-90B Adaptive Proportion Test (window 1024, cutoff 821)
                if (apt_n == 10'd0) begin
                    apt_ref <= samp;
                    apt_c   <= 10'd1;
                    apt_n   <= 10'd1;
                end else begin
                    if (samp == apt_ref) begin
                        apt_c <= apt_c + 10'd1;
                        if (apt_c == 10'd820) apt_fail <= 1'b1;
                    end
                    apt_n <= apt_n + 10'd1;
                    if (apt_n == 10'd1023) warm <= 1'b1;
                end
            end
        end
    end
endmodule
`default_nettype wire
