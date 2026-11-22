module qsag_trng #(parameter int VAT_ID = 0) (
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
    logic bit_q;
`ifdef ASS2_FAST_ENTROPY
    // Deterministic beat source for cycle simulations. Keep real RCT/APT and word packing.
    logic [15:0] fixture_q;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) fixture_q <= 16'(1 + VAT_ID);
        else if (en) fixture_q <= {fixture_q[14:0], ^(fixture_q & 16'hb400)};
    wire samp = fixture_q[0];
    wire nb = en;
    wire lock_bad_s = 1'b0;
`else
    wire osc_f, sclk;
    qsag_ass2_ring #(.STAGES(17)) u_fast (.en(en), .osc(osc_f));
    qsag_ass2_ring #(.STAGES(17)) u_slow (.en(en), .osc(sclk));


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
    (* async_reg = "true" *) logic [1:0] event_sync, fault_sync;
    logic stgl_q;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) begin
            event_sync <= '0;
            fault_sync <= '0;
            stgl_q <= 1'b0;
        end else begin
            event_sync <= {event_sync[0], stgl};
            fault_sync <= {fault_sync[0], lock_bad};
            stgl_q <= event_sync[1];
        end
    wire nb = event_sync[1] != stgl_q;
    wire lock_bad_s = fault_sync[1];
`endif

    logic [6:0] fill;
    logic [5:0] rct;
    logic [9:0] apt_n, apt_c;
    logic       apt_ref, warm;
    assign valid   = fill[6];
    assign ok      = warm && !rct_fail && !apt_fail;
    assign raw_bit = bit_q;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
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
            if (take) fill <= '0;
            if (lock_bad_s) rct_fail <= 1'b1;
            if (nb) begin
                bit_q <= samp;
                if (ok && (!fill[6] || take)) begin
                    word <= {word[62:0], samp};
                    fill <= take ? 7'd1 : fill + 1'b1;
                end
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
