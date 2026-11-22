// Coherent-Sampling Ring-Oscillator (CoSO) TRNG with NIST SP 800-90B Health Zeroization:
//   - Immediate hardware zeroization of `word` & `fill` on ANY RCT, APT, or lock-detector
//     fault so pre-fault bits can never be read by firmware.
//   - Pipelined `sclk` counter wrap/short flags for clean multi-corner high-speed timing.
module qsag_trng (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         en,
    input  wire         take,
    output logic [63:0] word,
    output wire         valid,
    output wire         ok,
    output logic        rct_fail,
    output logic        apt_fail,
    output wire         raw_bit
);
    logic bit_q;
`ifdef ASS2_FAST_ENTROPY
    logic [15:0] fixture_q;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) fixture_q <= 16'h1;
        else if (en) fixture_q <= {fixture_q[14:0], ^(fixture_q & 16'hb400)};
    wire samp = fixture_q[0];
    wire nb = en;
    wire lock_bad_s = 1'b0;
`else
    wire osc_f, sclk;
    qsag_ass2_ring #(.STAGES(17)) u_fast (.en(en), .osc(osc_f));
    qsag_ass2_ring #(.STAGES(17)) u_slow (.en(en), .osc(sclk));

    (* ASYNC_REG = "TRUE" *) logic beat_m, beat_s;
    logic [2:0]  beat_hist;
    logic        beat_st, short_prev, cnt_max_q, cnt_short_q;
    logic [15:0] c_cnt;
    logic        samp, stgl, lock_bad;

    wire all_hi    = beat_s & (&beat_hist);
    wire all_lo    = ~beat_s & (~|beat_hist);
    wire beat_rise = ~beat_st & all_hi;

    always_ff @(posedge sclk or negedge rst_n) begin
        if (!rst_n) begin
            beat_m      <= 1'b0;
            beat_s      <= 1'b0;
            beat_hist   <= 3'b000;
            beat_st     <= 1'b0;
            short_prev  <= 1'b0;
            cnt_max_q   <= 1'b0;
            cnt_short_q <= 1'b1;
            c_cnt       <= 16'd1;
            samp        <= 1'b0;
            stgl        <= 1'b0;
            lock_bad    <= 1'b0;
        end else begin
            beat_m    <= osc_f;
            beat_s    <= beat_m;
            beat_hist <= {beat_hist[1:0], beat_s};
            if (all_hi)      beat_st <= 1'b1;
            else if (all_lo) beat_st <= 1'b0;
            if (beat_rise || cnt_max_q) begin
                samp        <= c_cnt[0];
                short_prev  <= cnt_short_q;
                if ((short_prev && cnt_short_q) || cnt_max_q) lock_bad <= 1'b1;
                stgl        <= ~stgl;
                c_cnt       <= 16'd1;
                cnt_max_q   <= 1'b0;
                cnt_short_q <= 1'b1;
            end else begin
                c_cnt       <= c_cnt + 16'd1;
                cnt_max_q   <= (c_cnt == 16'hFFFE);
                cnt_short_q <= (c_cnt < 16'd11);
            end
        end
    end

    (* async_reg = "true" *) logic [1:0] event_sync, fault_sync;
    logic stgl_q;
    always_ff @(posedge clk or negedge rst_n)
        if (!rst_n) begin
            event_sync <= '0;
            fault_sync <= '0;
            stgl_q     <= 1'b0;
        end else begin
            event_sync <= {event_sync[0], stgl};
            fault_sync <= {fault_sync[0], lock_bad};
            stgl_q     <= event_sync[1];
        end
    wire nb         = event_sync[1] != stgl_q;
    wire lock_bad_s = fault_sync[1];
`endif

    logic [6:0] fill;
    logic [5:0] rct;
    logic [9:0] apt_n, apt_c;
    logic       apt_ref, warm;
    wire  any_fault = rct_fail || apt_fail || lock_bad_s;
    assign ok       = warm && !any_fault;
    assign valid    = fill[6] && ok;
    assign raw_bit  = bit_q;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bit_q    <= 1'b0;
            word     <= '0;
            fill     <= '0;
            rct      <= '0;
            apt_n    <= '0;
            apt_c    <= '0;
            apt_ref  <= 1'b0;
            warm     <= 1'b0;
            rct_fail <= 1'b0;
            apt_fail <= 1'b0;
        end else begin
            if (lock_bad_s) rct_fail <= 1'b1;
            if (any_fault) begin
                word <= '0;
                fill <= '0;
            end else if (take) begin
                fill <= '0;
            end

            if (nb) begin
                bit_q <= samp;
                if (ok && (!fill[6] || take)) begin
                    word <= {word[62:0], samp};
                    fill <= take ? 7'd1 : (fill + 7'd1);
                end
                // NIST SP 800-90B Repetition Count Test (cutoff 41)
                if (samp == bit_q) begin
                    if (rct == 6'd39) begin
                        rct_fail <= 1'b1;
                        word     <= '0;
                        fill     <= '0;
                    end else rct <= rct + 6'd1;
                end else rct <= '0;
                // NIST SP 800-90B Adaptive Proportion Test (window 1024, cutoff 821)
                if (apt_n == 10'd0) begin
                    apt_ref <= samp;
                    apt_c   <= 10'd1;
                    apt_n   <= 10'd1;
                end else begin
                    if (samp == apt_ref) begin
                        apt_c <= apt_c + 10'd1;
                        if (apt_c == 10'd820) begin
                            apt_fail <= 1'b1;
                            word     <= '0;
                            fill     <= '0;
                        end
                    end
                    apt_n <= apt_n + 10'd1;
                    if (apt_n == 10'd1023) warm <= 1'b1;
                end
            end
        end
    end
endmodule
