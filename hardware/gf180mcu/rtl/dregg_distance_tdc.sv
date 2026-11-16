// Dregg-180 Organ 4: 64-round rapid-bit responder (Hancke-Kuhn style) + 32-tap Vernier TDC.
//
// Rapid-bit responder. Each round i has two secret response bits r0[i], r1[i]; the verifier is
// entitled to exactly one of them. Per round (R1 B3):
//   * The round opens a few clocks after `arm_responder` / `step_round`. Until something is
//     committed the response pad drives 0: neither bit is on the pad.
//   * Challenge 1 = the challenge pad goes high while the round is open. The pad sets the
//     single-shot lock `u_lock` through one AOI21, and the lock selects r1[i] in `u_rapid_mux`
//     (pad -> AOI21 -> mux2_4 -> pad is the timed path). The lock holds until the next round, so
//     further edges on the pad change nothing and r0[i] never appears.
//   * Challenge 0 = the pad stays low for ROUND_WINDOW core clocks. The round then closes (the
//     lock can no longer be set), and only after the synchronized lock state has been seen clear
//     for four more clocks is r0[i] put on the pad. From then on the pad cannot select r1[i].
//   * `step_round` logs the committed challenge and response, clears the lock, and only then
//     shifts to the next pair of bits, so the next bits are never visible through a stale select.
// A challenge-0 round is therefore not time-critical (the response appears when the window ends);
// the verifier times the challenge-1 rounds, as in the previous design where r0 was simply always
// on the pad. What changed is that r0[i] and r1[i] can no longer both be read.
//   * 64-round shift-out `r0_sr[63:0]` / `r1_sr[63:0]` and 64-bit `chal_log` + `resp_log`.
//   * `db_resp_pad_loopback` (`.IE=1` during ping) cancels outbound `bi_24t` A->PAD delay, and
//     one-shot self-locking `echo_hit_async` blocks reflection re-clocking of `u_tdc`.
`default_nettype none
`timescale 1ps / 1ps

module dregg_vernier_tdc32 (
    input  wire        rst_n,
    input  wire        arm_n,
    input  wire        start_pulse,
    input  wire        stop_pulse,
    output wire [5:0]  fine_code,
    output wire [31:0] thermo_raw
);
    wire start_iso, stop_iso;
    qsag_iso_buf u_ista (.a(start_pulse), .y(start_iso));
    qsag_iso_buf u_isto (.a(stop_pulse),  .y(stop_iso));

    wire [32:0] s_line;
    wire [32:0] f_line;
    assign s_line[0] = start_iso;
    assign f_line[0] = stop_iso;

    genvar i;
    generate
        for (i = 0; i < 32; i++) begin : g_vernier
            qsag_dly_buf      #(.TD(450)) u_slow (.a(s_line[i]), .y(s_line[i+1]));
            qsag_vernier_fast #(.TD(220)) u_fast (.a(f_line[i]), .y(f_line[i+1]));
            wire f_clk;
            qsag_clkbuf u_fc (.a(f_line[i+1]), .y(f_clk));
            logic q_tap;
            wire  tap_rn = rst_n & arm_n;
            always_ff @(posedge f_clk or negedge tap_rn)
                if (!tap_rn) q_tap <= 1'b0;
                else         q_tap <= s_line[i+1];
            assign thermo_raw[i] = q_tap;
        end
    endgenerate

    logic [5:0] pop;
    always_comb begin
        pop = 6'd0;
        for (int k = 0; k < 32; k++)
            pop = pop + {5'd0, thermo_raw[k]};
    end
    assign fine_code = pop;
endmodule

module dregg_distance_tdc (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         srst_n,
    // Pad signals
    input  wire         db_chal_pad_in,
    output wire         db_resp_pad_out,
    output wire         db_resp_pad_oe,
    output wire         db_resp_pad_ie_force,
    input  wire         db_resp_pad_loopback,
    // Control from Wire Engine / CapTP Vat
    input  wire         load_r0,
    input  wire         load_r1,
    input  wire  [63:0] load_wdata,
    input  wire         arm_responder,
    input  wire         step_round,
    input  wire         launch_ping,
    input  wire         cal_ping,
    input  wire         dist_consume,
    // Transcript & TDC outputs
    output logic        responder_armed,
    output logic [6:0]  rounds_done,
    output wire  [63:0] chal_log_lo,
    output wire  [63:0] resp_log_lo,
    output logic        dist_valid,
    output logic        dist_timeout,
    output logic [31:0] dist_cycles
);
    // 2^18 core clocks (5.2 ms at 50 MHz): time the verifier has, after the step command, to send
    // a challenge-1 edge. Longer than an SPI transaction plus host scheduling, short enough that
    // 64 challenge-0 rounds stay below half a second.
    localparam int ROUND_WINDOW_LOG2 = 18;

    wire [63:0] r0_sr, r1_sr;
    logic [1:0] rph;            // round sequencer: 0 live, 1 shift, 2 release the lock clear, 3 open
    logic       round_open;     // the lock may be set by the challenge pad
    logic       locked0;        // challenge 0 committed: r0 bit is on the pad
    logic       lock_clr;
    logic [ROUND_WINDOW_LOG2-1:0] rw_cnt;
    logic [1:0] close_dly;
    wire        step_now = responder_armed & step_round & (rph == 2'd0);
    wire        rb_shift = (rph == 2'd1);
    qsag_ereg #(.W(64)) u_r0 (
        .clk(clk), .rst_n(srst_n), .en(load_r0 | rb_shift),
        .d(load_r0 ? load_wdata : {1'b0, r0_sr[63:1]}), .q(r0_sr)
    );
    qsag_ereg #(.W(64)) u_r1 (
        .clk(clk), .rst_n(srst_n), .en(load_r1 | rb_shift),
        .d(load_r1 ? load_wdata : {1'b0, r1_sr[63:1]}), .q(r1_sr)
    );

    logic ping_active, ping_cal_mode, ping_tx_q, cal_stop_q;
    wire  rapid_mux_y;

    wire ping_drive = ping_active && !ping_cal_mode;
    wire mux_i0_raw = ping_drive ? ping_tx_q : (r0_sr[0] & locked0);
    wire mux_i1_raw = ping_drive ? ping_tx_q : r1_sr[0];
    wire mux_i0_iso, mux_i1_iso;
    qsag_iso_buf u_mi0 (.a(mux_i0_raw), .y(mux_i0_iso));
    qsag_iso_buf u_mi1 (.a(mux_i1_raw), .y(mux_i1_iso));

    // Single-shot challenge lock. hit_n low selects the r1 input; it can only fall while the round
    // is open and only rises again through lock_clr (a flop, asserted between rounds).
    wire lock_hit_n, lock_hit;
    qsag_chal_lock u_lock (
        .chal(db_chal_pad_in), .open(round_open), .clr(lock_clr), .hit_n(lock_hit_n), .hit(lock_hit)
    );
    qsag_fast_mux2 u_rapid_mux (
        .a(mux_i1_iso), .b(mux_i0_iso), .sel(lock_hit_n), .y(rapid_mux_y)
    );
    assign db_resp_pad_out      = rapid_mux_y;
    assign db_resp_pad_oe       = responder_armed | ping_drive;
    assign db_resp_pad_ie_force = ping_drive;

    wire chal_side_iso;
    qsag_iso_buf u_csiso (.a(db_chal_pad_in), .y(chal_side_iso));

    // Committed challenge of the current round, as seen by the core clock
    wire chal_s;
    qsag_sync2 #(.RV(1'b0)) u_cs (.clk(clk), .rst_n(rst_n), .d(lock_hit), .q(chal_s));

    logic tdc_arm_n;
    wire  hit_rn   = rst_n & tdc_arm_n;
    wire  stop_raw = ping_cal_mode ? cal_stop_q : chal_side_iso;
    wire  stop_clk;
    logic echo_hit_async;
    wire  echo_hit_s;
    qsag_clkbuf u_ccb (.a(stop_raw), .y(stop_clk));
    always_ff @(posedge stop_clk or negedge hit_rn)
        if (!hit_rn) echo_hit_async <= 1'b0;
        else         echo_hit_async <= 1'b1;
    qsag_sync2 #(.RV(1'b0)) u_ehs (.clk(clk), .rst_n(rst_n), .d(echo_hit_async), .q(echo_hit_s));

    wire start_mux = ping_cal_mode ? ping_tx_q : db_resp_pad_loopback;
    wire [5:0]  vernier_fine;
    wire [31:0] vernier_thermo;
    dregg_vernier_tdc32 u_tdc (
        .rst_n(rst_n), .arm_n(tdc_arm_n),
        .start_pulse(start_mux),
        .stop_pulse(echo_hit_async),
        .fine_code(vernier_fine), .thermo_raw(vernier_thermo)
    );

    wire [63:0] clog_q, rlog_q;
    wire        rbit_cur = chal_s ? r1_sr[0] : r0_sr[0];
    qsag_ereg_nr #(.W(64)) u_clog (
        .clk(clk), .en(arm_responder | step_now),
        .d(arm_responder ? 64'd0 : {chal_s, clog_q[63:1]}), .q(clog_q)
    );
    qsag_ereg_nr #(.W(64)) u_rlog (
        .clk(clk), .en(arm_responder | step_now),
        .d(arm_responder ? 64'd0 : {rbit_cur, rlog_q[63:1]}), .q(rlog_q)
    );
    assign chal_log_lo = (rounds_done != 7'd0) ? clog_q : 64'd0;
    assign resp_log_lo = (rounds_done != 7'd0) ? rlog_q : 64'd0;

    logic [11:0] coarse_cnt;

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            responder_armed <= 1'b0;
            rounds_done     <= '0;
            rph             <= 2'd0;
            round_open      <= 1'b0;
            locked0         <= 1'b0;
            lock_clr        <= 1'b1;
            rw_cnt          <= '0;
            close_dly       <= '0;
            ping_active     <= 1'b0;
            ping_cal_mode   <= 1'b0;
            ping_tx_q       <= 1'b0;
            cal_stop_q      <= 1'b0;
            tdc_arm_n       <= 1'b0;
            coarse_cnt      <= '0;
            dist_valid      <= 1'b0;
            dist_timeout    <= 1'b0;
            dist_cycles     <= 32'hFFFF_FFFF;
        end else begin
            if (dist_consume) dist_valid <= 1'b0;

            if (arm_responder) begin
                // (re)start: everything closed and cleared, first round opens two clocks later
                responder_armed <= 1'b1;
                rounds_done     <= 7'd0;
                round_open      <= 1'b0;
                locked0         <= 1'b0;
                lock_clr        <= 1'b1;
                rph             <= 2'd2;
            end else if (step_now) begin
                // close the round: the response pad goes back to 0 and the lock is cleared before
                // the registers shift (next clock)
                round_open <= 1'b0;
                locked0    <= 1'b0;
                lock_clr   <= 1'b1;
                rph        <= 2'd1;
            end else begin
                unique case (rph)
                    2'd1: begin
                        rounds_done <= rounds_done + 7'd1;
                        if (rounds_done == 7'd63) begin
                            responder_armed <= 1'b0;   // lock stays cleared, pad released
                            rph             <= 2'd0;
                        end else rph <= 2'd2;
                    end
                    2'd2: begin
                        lock_clr <= 1'b0;
                        rph      <= 2'd3;
                    end
                    2'd3: begin
                        round_open <= 1'b1;
                        rw_cnt     <= '0;
                        close_dly  <= 2'd0;
                        rph        <= 2'd0;
                    end
                    default: if (responder_armed) begin
                        if (round_open) begin
                            if (chal_s || (&rw_cnt)) round_open <= 1'b0;
                            else                     rw_cnt     <= rw_cnt + 1'b1;
                        end else if (!locked0 && !chal_s && !lock_clr) begin
                            // window ended without a challenge: the lock can no longer be set;
                            // wait out the synchronizer before committing to challenge 0
                            if (close_dly == 2'd3) locked0 <= 1'b1;
                            else                   close_dly <= close_dly + 2'd1;
                        end
                    end
                endcase
            end

            if (launch_ping || cal_ping) begin
                ping_active   <= 1'b1;
                ping_cal_mode <= cal_ping;
                ping_tx_q     <= 1'b0;
                cal_stop_q    <= 1'b0;
                tdc_arm_n     <= 1'b0;
                coarse_cnt    <= 12'd0;
                dist_valid    <= 1'b0;
                dist_timeout  <= 1'b0;
            end else if (ping_active) begin
                if (!tdc_arm_n) begin
                    tdc_arm_n <= 1'b1;
                end else if (!ping_tx_q) begin
                    ping_tx_q  <= 1'b1;
                    coarse_cnt <= 12'd0;
                end else begin
                    if (ping_cal_mode) cal_stop_q <= 1'b1;
                    if (echo_hit_s) begin
                        ping_active <= 1'b0;
                        ping_tx_q   <= 1'b0;
                        cal_stop_q  <= 1'b0;
                        dist_valid  <= 1'b1;
                        dist_cycles <= {14'd0, (coarse_cnt >= 12'd2) ? (coarse_cnt - 12'd2) : 12'd0, vernier_fine};
                    end else if (coarse_cnt == 12'hFFF) begin
                        ping_active  <= 1'b0;
                        ping_tx_q    <= 1'b0;
                        cal_stop_q   <= 1'b0;
                        dist_timeout <= 1'b1;
                        dist_cycles  <= 32'hFFFF_FFFF;
                    end else begin
                        coarse_cnt <= coarse_cnt + 12'd1;
                    end
                end
            end
        end
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = |vernier_thermo;
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire
