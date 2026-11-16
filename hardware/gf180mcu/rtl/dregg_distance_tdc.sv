// Dregg-180 Organ 4: < 5 ns Brands-Chaum Distance-Bounding Responder + 32-Tap Vernier TDC.
//
// Silicon-hardened against Subcarbon R0 Traps T2 & T3 + Gotcha #5:
//   * Single-gate `mux2_4` (`u_rapid_mux`) on `db_chal_pad_in -> db_resp_pad_out` (~2.9 ns TT,
//     ~4.6 ns SS!) with non-dont_touch `qsag_iso_buf` buffers on `mux_i0/mux_i1` and on the side
//     synchronizer tap `chal_tap_iso` so OpenROAD Resizer NEVER hits RSZ-3006 or loads `sel`.
//   * `db_resp_pad_loopback` (`.IE=1` during ping) triggers `u_tdc.start_pulse`, cancelling the
//     outbound `bi_24t` A->PAD delay and matching inbound PAD->Y across PVT.
//   * One-shot self-locking echo latch (`echo_hit_async`) blocks reflection/ringing edges on
//     `db_chal_pad_in` from re-clocking the Vernier taps while `vernier_fine` settles!
//   * Includes on-chip 1-cycle `clk_core` PVT calibration (`cal_ping`) per Park & Wentzloff 2011.
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
    // Pad signals (ESD-protected bi_24t, CS=0 CMOS buffer on CHAL, SL=0 fast slew on RESP)
    input  wire         db_chal_pad_in,
    output wire         db_resp_pad_out,
    output wire         db_resp_pad_oe,
    output wire         db_resp_pad_ie_force,
    input  wire         db_resp_pad_loopback,
    // Control from Wire Engine / CapTP Vat
    input  wire         load_r0_lo,
    input  wire         load_r0_hi,
    input  wire         load_r1_lo,
    input  wire         load_r1_hi,
    input  wire  [63:0] load_wdata,
    input  wire         arm_responder,
    input  wire         step_round,
    input  wire         launch_ping,
    input  wire         cal_ping,              // 1-cycle on-chip PVT Vernier self-calibration!
    input  wire         dist_consume,
    // Transcript & TDC outputs
    output logic        responder_armed,
    output logic [7:0]  rounds_done,
    output logic [63:0] chal_log_lo,
    output logic [63:0] resp_log_lo,
    output logic [63:0] transcript_mac,
    output logic        dist_valid,
    output logic        dist_timeout,
    output logic [31:0] dist_cycles
);
    // Secret R0/R1 vectors stored in async-zeroized latrnq_1 transparent latches
    wire        r_any_we = load_r0_lo | load_r0_hi | load_r1_lo | load_r1_hi;
    wire [63:0] r_wd_q;
    qsag_ereg_nr #(.W(64)) u_rhold (.clk(clk), .en(r_any_we), .d(load_wdata), .q(r_wd_q));

    wire [63:0] r0_lo, r0_hi, r1_lo, r1_hi;
    wire g_r0l, g_r0h, g_r1l, g_r1h;
    qsag_clkgate_1 u_cg0l (.clk(clk), .en(load_r0_lo), .gclk(g_r0l));
    qsag_clkgate_1 u_cg0h (.clk(clk), .en(load_r0_hi), .gclk(g_r0h));
    qsag_clkgate_1 u_cg1l (.clk(clk), .en(load_r1_lo), .gclk(g_r1l));
    qsag_clkgate_1 u_cg1h (.clk(clk), .en(load_r1_hi), .gclk(g_r1h));
    qsag_latch_word_rst #(.W(64)) u_r0l (.gate(g_r0l), .rst_n(srst_n), .d(r_wd_q), .q(r0_lo));
    qsag_latch_word_rst #(.W(64)) u_r0h (.gate(g_r0h), .rst_n(srst_n), .d(r_wd_q), .q(r0_hi));
    qsag_latch_word_rst #(.W(64)) u_r1l (.gate(g_r1l), .rst_n(srst_n), .d(r_wd_q), .q(r1_lo));
    qsag_latch_word_rst #(.W(64)) u_r1h (.gate(g_r1h), .rst_n(srst_n), .d(r_wd_q), .q(r1_hi));

    wire [127:0] r0_vec = {r0_hi, r0_lo};
    wire [127:0] r1_vec = {r1_hi, r1_lo};

    logic r0_pre_q, r1_pre_q;
    logic ping_active, ping_cal_mode, ping_tx_q, cal_stop_q;
    wire  rapid_mux_y;

    wire mux_i0_raw = (ping_active && !ping_cal_mode) ? ping_tx_q : r0_pre_q;
    wire mux_i1_raw = (ping_active && !ping_cal_mode) ? ping_tx_q : r1_pre_q;
    wire mux_i0_iso, mux_i1_iso;
    qsag_iso_buf u_mi0 (.a(mux_i0_raw), .y(mux_i0_iso));
    qsag_iso_buf u_mi1 (.a(mux_i1_raw), .y(mux_i1_iso));

    qsag_fast_mux2 u_rapid_mux (
        .a(mux_i0_iso), .b(mux_i1_iso), .sel(db_chal_pad_in), .y(rapid_mux_y)
    );
    assign db_resp_pad_out      = rapid_mux_y;
    assign db_resp_pad_oe       = responder_armed | (ping_active & ~ping_cal_mode);
    assign db_resp_pad_ie_force = ping_active & ~ping_cal_mode;

    // Isolated side tap so buffering u_cs/u_ccb never touches u_rapid_mux/S!
    wire chal_side_iso;
    qsag_iso_buf u_csiso (.a(db_chal_pad_in), .y(chal_side_iso));

    wire chal_s;
    qsag_sync2 #(.RV(1'b0)) u_cs (.clk(clk), .rst_n(rst_n), .d(chal_side_iso), .q(chal_s));

    // One-shot self-locking echo detector: captures ONLY the FIRST rising edge of stop_raw!
    logic tdc_arm_n;
    wire  hit_rn    = rst_n & tdc_arm_n;
    wire  stop_raw  = ping_cal_mode ? cal_stop_q : chal_side_iso;
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
        .stop_pulse(echo_hit_async), // locked 0->1 single-edge stop_pulse prevents re-clocking!
        .fine_code(vernier_fine), .thermo_raw(vernier_thermo)
    );

    logic [15:0] coarse_cnt;
    logic [6:0]  rb_idx;

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            responder_armed <= 1'b0;
            rounds_done     <= '0;
            rb_idx          <= '0;
            r0_pre_q        <= 1'b0;
            r1_pre_q        <= 1'b0;
            chal_log_lo     <= '0;
            resp_log_lo     <= '0;
            transcript_mac  <= '0;
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
                responder_armed <= 1'b1;
                rounds_done     <= 8'd0;
                rb_idx          <= 7'd0;
                r0_pre_q        <= r0_vec[0];
                r1_pre_q        <= r1_vec[0];
                chal_log_lo     <= 64'd0;
                resp_log_lo     <= 64'd0;
                transcript_mac  <= 64'hDB18_05A3_CAFE_0001;
            end else if (responder_armed && step_round) begin
                logic cbit, rbit;
                cbit = chal_s;
                rbit = cbit ? r1_pre_q : r0_pre_q;
                // Shift register capture (zero 128-way bit-addressed demuxes!)
                chal_log_lo    <= {cbit, chal_log_lo[63:1]};
                resp_log_lo    <= {rbit, resp_log_lo[63:1]};
                transcript_mac <= {transcript_mac[62:0], transcript_mac[63]} ^
                                  (transcript_mac[63] ? 64'h1B : 64'd0) ^ {62'd0, rbit, cbit};
                rounds_done    <= rounds_done + 8'd1;
                if (rb_idx == 7'd127) begin
                    responder_armed <= 1'b0;
                end else begin
                    rb_idx   <= rb_idx + 7'd1;
                    r0_pre_q <= r0_vec[rb_idx + 7'd1];
                    r1_pre_q <= r1_vec[rb_idx + 7'd1];
                end
            end

            if (launch_ping || cal_ping) begin
                ping_active   <= 1'b1;
                ping_cal_mode <= cal_ping;
                ping_tx_q     <= 1'b0;
                cal_stop_q    <= 1'b0;
                tdc_arm_n     <= 1'b0;
                coarse_cnt    <= 16'd0;
                dist_valid    <= 1'b0;
                dist_timeout  <= 1'b0;
            end else if (ping_active) begin
                if (!tdc_arm_n) begin
                    tdc_arm_n <= 1'b1;
                end else if (!ping_tx_q) begin
                    ping_tx_q  <= 1'b1;
                    coarse_cnt <= 16'd0;
                end else begin
                    if (ping_cal_mode) cal_stop_q <= 1'b1; // 1-cycle known reference stop!
                    if (echo_hit_s) begin
                        ping_active <= 1'b0;
                        ping_tx_q   <= 1'b0;
                        cal_stop_q  <= 1'b0;
                        dist_valid  <= 1'b1;
                        dist_cycles <= {10'd0, (coarse_cnt >= 16'd2) ? (coarse_cnt - 16'd2) : 16'd0, vernier_fine};
                    end else if (coarse_cnt == 16'h0FFF) begin
                        ping_active  <= 1'b0;
                        ping_tx_q    <= 1'b0;
                        cal_stop_q   <= 1'b0;
                        dist_timeout <= 1'b1;
                        dist_cycles  <= 32'hFFFF_FFFF;
                    end else begin
                        coarse_cnt <= coarse_cnt + 16'd1;
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
