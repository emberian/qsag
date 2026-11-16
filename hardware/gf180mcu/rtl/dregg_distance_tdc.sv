// Dregg-180 Organ 4: < 6 ns Brands-Chaum Distance-Bounding Responder + 32-Tap Vernier TDC.
//
// GOTCHA #5 silicon fix:
//   * Triggers `u_tdc.start_pulse` from `db_resp_pad_loopback` (`bidir_in[p_resp]` with `.IE=1`
//     enabled during ping!), cancelling the ~3.5 ns outbound `bi_24t` A->PAD buffer delay AND
//     matching the inbound `bi_24t` PAD->Y receiver delay across PVT!
//   * Captures echo arrival via an edge-latched flip-flop (`posedge chal_clk_buf`) rather than
//     sampling `db_chal_pad_in` directly with `clk_core`, so sub-cycle return pulses are never
//     missed while `vernier_fine[5:0]` resolves arrival within ~230 ps (~3.5 cm)!
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
    wire [32:0] s_line;
    wire [32:0] f_line;
    assign s_line[0] = start_pulse;
    assign f_line[0] = stop_pulse;

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
    // Pad signals (ESD-protected bi_24t)
    input  wire         db_chal_pad_in,
    output wire         db_resp_pad_out,
    output wire         db_resp_pad_oe,
    output wire         db_resp_pad_ie_force,  // keeps receiver `.Y` active during ping loopback!
    input  wire         db_resp_pad_loopback,  // `bidir_in[p_resp]` physical pin loopback!
    // Control from Wire Engine / CapTP Vat
    input  wire         load_r0_lo,
    input  wire         load_r0_hi,
    input  wire         load_r1_lo,
    input  wire         load_r1_hi,
    input  wire  [63:0] load_wdata,
    input  wire         arm_responder,
    input  wire         step_round,
    input  wire         launch_ping,
    input  wire         dist_consume,
    // Transcript & TDC outputs
    output logic        responder_armed,
    output logic [7:0]  rounds_done,
    output logic [63:0] chal_log_lo,
    output logic [63:0] chal_log_hi,
    output logic [63:0] resp_log_lo,
    output logic [63:0] resp_log_hi,
    output logic        dist_valid,
    output logic        dist_timeout,
    output logic [31:0] dist_cycles
);
    wire [63:0] r0_lo, r0_hi, r1_lo, r1_hi;
    qsag_ereg #(.W(64)) u_r0l (.clk(clk), .rst_n(srst_n), .en(load_r0_lo), .d(load_wdata), .q(r0_lo));
    qsag_ereg #(.W(64)) u_r0h (.clk(clk), .rst_n(srst_n), .en(load_r0_hi), .d(load_wdata), .q(r0_hi));
    qsag_ereg #(.W(64)) u_r1l (.clk(clk), .rst_n(srst_n), .en(load_r1_lo), .d(load_wdata), .q(r1_lo));
    qsag_ereg #(.W(64)) u_r1h (.clk(clk), .rst_n(srst_n), .en(load_r1_hi), .d(load_wdata), .q(r1_hi));

    wire [127:0] r0_vec = {r0_hi, r0_lo};
    wire [127:0] r1_vec = {r1_hi, r1_lo};

    logic r0_pre_q, r1_pre_q;
    logic ping_active, ping_tx_q;
    wire  rapid_mux_y;

    wire mux_i0 = ping_active ? ping_tx_q : r0_pre_q;
    wire mux_i1 = ping_active ? ping_tx_q : r1_pre_q;
    qsag_fast_mux2 u_rapid_mux (
        .a(mux_i0), .b(mux_i1), .sel(db_chal_pad_in), .y(rapid_mux_y)
    );
    assign db_resp_pad_out      = rapid_mux_y;
    assign db_resp_pad_oe       = responder_armed | ping_active;
    assign db_resp_pad_ie_force = ping_active;

    // Synchronized level for rapid-bit logging
    wire chal_s;
    qsag_sync2 #(.RV(1'b0)) u_cs (.clk(clk), .rst_n(rst_n), .d(db_chal_pad_in), .q(chal_s));

    // Edge-latched echo detector clocked directly on posedge db_chal_pad_in (never misses narrow echoes!)
    logic       tdc_arm_n;
    wire        hit_rn = rst_n & tdc_arm_n;
    wire        chal_clk_buf;
    logic       echo_hit_async;
    wire        echo_hit_s;
    qsag_clkbuf u_ccb (.a(db_chal_pad_in), .y(chal_clk_buf));
    always_ff @(posedge chal_clk_buf or negedge hit_rn)
        if (!hit_rn) echo_hit_async <= 1'b0;
        else         echo_hit_async <= 1'b1;
    qsag_sync2 #(.RV(1'b0)) u_ehs (.clk(clk), .rst_n(rst_n), .d(echo_hit_async), .q(echo_hit_s));

    // Pad-loopback start pulse cancels outbound bi_24t buffer delay!
    wire  [5:0]  vernier_fine;
    wire  [31:0] vernier_thermo;
    dregg_vernier_tdc32 u_tdc (
        .rst_n(rst_n), .arm_n(tdc_arm_n),
        .start_pulse(db_resp_pad_loopback),
        .stop_pulse(db_chal_pad_in),
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
            chal_log_hi     <= '0;
            resp_log_lo     <= '0;
            resp_log_hi     <= '0;
            ping_active     <= 1'b0;
            ping_tx_q       <= 1'b0;
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
                chal_log_hi     <= 64'd0;
                resp_log_lo     <= 64'd0;
                resp_log_hi     <= 64'd0;
            end else if (responder_armed && step_round) begin
                logic cbit, rbit;
                cbit = chal_s;
                rbit = cbit ? r1_pre_q : r0_pre_q;
                if (!rb_idx[6]) begin
                    chal_log_lo[rb_idx[5:0]] <= cbit;
                    resp_log_lo[rb_idx[5:0]] <= rbit;
                end else begin
                    chal_log_hi[rb_idx[5:0]] <= cbit;
                    resp_log_hi[rb_idx[5:0]] <= rbit;
                end
                rounds_done <= rounds_done + 8'd1;
                if (rb_idx == 7'd127) begin
                    responder_armed <= 1'b0;
                end else begin
                    rb_idx   <= rb_idx + 7'd1;
                    r0_pre_q <= r0_vec[rb_idx + 7'd1];
                    r1_pre_q <= r1_vec[rb_idx + 7'd1];
                end
            end

            if (launch_ping) begin
                ping_active  <= 1'b1;
                ping_tx_q    <= 1'b0;
                tdc_arm_n    <= 1'b0;
                coarse_cnt   <= 16'd0;
                dist_valid   <= 1'b0;
                dist_timeout <= 1'b0;
            end else if (ping_active) begin
                if (!tdc_arm_n) begin
                    tdc_arm_n <= 1'b1;
                end else if (!ping_tx_q) begin
                    ping_tx_q  <= 1'b1;
                    coarse_cnt <= 16'd0;
                end else if (echo_hit_s) begin
                    ping_active <= 1'b0;
                    ping_tx_q   <= 1'b0;
                    dist_valid  <= 1'b1;
                    // Subtract 2 synchronizer cycles from coarse_cnt (saturated at 0)
                    dist_cycles <= {10'd0, (coarse_cnt >= 16'd2) ? (coarse_cnt - 16'd2) : 16'd0, vernier_fine};
                end else if (coarse_cnt == 16'h0FFF) begin
                    ping_active  <= 1'b0;
                    ping_tx_q    <= 1'b0;
                    dist_timeout <= 1'b1;
                    dist_cycles  <= 32'hFFFF_FFFF;
                end else begin
                    coarse_cnt <= coarse_cnt + 16'd1;
                end
            end
        end
    end
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = |vernier_thermo;
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire
