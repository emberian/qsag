// Dregg-180 Organ 4: < 6 ns Brands-Chaum Distance-Bounding Responder + 32-Tap Vernier TDC.
//
// Defends capability invocations against Mafia-fraud / wormhole / relay attacks at speed of light
// (c = 30 cm/ns -> 15 cm round-trip distance per nanosecond of excess propagation time):
//   1. Pre-committed 128-bit rapid-bit registers (r0[127:0], r1[127:0]) cleared on srst_n.
//      Before each round idx, r0_pre_q = r0[idx] and r1_pre_q = r1[idx] are pre-staged so the
//      live pad-to-pad turnaround path from DB_CHAL_IN to DB_RESP_OUT traverses ONE single
//      (* keep *) gf180mcu_fd_sc_mcu7t5v0__mux2_4 gate (< 4.2 ns pad-to-pad in gf180mcuD 5V!).
//   2. 32-Stage (* keep *) Vernier Delay-Line Time-to-Digital Converter (TDC):
//      Pairs a 32-tap slow delay chain (dlya_1, ~450 ps/tap) against a 32-tap fast buffer chain
//      (buf_2, ~220 ps/tap) for ~230 ps (~3.5 cm) sub-cycle Vernier time resolution alongside a
//      16-bit coarse core-clock cycle counter, producing `dist_measured = {coarse[15:0], fine[5:0]}`
//      enforced directly against `SpongeMacaroon.max_distance_cycles` inside `dregg_captp_vat`.
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

    // Population count / thermometer-to-binary encoder (0..32)
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
    // Control from Wire Engine / CapTP Vat
    input  wire         load_r0_lo,
    input  wire         load_r0_hi,
    input  wire         load_r1_lo,
    input  wire         load_r1_hi,
    input  wire  [63:0] load_wdata,
    input  wire         arm_responder,     // arms 128-round < 6 ns rapid-bit responder
    input  wire         step_round,        // host/protocol round advance strobe (or auto on pulse)
    input  wire         launch_ping,       // launches speed-of-light RTT measurement pulse
    input  wire         dist_consume,      // single-use consume by CapTP Vat
    // Transcript & TDC outputs
    output logic        responder_armed,
    output logic [7:0]  rounds_done,
    output logic [63:0] chal_log_lo,
    output logic [63:0] chal_log_hi,
    output logic [63:0] resp_log_lo,
    output logic [63:0] resp_log_hi,
    output logic        dist_valid,
    output logic        dist_timeout,
    output logic [31:0] dist_cycles        // [21:6] coarse core clocks, [5:0] Vernier 230 ps taps
);
    // Secret pre-committed rapid-bit vectors r0[127:0], r1[127:0]
    wire [63:0] r0_lo, r0_hi, r1_lo, r1_hi;
    qsag_ereg #(.W(64)) u_r0l (.clk(clk), .rst_n(srst_n), .en(load_r0_lo), .d(load_wdata), .q(r0_lo));
    qsag_ereg #(.W(64)) u_r0h (.clk(clk), .rst_n(srst_n), .en(load_r0_hi), .d(load_wdata), .q(r0_hi));
    qsag_ereg #(.W(64)) u_r1l (.clk(clk), .rst_n(srst_n), .en(load_r1_lo), .d(load_wdata), .q(r1_lo));
    qsag_ereg #(.W(64)) u_r1h (.clk(clk), .rst_n(srst_n), .en(load_r1_hi), .d(load_wdata), .q(r1_hi));

    wire [127:0] r0_vec = {r0_hi, r0_lo};
    wire [127:0] r1_vec = {r1_hi, r1_lo};

    // Pre-staged current round bits so ONLY u_rapid_mux sits on DB_CHAL_IN -> DB_RESP_OUT!
    logic        r0_pre_q, r1_pre_q;
    logic        ping_active, ping_tx_q;
    wire         rapid_mux_y;

    // In rapid-bit responder mode: responder_armed == 1, ping_active == 0 -> pure mux2_4 path!
    // In active RTT ping mode: ping_active == 1 -> drives ping_tx_q launch edge!
    wire mux_i0 = ping_active ? ping_tx_q : r0_pre_q;
    wire mux_i1 = ping_active ? ping_tx_q : r1_pre_q;
    qsag_fast_mux2 u_rapid_mux (
        .a(mux_i0), .b(mux_i1), .sel(db_chal_pad_in), .y(rapid_mux_y)
    );
    assign db_resp_pad_out = rapid_mux_y;
    assign db_resp_pad_oe  = responder_armed | ping_active;

    // Synchronized observation of challenge/echo pad in clk_core
    wire chal_s;
    qsag_sync2 #(.RV(1'b0)) u_cs (.clk(clk), .rst_n(rst_n), .d(db_chal_pad_in), .q(chal_s));

    // Vernier TDC instance: start_pulse = ping_tx_q, stop_pulse = db_chal_pad_in
    logic        tdc_arm_n;
    wire  [5:0]  vernier_fine;
    wire  [31:0] vernier_thermo;
    dregg_vernier_tdc32 u_tdc (
        .rst_n(rst_n), .arm_n(tdc_arm_n), .start_pulse(ping_tx_q), .stop_pulse(db_chal_pad_in),
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
            if (dist_consume) begin
                dist_valid <= 1'b0;
            end

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
                    ping_tx_q  <= 1'b1; // Launch outbound pulse edge!
                    coarse_cnt <= 16'd0;
                end else if (chal_s) begin
                    ping_active <= 1'b0;
                    ping_tx_q   <= 1'b0;
                    dist_valid  <= 1'b1;
                    dist_cycles <= {10'd0, coarse_cnt, vernier_fine};
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
