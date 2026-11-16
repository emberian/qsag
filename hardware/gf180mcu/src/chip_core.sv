// SPDX-License-Identifier: Apache-2.0
// Dregg-180 (QSAG-NI-180) Dragon's Egg Houyhnhnm Enclave chip core for wafer.space GF180MCU Run 3,
// SLOT_0P5X0P5 (`4.90 mm^2`, `gf180mcuD`, 5.0V `gf180mcu_fd_sc_mcu7t5v0`).
// Port signature identical to frozen wafer-space/gf180mcu-project-template `chip_core`.
//
//   inputs[0]   EXT_CLK_BYPASS (pull-up: 1 = clk_pad is the core clock)
//   inputs[2:1] IO_MODE        (pull-down: 00 = SPI, overridable via CSR[56:54])
//   inputs[3]   CS_N           (pull-up)
//   analog[3:0] Unused (zero digital cells wired onto unbuffered asig_5p0 pads)
`default_nettype none

module chip_core #(
    parameter NUM_INPUT_PADS  = 4,
    parameter NUM_BIDIR_PADS  = 38,
    parameter NUM_ANALOG_PADS = 4
)(
    `ifdef USE_POWER_PINS
    inout  wire VDD,
    inout  wire VSS,
    `endif

    input  wire clk,       // clk_pad
    input  wire rst_n,     // rst_n_pad (active low, asynchronous)

    input  wire [NUM_INPUT_PADS-1:0]  input_in,
    output wire [NUM_INPUT_PADS-1:0]  input_pu,
    output wire [NUM_INPUT_PADS-1:0]  input_pd,

    input  wire [NUM_BIDIR_PADS-1:0]  bidir_in,
    output wire [NUM_BIDIR_PADS-1:0]  bidir_out,
    output wire [NUM_BIDIR_PADS-1:0]  bidir_oe,
    output wire [NUM_BIDIR_PADS-1:0]  bidir_cs,
    output wire [NUM_BIDIR_PADS-1:0]  bidir_sl,
    output wire [NUM_BIDIR_PADS-1:0]  bidir_ie,
    output wire [NUM_BIDIR_PADS-1:0]  bidir_pu,
    output wire [NUM_BIDIR_PADS-1:0]  bidir_pd,

    inout  wire [NUM_ANALOG_PADS-1:0] analog
);
    localparam logic [31:0] HW_REV = 32'h0180_0002;

    wire        bypass        = input_in[0];
    wire [1:0]  io_mode_strap = input_in[2:1];
    wire        cs_n          = input_in[3];
    assign input_pu = 4'b1001;
    assign input_pd = 4'b0110;

    wire        clk_core, rst_core_n, srst_n, zeroize;
    wire        fault_glitch, fault_tamper, fault_shield, clk_mon;
    wire [3:0]  quad_trip_map;
    wire [31:0] clk_tel;
    wire [63:0] csr;
    wire        tamper_n;

    wire        trng_take, trng_valid, trng_ok, rct_fail, apt_fail, trng_bit;
    wire [63:0] trng_word;

    wire        an_start, an_write, an_stb, an_go, an_done, an_busy;
    wire [15:0] an_addr;
    wire [63:0] an_rx, an_tx;
    wire        an_cs_n, an_sck, an_mosi, an_miso;

    // Organ 2: 64-RO PUF + BCH(63,36,t=5) Fuzzy Extractor
    wire        puf_start_blk, puf_recon_mode, puf_busy, puf_done, puf_blk_err, puf_mon_clk;
    wire [2:0]  puf_blk_sel, puf_noise_flips;
    wire [5:0]  puf_margin, puf_accepted;
    wire [3:0]  puf_corrected;
    wire [63:0] puf_vmask_in, puf_vmask_out, puf_word_out;
    wire [26:0] puf_syn_in, puf_syn_out;

    // Organ 3: 13.56 MHz HF-NFC + 32-Bit RF NCO
    wire        nfc_clk_in, nfc_ask_in, nfc_load_mod, nco_rf_out;
    wire        nfc_token_valid, nfc_token_consume, nfc_crc_err;
    wire [63:0] nfc_token_nonce, nfc_digest_bind, nco_pkt_data;
    wire [15:0] nfc_quorum_flags, nfc_rx_frames;
    wire        nco_en, nco_pkt_load, nco_tx_active;
    wire [1:0]  nco_mode;
    wire [3:0]  nco_sym_shift;
    wire [31:0] nco_ftw_base, nco_ftw_delta;

    // Organ 4: < 5 ns Brands-Chaum Rapid-Bit Responder + 32-Tap Vernier TDC
    wire        db_chal_in, db_resp_out, db_resp_oe, db_resp_ie_force, db_resp_loopback;
    wire        db_load_r0, db_load_r1, db_arm_responder, db_step_round;
    wire        db_launch_ping, db_cal_ping, db_dist_consume;
    wire        db_responder_armed, db_dist_valid, db_dist_timeout;
    wire [6:0]  db_rounds_done;
    wire [63:0] db_load_wdata, db_chal_log, db_resp_log;
    wire [31:0] db_dist_cycles;

    wire        in_valid, in_pop, out_ready, out_push;
    wire [63:0] in_data, out_data;
    wire [1:0]  active_io_mode;
    wire        verify_ok, key_valid, vat_ready;
    wire        fault_anchor, fault_mac, fault_control, fault_laser_dfa;
    wire        eng_busy, rx_overrun, tx_underrun;

    qsag_gals_clk_rst u_clk (
        .clk_pad(clk), .rst_n_pad(rst_n), .bypass(bypass), .tamper_n(tamper_n), .csr(csr),
        .trng_bit(trng_bit), .puf_mon_clk(puf_mon_clk), .ext_zeroize_req(fault_laser_dfa),
        .clk_core(clk_core), .rst_core_n(rst_core_n), .srst_n(srst_n),
        .zeroize(zeroize), .fault_glitch(fault_glitch), .fault_tamper(fault_tamper),
        .fault_shield(fault_shield), .quad_trip_map(quad_trip_map),
        .clk_mon(clk_mon), .tel(clk_tel)
    );

    qsag_trng u_trng (
        .clk(clk_core), .rst_n(rst_core_n), .en(csr[25]), .take(trng_take), .word(trng_word),
        .valid(trng_valid), .ok(trng_ok), .rct_fail(rct_fail), .apt_fail(apt_fail), .raw_bit(trng_bit)
    );

    qsag_anchor_spi u_anchor (
        .clk(clk_core), .rst_n(rst_core_n), .div(csr[24:21]), .start(an_start), .write(an_write),
        .addr(an_addr), .stb(an_stb), .go(an_go), .rx(an_rx), .tx(an_tx), .done(an_done),
        .busy(an_busy), .cs_n(an_cs_n), .sck(an_sck), .mosi(an_mosi), .miso(an_miso)
    );

    dregg_ro_puf_bch u_puf (
        .clk(clk_core), .rst_n(rst_core_n), .srst_n(srst_n),
        .start_blk(puf_start_blk), .recon_mode(puf_recon_mode), .blk_sel(puf_blk_sel),
        .margin_thresh(puf_margin), .noise_flips(puf_noise_flips),
        .vmask_in(puf_vmask_in), .syn_in(puf_syn_in),
        .mon_en(csr[50]), .mon_beat(csr[51]), .mon_idx(csr[63:58]), .puf_mon_clk(puf_mon_clk),
        .busy(puf_busy), .done(puf_done), .blk_err(puf_blk_err),
        .vmask_out(puf_vmask_out), .syn_out(puf_syn_out), .word_out(puf_word_out),
        .accepted_in_blk(puf_accepted), .corrected_in_blk(puf_corrected)
    );

    dregg_nfc_nco u_nfc (
        .clk(clk_core), .rst_n(rst_core_n), .arst_n(rst_n), .srst_n(srst_n),
        .nfc_clk_in(nfc_clk_in), .nfc_ask_in(nfc_ask_in),
        .nfc_load_mod(nfc_load_mod), .nco_rf_out(nco_rf_out),
        .token_consume(nfc_token_consume), .token_valid(nfc_token_valid),
        .token_nonce(nfc_token_nonce), .token_digest_bind(nfc_digest_bind),
        .token_quorum_flags(nfc_quorum_flags), .nfc_rx_frames(nfc_rx_frames), .nfc_crc_err(nfc_crc_err),
        .nco_en(nco_en), .nco_mode(nco_mode), .nco_sym_shift(nco_sym_shift),
        .nco_ftw_base(nco_ftw_base), .nco_ftw_delta(nco_ftw_delta),
        .nco_pkt_load(nco_pkt_load), .nco_pkt_data(nco_pkt_data), .nco_tx_active(nco_tx_active)
    );

    dregg_distance_tdc u_db (
        .clk(clk_core), .rst_n(rst_core_n), .srst_n(srst_n),
        .db_chal_pad_in(db_chal_in), .db_resp_pad_out(db_resp_out),
        .db_resp_pad_oe(db_resp_oe), .db_resp_pad_ie_force(db_resp_ie_force),
        .db_resp_pad_loopback(db_resp_loopback),
        .load_r0(db_load_r0), .load_r1(db_load_r1), .load_wdata(db_load_wdata),
        .arm_responder(db_arm_responder), .step_round(db_step_round),
        .launch_ping(db_launch_ping), .cal_ping(db_cal_ping), .dist_consume(db_dist_consume),
        .responder_armed(db_responder_armed), .rounds_done(db_rounds_done),
        .chal_log_lo(db_chal_log), .resp_log_lo(db_resp_log),
        .dist_valid(db_dist_valid), .dist_timeout(db_dist_timeout), .dist_cycles(db_dist_cycles)
    );

    // Mandate #1: rct_fail / apt_fail are reported in tel0 (and gate TRNG keyload) without wedging
    // FAULT at cold boot if csr[25]=0; fault_shield only asserts FAULT when csr[49] is armed!
    wire fault = fault_glitch | fault_tamper | (fault_shield & csr[49]) | fault_laser_dfa
               | fault_anchor | fault_mac | (csr[25] & (rct_fail | apt_fail))
               | rx_overrun | tx_underrun | fault_control;

    wire [63:0] tel0 = {HW_REV[31:16], fault_laser_dfa, (fault_shield & csr[49]), quad_trip_map[1:0],
                        eng_busy, key_valid, active_io_mode, bypass, rx_overrun, tx_underrun,
                        trng_ok, apt_fail, rct_fail, fault_tamper, fault_glitch, clk_tel};

    qsag_wire_engine u_engine (
        .clk(clk_core), .rst_n(rst_core_n), .srst_n(srst_n), .zeroize(zeroize),
        .in_valid(in_valid), .in_data(in_data), .in_pop(in_pop),
        .out_ready(out_ready), .out_data(out_data), .out_push(out_push),
        .an_start(an_start), .an_write(an_write), .an_addr(an_addr), .an_stb(an_stb), .an_go(an_go),
        .an_rx(an_rx), .an_tx(an_tx), .an_done(an_done),
        .trng_valid(trng_valid), .trng_word(trng_word), .trng_ok(trng_ok), .trng_take(trng_take),
        .puf_start_blk(puf_start_blk), .puf_recon_mode(puf_recon_mode), .puf_blk_sel(puf_blk_sel),
        .puf_margin(puf_margin), .puf_noise_flips(puf_noise_flips),
        .puf_vmask_in(puf_vmask_in), .puf_syn_in(puf_syn_in),
        .puf_done(puf_done), .puf_blk_err(puf_blk_err),
        .puf_vmask_out(puf_vmask_out), .puf_syn_out(puf_syn_out), .puf_word_out(puf_word_out),
        .puf_corrected(puf_corrected),
        .nfc_token_valid(nfc_token_valid), .nfc_digest_bind(nfc_digest_bind),
        .nfc_quorum_flags(nfc_quorum_flags), .nfc_rx_frames(nfc_rx_frames),
        .nfc_token_consume(nfc_token_consume),
        .nco_en(nco_en), .nco_mode(nco_mode), .nco_sym_shift(nco_sym_shift),
        .nco_ftw_base(nco_ftw_base), .nco_ftw_delta(nco_ftw_delta),
        .nco_pkt_load(nco_pkt_load), .nco_pkt_data(nco_pkt_data), .nco_tx_active(nco_tx_active),
        .db_load_r0(db_load_r0), .db_load_r1(db_load_r1), .db_load_wdata(db_load_wdata),
        .db_arm_responder(db_arm_responder), .db_step_round(db_step_round),
        .db_launch_ping(db_launch_ping), .db_cal_ping(db_cal_ping), .db_dist_consume(db_dist_consume),
        .db_responder_armed(db_responder_armed), .db_rounds_done(db_rounds_done),
        .db_chal_log(db_chal_log), .db_resp_log(db_resp_log),
        .db_dist_valid(db_dist_valid), .db_dist_timeout(db_dist_timeout), .db_dist_cycles(db_dist_cycles),
        .tel0(tel0), .tel1({HW_REV[15:0], 11'd0, nfc_crc_err, quad_trip_map}), .csr(csr),
        .verify_ok(verify_ok), .key_valid_o(key_valid), .vat_ready_o(vat_ready),
        .fault_anchor(fault_anchor), .fault_mac(fault_mac), .fault_control(fault_control),
        .fault_laser_dfa(fault_laser_dfa), .busy(eng_busy)
    );

    qsag_io_shell u_io (
        .clk_core(clk_core), .rst_core_n(rst_core_n), .arst_n(rst_n), .clk_pad(clk),
        .io_mode_strap(io_mode_strap), .cs_n(cs_n),
        .csr_sck_clkpad(csr[57]), .csr_iomode_en(csr[56]), .csr_iomode(csr[55:54]),
        .csr_async_sb_en(csr[26]),
        .slew_dq(csr[19]), .slew_tx(csr[19]), .slew_ctrl(csr[19]), .slew_rf_db(csr[27]),
        .bidir_in(bidir_in), .bidir_out(bidir_out), .bidir_oe(bidir_oe), .bidir_cs(bidir_cs),
        .bidir_sl(bidir_sl), .bidir_ie(bidir_ie), .bidir_pu(bidir_pu), .bidir_pd(bidir_pd),
        .in_valid(in_valid), .in_data(in_data), .in_pop(in_pop),
        .out_ready(out_ready), .out_data(out_data), .out_push(out_push),
        .verify_ok(verify_ok), .fault(fault), .busy(eng_busy), .clk_mon(clk_mon),
        .an_cs_n(an_cs_n), .an_sck(an_sck), .an_mosi(an_mosi), .an_miso(an_miso),
        .tamper_n(tamper_n),
        .nfc_clk_in(nfc_clk_in), .nfc_ask_in(nfc_ask_in), .nfc_load_mod(nfc_load_mod),
        .nco_rf_out(nco_rf_out),
        .db_chal_in(db_chal_in), .db_resp_out(db_resp_out), .db_resp_oe(db_resp_oe),
        .db_resp_ie_force(db_resp_ie_force), .db_resp_loopback(db_resp_loopback),
        .active_io_mode(active_io_mode),
        .rx_overrun(rx_overrun), .tx_underrun(tx_underrun)
    );

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, an_busy, puf_busy, puf_accepted, nfc_token_nonce, vat_ready};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule

`default_nettype wire
