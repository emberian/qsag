// Dregg-180 v2, configuration S: AREA AND CONNECTIVITY PROXY of the chip core for physical experiments.
// This is not the design and is not simulated. It instantiates block stand-ins with the cell mix, the
// pin counts and the bus topology of ARCHITECTURE.md sections 5 to 7 so that placement, clock-tree and
// routing runs in SLOT_0P5X0P5 with the real pad ring mean something. Replace block by block with
// `v2/rtl` as it appears; the instance names below (u_rf, u_kec, u_wu, u_seq, u_rom, u_spi, u_fram,
// u_trng, u_nfc, u_db, u_puf, u_pufarr, u_shield, u_clk) are what `floorplan/*.tcl` keys on.
//
// Pads (ARCHITECTURE.md 11.2):
//   south  bidir[0] SCK  [1] MOSI  [2] MISO  [3] CS_N        (clk_pad, rst_n_pad beside them)
//   east   bidir[8] NFC_CLK  [9] NFC_ASK  [10] NFC_LM   [13] DB_CHAL  [14] DB_RESP
//          bidir[16] FAULT  [17] IRQ  [21] CLK_MON
//   north  bidir[22] FRAM_CS_N  [23] FRAM_SCK  [24] FRAM_MOSI  [25] FRAM_MISO  [26] TAMPER_N
//   west   input[0] strap: ring as clock   input[1] strap: spare
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
    input  wire clk,
    input  wire rst_n,
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
    // ------------------------------------------------------------------ pads
    wire sck      = bidir_in[0];
    wire mosi     = bidir_in[1];
    wire cs_n     = bidir_in[3];
    wire nfc_clk  = bidir_in[8];
    wire nfc_ask  = bidir_in[9];
    wire db_chal  = bidir_in[13];
    wire fram_miso = bidir_in[25];
    wire tamper_n = bidir_in[26];
    wire miso, nfc_lm, db_resp, db_resp_oe, db_resp_ie, fram_cs_n, fram_sck, fram_mosi;
    logic fault_q, irq_q, clkmon_q;

    assign input_pu = 4'b0000;
    assign input_pd = 4'b1111;

    //   outputs: 2 MISO, 10 NFC_LM, 14 DB_RESP, 16 FAULT, 17 IRQ, 21 CLK_MON, 22 23 24 FRAM
    localparam logic [37:0] OUT_PADS = (38'd1 << 2) | (38'd1 << 10) | (38'd1 << 14) | (38'd1 << 16) |
                                       (38'd1 << 17) | (38'd1 << 21) | (38'd1 << 22) | (38'd1 << 23) | (38'd1 << 24);
    //   inputs:  0 SCK, 1 MOSI, 3 CS_N, 8 9 NFC, 13 DB_CHAL, 25 FRAM_MISO, 26 TAMPER_N
    localparam logic [37:0] IN_PADS  = (38'd1 << 0) | (38'd1 << 1) | (38'd1 << 3) | (38'd1 << 8) | (38'd1 << 9) |
                                       (38'd1 << 13) | (38'd1 << 25) | (38'd1 << 26);
    logic [37:0] o;
    always_comb begin
        o = '0;
        o[2]  = miso;      o[10] = nfc_lm;   o[14] = db_resp;
        o[16] = fault_q;   o[17] = irq_q;    o[21] = clkmon_q;
        o[22] = fram_cs_n; o[23] = fram_sck; o[24] = fram_mosi;
    end
    assign bidir_out = o;
    assign bidir_oe  = (OUT_PADS & ~(38'd1 << 14) & ~(38'd1 << 2)) | ({37'd0, db_resp_oe} << 14) | ({37'd0, ~cs_n} << 2);
    assign bidir_ie  = IN_PADS | ({37'd0, db_resp_ie} << 14);
    assign bidir_cs  = '0;
    assign bidir_sl  = OUT_PADS;                 // slew-limited outputs
    assign bidir_pu  = '0;
    assign bidir_pd  = ~(OUT_PADS | IN_PADS);    // unused pads: inputs with pull-down

    // ------------------------------------------------------------------ clock, reset, tamper
    wire clk_raw, clk_core, osc_raw, osc, rst_core_n, secret_rst_n, clk_fault, tamper_latched;
    wire [15:0] clk_diag;
    logic prov_q, zeroize_q;
    wire fault_glitch, fault_shield;
    wire [3:0] quad_trip;
    qsag_ring_osc #(.N(7)) u_ring (.en(rst_n), .osc(osc_raw));
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_2 u_oscbuf  (.I(osc_raw), .Z(osc));
    px_clkmon u_clk (
        .clk_pad(clk), .osc(osc), .rst_n_pad(rst_n), .strap_osc(input_in[0]), .tamper_n(tamper_n),
        .prov(prov_q), .zeroize(zeroize_q), .sensor_evt(fault_glitch | fault_shield),
        .win_lo(12'd512), .win_hi(12'd3072),
        .clk_core(clk_raw), .rst_core_n(rst_core_n), .secret_rst_n(secret_rst_n),
        .clk_fault(clk_fault), .tamper_latched(tamper_latched), .diag(clk_diag)
    );
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_8 u_clkroot (.I(clk_raw), .Z(clk_core));

    // ------------------------------------------------------------------ sequencer and ROM
    wire [27:0] ir;
    wire [10:0] pc;
    wire [6:0]  ra, rb;
    wire [63:0] h, rd_data;
    wire        z, cy, hz, seq_fault, keyed, dirty, hdr_done, egress_ok;
    wire        unit_busy;
    wire [63:0] rx_word;
    wire        rx_valid;
    logic       key_valid_q;
    px_rom u_rom (.a(pc), .d(ir));
    px_seq3 u_seq (
        .clk(clk_core), .rst_n(rst_core_n), .ir(ir), .entry(rx_word[10:0]), .h(h),
        .z(z), .cy(cy), .hz(hz), .more(rx_valid), .key_valid(key_valid_q), .unit_busy(unit_busy),
        .pc(pc), .ra(ra), .rb(rb), .fault(seq_fault), .keyed(keyed), .dirty(dirty), .hdr_done(hdr_done),
        .egress_ok(egress_ok)
    );
    wire [4:0] op = ir[27:23];
    wire [6:0] fa = ir[22:16], fb = ir[15:9];
    wire [3:0] fn = ir[8:5];
    wire       uop = (op == 5'd20) && !unit_busy;       // unit / organ strobe, organ index in fa[3:0]
    logic [15:0] ustb;
    always_ff @(posedge clk_core or negedge rst_core_n) begin
        if (!rst_core_n) begin
            ustb <= '0; prov_q <= 1'b0; zeroize_q <= 1'b0; key_valid_q <= 1'b0;
        end else begin
            ustb <= uop ? (16'd1 << fa[3:0]) : 16'd0;
            if (ustb[13]) prov_q <= 1'b1;
            zeroize_q <= ustb[14];
            if (ustb[1]) key_valid_q <= 1'b1;
        end
    end

    // ------------------------------------------------------------------ register file, word unit, Keccak
    wire        kec_busy, kec_done, kec_wr_en;
    wire [5:0]  kec_rd_addr, kec_wr_addr;
    wire [63:0] kec_wr_data;
    wire        wu_wr = fn[0] && !op[4] && !unit_busy;
    px_rf u_rf (
        .clk(clk_core), .srst_n(secret_rst_n),
        .wr_en(kec_busy ? kec_wr_en : wu_wr),
        .wr_addr(kec_busy ? {1'b0, kec_wr_addr} : rb),
        .wr_data(kec_busy ? kec_wr_data : h),
        .rd_addr(kec_busy ? {1'b0, kec_rd_addr} : ra),
        .rd_data(rd_data)
    );
    qsag_keccak_serial u_kec (
        .clk(clk_core), .rst_n(rst_core_n), .srst_n(secret_rst_n), .start(ustb[0]), .turbo(fn[1]),
        .fault_inj(1'b0), .busy(kec_busy), .done(kec_done), .rd_addr(kec_rd_addr), .port(rd_data),
        .wr_en(kec_wr_en), .wr_addr(kec_wr_addr), .wr_data(kec_wr_data)
    );

    // organ words into the word unit
    wire [63:0] puf_word, puf_vmask, trng_word, db_clog, db_rlog, nfc_nonce, nfc_bind, fram_rx;
    wire [26:0] puf_syn;
    wire [31:0] dist_cycles;
    wire [15:0] nfc_flags, nfc_frames;
    wire [6:0]  db_rounds;
    wire [15:0] cnt_a, cnt_b;
    logic [63:0] organ, cst;
    always_comb begin
        unique case (fb[6:4])
            3'd0: organ = puf_word;
            3'd1: organ = trng_word;
            3'd2: organ = db_clog;
            3'd3: organ = db_rlog;
            3'd4: organ = nfc_nonce;
            3'd5: organ = nfc_bind;
            3'd6: organ = puf_vmask;
            default: organ = {dist_cycles, cnt_b, cnt_a};
        endcase
        unique case (fb[3:0])     // 64-bit constant table beside the ROM
            4'd0:  cst = 64'h0000000000000001;  4'd1:  cst = 64'h0000000000008082;
            4'd2:  cst = 64'h800000000000808A;  4'd3:  cst = 64'h8000000080008000;
            4'd4:  cst = 64'h000000000000808B;  4'd5:  cst = 64'h0000000080000001;
            4'd6:  cst = 64'h8000000080008081;  4'd7:  cst = 64'h8000000000008009;
            4'd8:  cst = 64'h44524547472E4B44;  4'd9:  cst = 64'h4556000000000000;
            4'd10: cst = 64'h44524547472E5055;  4'd11: cst = 64'h4643484B00000000;
            4'd12: cst = 64'hFFFFFFFF00000001;  4'd13: cst = 64'h1F00000000000000;
            4'd14: cst = 64'h0000000000000080;  default: cst = 64'h8000000000000000;
        endcase
    end
    px_wu3 u_wu (
        .clk(clk_core), .rst_n(secret_rst_n), .row(rd_data), .imm({fa, fb, ir[1:0]}), .use_imm(fn[1]),
        .alu(op[2:0]), .un({fn[3:2], ir[4:3]}), .src({ir[2], fn[3:2]}),
        .din(rx_word), .fld({nfc_flags, nfc_frames, 9'd0, puf_syn[22:0]}), .cst(cst), .fram(fram_rx), .gl(organ),
        .ld_h(!op[4] && !unit_busy), .clr_h(op == 5'd15), .clr_z(op == 5'd29),
        .h(h), .z(z), .cy(cy), .hz(hz)
    );

    // ------------------------------------------------------------------ host link
    wire tx_take;
    px_spi u_spi (
        .clk(clk_core), .rst_n(rst_core_n), .sck(sck), .cs_n(cs_n), .mosi(mosi), .miso(miso),
        .rx_word(rx_word), .rx_valid(rx_valid), .rx_take(ustb[15]),
        .tx_word(rd_data & {64{egress_ok}}), .tx_valid(egress_ok), .tx_take(tx_take),
        .diag({clk_diag, 8'd0, quad_trip, 4'd0, pc, 5'd0, keyed, dirty, hdr_done, 13'd0})
    );

    // ------------------------------------------------------------------ organs
    wire fram_done, fram_busy, fram_stb;
    qsag_anchor_spi u_fram (
        .clk(clk_core), .rst_n(rst_core_n), .div(4'd2), .start(ustb[3]), .write(fn[2]), .addr(h[15:0]),
        .stb(fram_stb), .go(ustb[4]), .rx(fram_rx), .tx(h), .done(fram_done), .busy(fram_busy),
        .cs_n(fram_cs_n), .sck(fram_sck), .mosi(fram_mosi), .miso(fram_miso)
    );

    wire trng_valid, trng_ok, rct_fail, apt_fail, trng_bit;
    px_trng8 u_trng (
        .clk(clk_core), .rst_n(rst_core_n), .en(1'b1), .take(ustb[2]), .word(trng_word),
        .valid(trng_valid), .ok(trng_ok), .rct_fail(rct_fail), .apt_fail(apt_fail), .raw_bit(trng_bit)
    );

    wire nfc_valid, nfc_crc_err;
    px_nfc u_nfc (
        .clk(clk_core), .rst_n(rst_core_n), .arst_n(rst_core_n), .srst_n(secret_rst_n),
        .nfc_clk_in(nfc_clk), .nfc_ask_in(nfc_ask), .token_consume(ustb[5]),
        .nfc_load_mod(nfc_lm), .token_valid(nfc_valid), .token_nonce(nfc_nonce),
        .token_digest_bind(nfc_bind), .token_quorum_flags(nfc_flags), .nfc_rx_frames(nfc_frames),
        .nfc_crc_err(nfc_crc_err)
    );

    wire db_armed, dist_valid, dist_timeout;
    dregg_distance_tdc u_db (
        .clk(clk_core), .rst_n(rst_core_n), .srst_n(secret_rst_n),
        .db_chal_pad_in(db_chal), .db_resp_pad_out(db_resp), .db_resp_pad_oe(db_resp_oe),
        .db_resp_pad_ie_force(db_resp_ie), .db_resp_pad_loopback(bidir_in[14]),
        .load_r0(ustb[6]), .load_r1(ustb[7]), .load_wdata(h), .arm_responder(ustb[8]),
        .step_round(ustb[9]), .launch_ping(ustb[10]), .cal_ping(ustb[11]), .dist_consume(ustb[12]),
        .responder_armed(db_armed), .rounds_done(db_rounds), .chal_log_lo(db_clog), .resp_log_lo(db_rlog),
        .dist_valid(dist_valid), .dist_timeout(dist_timeout), .dist_cycles(dist_cycles)
    );

    // PUF: the existing decoder leaf (BCH, counters, control, its own 64 rings) stands in for the
    // decoder and control; the 252-pair key array is the separate block the floorplan isolates.
    wire puf_busy, puf_done, puf_err, puf_mon;
    wire [5:0] puf_acc;
    wire [3:0] puf_corr;
    dregg_ro_puf_bch u_puf (
        .clk(clk_core), .rst_n(rst_core_n), .srst_n(secret_rst_n), .start_blk(ustb[1]), .recon_mode(fn[2]),
        .blk_sel(fb[2:0]), .margin_thresh(fb[5:0]), .noise_flips(3'd0), .vmask_in(h), .syn_in(h[26:0]),
        .mon_en(1'b0), .mon_beat(1'b0), .mon_idx(6'd0), .puf_mon_clk(puf_mon),
        .busy(puf_busy), .done(puf_done), .blk_err(puf_err), .vmask_out(puf_vmask), .syn_out(puf_syn),
        .word_out(puf_word), .accepted_in_blk(puf_acc), .corrected_in_blk(puf_corr)
    );
    logic [5:0] prow_q;
    logic [4:0] pcol_q;
    always_ff @(posedge clk_core or negedge rst_core_n) begin
        if (!rst_core_n) begin prow_q <= '0; pcol_q <= '0; end
        else if (puf_done) begin
            pcol_q <= (pcol_q == 5'd23) ? 5'd0 : pcol_q + 5'd1;
            if (pcol_q == 5'd23) prow_q <= (prow_q == 6'd41) ? 6'd0 : prow_q + 6'd1;
        end
    end
    wire arr_osc;
    px_puf_array u_pufarr (.en(puf_busy), .row(prow_q), .col(pcol_q), .osc(arr_osc));
    dregg_ripple_cnt #(.N(16)) u_pufcnt_a (.clk(arr_osc), .rst_n(puf_busy), .q(cnt_a));
    dregg_ripple_cnt #(.N(16)) u_pufcnt_b (.clk(puf_mon), .rst_n(puf_busy), .q(cnt_b));

    dregg_shield_canaries u_shield (
        .clk(clk_core), .rst_n(rst_core_n), .canary_arm(prov_q), .canary_tap(fb[2:0]), .shield_en(prov_q),
        .trng_bit(trng_bit), .fib_cut_inj(1'b0), .fault_quad_glitch(fault_glitch),
        .fault_shield(fault_shield), .quad_trip_map(quad_trip)
    );

    assign unit_busy = kec_busy | puf_busy | fram_busy;

    // ------------------------------------------------------------------ status pads
    always_ff @(posedge clk_core or negedge rst_core_n) begin
        if (!rst_core_n) begin fault_q <= 1'b0; irq_q <= 1'b0; end
        else begin
            fault_q <= seq_fault | tamper_latched | clk_fault | rct_fail | apt_fail | puf_err | nfc_crc_err;
            irq_q   <= rx_valid | tx_take | kec_done | fram_done | fram_stb | puf_done | nfc_valid | dist_valid
                       | dist_timeout | db_armed | trng_valid | trng_ok | (|db_rounds) | (|puf_acc) | (|puf_corr);
        end
    end
    always_ff @(posedge clk or negedge rst_n) if (!rst_n) clkmon_q <= 1'b0; else clkmon_q <= ~clkmon_q;
endmodule
`default_nettype wire
