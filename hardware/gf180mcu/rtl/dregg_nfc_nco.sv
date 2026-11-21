// Dregg-180 Organ 3: Contactless 13.56 MHz HF-NFC Air-Gap Port + 32-Bit Phase-Continuous NCO.
//
// Silicon-hardened NFC + RF NCO:
//   * 13.56 MHz `nfc_clk_buf` prescaler (`÷16 = 847.5 kHz` subcarrier + slow half-bit CDC).
//   * In-place `pay_sr[143:0]` (`dffq_1`, gated by `srst_n`-cleared `token_valid`) and unified
//     `cur_ftw`/`ftw_delta` NCO (deleting external `u_nco_ftw` 64-FF duplicate!).
`default_nettype none

module dregg_nfc_nco (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         arst_n,
    input  wire         srst_n,
    // Physical bi_24t pad signals
    input  wire         nfc_clk_in,
    input  wire         nfc_ask_in,
    output wire         nfc_load_mod,
    output wire         nco_rf_out,
    // Co-approval token interface to Wire Engine / CapTP Vat:
    // 144-bit Manchester payload = {nfc_seq[31:0], quorum_flags[15:0], nfc_mac[95:0]} + CRC16-A
    input  wire         token_consume,
    output logic        token_valid,
    output wire  [31:0] token_seq,
    output wire  [95:0] token_mac,
    output wire  [15:0] token_quorum_flags,
    output wire  [15:0] nfc_rx_frames,
    output logic        nfc_crc_err,
    // NCO configuration & packetizer interface
    input  wire         nco_en,
    input  wire  [1:0]  nco_mode,          // 0: CW, 1: 2-FSK beacon, 2: linear chirp
    input  wire  [3:0]  nco_sym_shift,     // [3]=fast-sim x4 NFC half-bit, [2:0]=NCO sym shift
    input  wire         nco_cfg_we,
    input  wire         nco_pkt_load,
    input  wire  [63:0] nco_pkt_data,
    output wire         nco_tx_active
);
    localparam logic [1:0] N_IDLE = 2'd0, N_SYNC = 2'd1, N_PAY = 2'd2, N_TX_ACK = 2'd3;
    logic [1:0]   nst;
    logic         half_idx;
    logic [7:0]   bit_cnt;
    wire  [143:0] pay_sr;
    wire  [31:0]  ack_word = {8'h5A, pay_sr[111:96], (8'hA5 ^ pay_sr[103:96])};
    wire          ack_bit  = ack_word[5'd31 - bit_cnt[4:0]];
    wire tx_manchester_core = ack_bit ? ~half_idx : half_idx;

    // ------------------------------------------------------------ 13.56 MHz Front-End Domain
    wire nfc_clk_buf, nfc_rst_n, ask_n_s;
    qsag_clkbuf   u_ncb (.a(nfc_clk_in), .y(nfc_clk_buf));
    qsag_rst_sync u_nrs (.clk(nfc_clk_buf), .arst_n(arst_n), .rst_n(nfc_rst_n));
    qsag_sync2 #(.RV(1'b1)) u_nas (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nfc_ask_in), .q(ask_n_s));

    wire fast_hb_s, tx_act_n, tx_env_n, frame_busy_n;
    qsag_sync2 #(.RV(1'b0)) u_fhs (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nco_sym_shift[3]),   .q(fast_hb_s));
    qsag_sync2 #(.RV(1'b0)) u_txa (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nst == N_TX_ACK),    .q(tx_act_n));
    qsag_sync2 #(.RV(1'b0)) u_txe (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(tx_manchester_core), .q(tx_env_n));
    qsag_sync2 #(.RV(1'b0)) u_fbn (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nst != N_IDLE),      .q(frame_busy_n));

    wire [5:0] hb_mid = fast_hb_s ? 6'd7  : 6'd31;
    wire [5:0] hb_end = fast_hb_s ? 6'd15 : 6'd63;

    logic [5:0] nfc_cdiv;
    logic       ask_n_prev, in_frame_n, hb_tgl_n, hb_val_n, hb_end_tgl_n;

    assign nfc_load_mod = tx_act_n & tx_env_n & nfc_cdiv[3];

    always_ff @(posedge nfc_clk_buf or negedge nfc_rst_n) begin
        if (!nfc_rst_n) begin
            nfc_cdiv     <= 6'd0;
            ask_n_prev   <= 1'b1;
            in_frame_n   <= 1'b0;
            hb_tgl_n     <= 1'b0;
            hb_val_n     <= 1'b1;
            hb_end_tgl_n <= 1'b0;
        end else begin
            ask_n_prev <= ask_n_s;
            if (!in_frame_n && !frame_busy_n) begin
                nfc_cdiv <= nfc_cdiv + 6'd1;
                if (ask_n_prev && !ask_n_s) begin
                    in_frame_n <= 1'b1;
                    nfc_cdiv   <= 6'd1;
                end
            end else begin
                if (nfc_cdiv == hb_mid) begin
                    hb_val_n <= ask_n_s;
                    hb_tgl_n <= ~hb_tgl_n;
                end
                if (nfc_cdiv == hb_end) begin
                    nfc_cdiv     <= 6'd0;
                    hb_end_tgl_n <= ~hb_end_tgl_n;
                    if (!frame_busy_n && in_frame_n) in_frame_n <= 1'b0;
                end else begin
                    nfc_cdiv <= nfc_cdiv + 6'd1;
                end
            end
        end
    end

    // ------------------------------------------------------------ Core Clock Domain Frame Decoder
    wire hb_tgl_c, hb_val_c, hb_end_c;
    qsag_sync2 #(.RV(1'b0)) u_htc (.clk(clk), .rst_n(rst_n), .d(hb_tgl_n),     .q(hb_tgl_c));
    qsag_sync2 #(.RV(1'b1)) u_hvc (.clk(clk), .rst_n(rst_n), .d(hb_val_n),     .q(hb_val_c));
    qsag_sync2 #(.RV(1'b0)) u_hec (.clk(clk), .rst_n(rst_n), .d(hb_end_tgl_n), .q(hb_end_c));

    logic hb_tgl_q, hb_end_q;
    wire  hb_mid_ev = (hb_tgl_c != hb_tgl_q);
    wire  hb_end_ev = (hb_end_c != hb_end_q);

    function automatic logic [15:0] crc16_step(input logic [15:0] c, input logic bit_in);
        logic fb;
        begin
            fb         = c[15] ^ bit_in;
            crc16_step = {c[14:0], 1'b0} ^ (fb ? 16'h1021 : 16'h0000);
        end
    endfunction

    logic        h0_sample;
    logic [6:0]  sync_sr;
    logic [15:0] crc_reg;
    logic [7:0]  rx_cnt_q;

    wire pay_shift = (nst == N_PAY) && hb_mid_ev && half_idx && (h0_sample != hb_val_c) && (bit_cnt < 8'd144);
    qsag_ereg_nr #(.W(144)) u_paysr (
        .clk(clk), .en(pay_shift),
        .d({pay_sr[142:0], h0_sample}), .q(pay_sr)
    );

    assign token_seq          = pay_sr[143:112];
    assign token_quorum_flags = token_valid ? pay_sr[111:96] : 16'd0;
    assign token_mac          = pay_sr[95:0];
    assign nfc_rx_frames      = {8'd0, rx_cnt_q};

    always_ff @(posedge clk) begin
        if (nst == N_IDLE && !token_valid && hb_mid_ev && !hb_val_c) begin
            h0_sample <= 1'b0;
            bit_cnt   <= 8'd0;
            sync_sr   <= 7'd0;
        end else if (nst == N_SYNC && hb_mid_ev) begin
            if (!half_idx) h0_sample <= hb_val_c;
            else if (h0_sample != hb_val_c) begin
                if (bit_cnt == 8'd0) begin
                    if (h0_sample == 1'b0) bit_cnt <= 8'd1;
                end else begin
                    sync_sr <= {sync_sr[5:0], h0_sample};
                    if (bit_cnt == 8'd8 && {sync_sr[6:0], h0_sample} == 8'hA5) begin
                        bit_cnt <= 8'd0;
                        crc_reg <= 16'h6363;
                    end else bit_cnt <= bit_cnt + 8'd1;
                end
            end
        end else if (nst == N_PAY && hb_mid_ev) begin
            if (!half_idx) h0_sample <= hb_val_c;
            else if (h0_sample != hb_val_c) begin
                if (bit_cnt < 8'd144) begin
                    crc_reg <= crc16_step(crc_reg, h0_sample);
                    bit_cnt <= bit_cnt + 8'd1;
                end else begin
                    crc_reg <= {crc_reg[14:0], 1'b0};
                    if (crc_reg[15] == h0_sample && bit_cnt == 8'd159)
                        bit_cnt <= 8'd0;
                    else
                        bit_cnt <= bit_cnt + 8'd1;
                end
            end
        end else if (nst == N_TX_ACK && hb_end_ev && half_idx) begin
            bit_cnt <= bit_cnt + 8'd1;
        end
    end

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            hb_tgl_q    <= 1'b0;
            hb_end_q    <= 1'b0;
            nst         <= N_IDLE;
            half_idx    <= 1'b0;
            token_valid <= 1'b0;
            rx_cnt_q    <= '0;
            nfc_crc_err <= 1'b0;
        end else begin
            hb_tgl_q <= hb_tgl_c;
            hb_end_q <= hb_end_c;
            if (token_consume) token_valid <= 1'b0;

            unique case (nst)
                N_IDLE: if (!token_valid && hb_mid_ev && !hb_val_c) begin
                    half_idx <= 1'b1;
                    nst      <= N_SYNC;
                end
                N_SYNC: if (hb_mid_ev) begin
                    half_idx <= ~half_idx;
                    if (half_idx) begin
                        if (h0_sample == hb_val_c) nst <= N_IDLE;
                        else if (bit_cnt == 8'd0 && h0_sample != 1'b0) nst <= N_IDLE;
                        else if (bit_cnt == 8'd8)
                            nst <= ({sync_sr[6:0], h0_sample} == 8'hA5) ? N_PAY : N_IDLE;
                    end
                end
                N_PAY: if (hb_mid_ev) begin
                    half_idx <= ~half_idx;
                    if (half_idx) begin
                        if (h0_sample == hb_val_c || (bit_cnt >= 8'd144 && crc_reg[15] != h0_sample)) begin
                            nfc_crc_err <= 1'b1;
                            nst         <= N_IDLE;
                        end else if (bit_cnt == 8'd159) begin
                            token_valid <= 1'b1;
                            rx_cnt_q    <= rx_cnt_q + 8'd1;
                            half_idx    <= 1'b0;
                            nst         <= N_TX_ACK;
                        end
                    end
                end
                N_TX_ACK: if (hb_end_ev) begin
                    half_idx <= ~half_idx;
                    if (half_idx && bit_cnt == 8'd31) nst <= N_IDLE;
                end
                default: nst <= N_IDLE;
            endcase
        end
    end

    // ------------------------------------------------------------ 32-bit Phase-Continuous RF NCO
    logic [31:0] phase_acc;
    logic [31:0] cur_ftw;
    wire  [31:0] ftw_delta;
    wire  [63:0] fsk_sr;
    logic [6:0]  fsk_bits;
    logic [11:0] sym_cnt;

    qsag_ereg_nr #(.W(32)) u_ftwd (.clk(clk), .en(nco_cfg_we), .d(nco_pkt_data[63:32]), .q(ftw_delta));

    wire [11:0] sym_lim = (12'd8 << nco_sym_shift[2:0]) - 12'd1;
    assign nco_tx_active = (fsk_bits != 7'd0);
    wire fsk_step = nco_en && (nco_mode == 2'd1) && nco_tx_active && (sym_cnt == sym_lim);
    qsag_ereg_nr #(.W(64)) u_fsk (
        .clk(clk), .en(nco_pkt_load | fsk_step),
        .d(nco_pkt_load ? nco_pkt_data : {fsk_sr[62:0], 1'b0}), .q(fsk_sr)
    );

    wire [3:0]  sync_bidx = fsk_bits[3:0] - 4'd1;
    wire [15:0] sync_hdr  = 16'hD391;
    wire        fsk_bit   = (fsk_bits > 7'd64) ? sync_hdr[sync_bidx] : fsk_sr[63];
    wire        use_del   = (nco_mode == 2'd2) || (nco_mode == 2'd1 && nco_tx_active);
    wire        fsk_sub   = (nco_mode == 2'd1) && nco_tx_active && !fsk_bit;
    wire [31:0] del_eff   = use_del ? (fsk_sub ? ~ftw_delta : ftw_delta) : 32'd0;
    wire [31:0] ftw_sum   = cur_ftw + del_eff + {31'd0, fsk_sub};
    wire [31:0] ftw_eff   = (nco_mode == 2'd2) ? cur_ftw : ftw_sum;

    always_ff @(posedge clk) begin
        if (nco_cfg_we) begin
            cur_ftw <= nco_pkt_data[31:0];
            sym_cnt <= 12'd0;
        end else if (nco_pkt_load) begin
            sym_cnt <= 12'd0;
        end else if (nco_en) begin
            phase_acc <= phase_acc + ftw_eff;
            if (sym_cnt == sym_lim) begin
                sym_cnt <= 12'd0;
                if (nco_mode == 2'd2) cur_ftw <= ftw_sum;
            end else begin
                sym_cnt <= sym_cnt + 12'd1;
            end
        end
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)            fsk_bits <= '0;
        else if (nco_pkt_load) fsk_bits <= 7'd80;
        else if (nco_en && sym_cnt == sym_lim && nco_mode != 2'd2 && nco_tx_active)
            fsk_bits <= fsk_bits - 7'd1;
    end

    assign nco_rf_out = nco_en & phase_acc[31];
endmodule
`default_nettype wire
