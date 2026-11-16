// Dregg-180 Organ 3: Contactless 13.56 MHz HF-NFC Air-Gap Port + 32-Bit Phase-Continuous NCO.
//
// Ultra-compact (~4.0 kGE!) silicon-hardened NFC + RF NCO:
//   * 13.56 MHz `nfc_clk_buf` prescaler (`÷16 = 847.5 kHz` subcarrier + slow half-bit CDC, Trap T5).
//   * In-place `pay_sr[143:0]` (`dffq_1` via `qsag_ereg_nr`, gated by `srst_n`-cleared `token_valid`)
//     and 64-bit `fsk_sr` (`dffq_1`), sharing ONE 32-bit frequency adder across CW/FSK/Chirp modes!
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
    // Co-approval token interface to CapTP Vat
    input  wire         token_consume,
    output logic        token_valid,
    output wire  [63:0] token_nonce,
    output wire  [63:0] token_digest_bind,
    output wire  [15:0] token_quorum_flags,
    output logic [15:0] nfc_rx_frames,
    output logic        nfc_crc_err,
    // NCO configuration & packetizer interface
    input  wire         nco_en,
    input  wire  [1:0]  nco_mode,          // 0: CW, 1: 2-FSK beacon, 2: linear chirp
    input  wire  [3:0]  nco_sym_shift,     // [3]=fast-sim x4 NFC half-bit, [2:0]=NCO sym shift
    input  wire  [31:0] nco_ftw_base,
    input  wire  [31:0] nco_ftw_delta,
    input  wire         nco_pkt_load,
    input  wire  [63:0] nco_pkt_data,
    output wire         nco_tx_active
);
    localparam logic [1:0] N_IDLE = 2'd0, N_SYNC = 2'd1, N_PAY = 2'd2, N_TX_ACK = 2'd3;
    logic [1:0]  nst;
    logic        half_idx;
    logic [31:0] ack_sr;
    wire tx_manchester_core = ack_sr[31] ? ~half_idx : half_idx;

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

    logic         h0_sample;
    logic [7:0]   bit_cnt;
    logic [7:0]   sync_sr;
    logic [15:0]  crc_reg;
    wire  [143:0] pay_sr;

    wire pay_shift = (nst == N_PAY) && hb_mid_ev && half_idx && (h0_sample != hb_val_c) && (bit_cnt < 8'd144);
    wire pay_wipe  = !srst_n || token_consume;
    qsag_ereg_nr #(.W(144)) u_paysr (
        .clk(clk), .en(pay_wipe | pay_shift),
        .d(pay_wipe ? 144'd0 : {pay_sr[142:0], h0_sample}), .q(pay_sr)
    );

    assign token_nonce        = token_valid ? pay_sr[143:80] : 64'd0;
    assign token_digest_bind  = token_valid ? pay_sr[79:16]  : 64'd0;
    assign token_quorum_flags = token_valid ? pay_sr[15:0]   : 16'd0;

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            hb_tgl_q      <= 1'b0;
            hb_end_q      <= 1'b0;
            nst           <= N_IDLE;
            half_idx      <= 1'b0;
            h0_sample     <= 1'b0;
            bit_cnt       <= '0;
            sync_sr       <= '0;
            crc_reg       <= 16'h6363;
            ack_sr        <= '0;
            token_valid   <= 1'b0;
            nfc_rx_frames <= '0;
            nfc_crc_err   <= 1'b0;
        end else begin
            hb_tgl_q <= hb_tgl_c;
            hb_end_q <= hb_end_c;
            if (token_consume) token_valid <= 1'b0;

            unique case (nst)
                N_IDLE: begin
                    if (!token_valid && hb_mid_ev && !hb_val_c) begin
                        h0_sample <= 1'b0;
                        half_idx  <= 1'b1;
                        bit_cnt   <= 8'd0;
                        sync_sr   <= 8'd0;
                        nst       <= N_SYNC;
                    end
                end
                N_SYNC: if (hb_mid_ev) begin
                    half_idx <= ~half_idx;
                    if (!half_idx) begin
                        h0_sample <= hb_val_c;
                    end else if (h0_sample == hb_val_c) begin
                        nst <= N_IDLE;
                    end else begin
                        if (bit_cnt == 8'd0) begin
                            if (h0_sample != 1'b0) nst <= N_IDLE;
                            else                   bit_cnt <= 8'd1;
                        end else begin
                            sync_sr <= {sync_sr[6:0], h0_sample};
                            if (bit_cnt == 8'd8) begin
                                if ({sync_sr[6:0], h0_sample} == 8'hA5) begin
                                    bit_cnt <= 8'd0;
                                    crc_reg <= 16'h6363;
                                    nst     <= N_PAY;
                                end else nst <= N_IDLE;
                            end else bit_cnt <= bit_cnt + 8'd1;
                        end
                    end
                end
                N_PAY: if (hb_mid_ev) begin
                    half_idx <= ~half_idx;
                    if (!half_idx) begin
                        h0_sample <= hb_val_c;
                    end else if (h0_sample == hb_val_c) begin
                        nfc_crc_err <= 1'b1;
                        nst         <= N_IDLE;
                    end else if (bit_cnt < 8'd144) begin
                        crc_reg <= crc16_step(crc_reg, h0_sample);
                        bit_cnt <= bit_cnt + 8'd1;
                    end else begin
                        crc_reg <= {crc_reg[14:0], 1'b0};
                        if (crc_reg[15] != h0_sample) begin
                            nfc_crc_err <= 1'b1;
                            nst         <= N_IDLE;
                        end else if (bit_cnt == 8'd159) begin
                            token_valid   <= 1'b1;
                            nfc_rx_frames <= nfc_rx_frames + 16'd1;
                            ack_sr        <= {8'h5A, pay_sr[15:0], (8'hA5 ^ pay_sr[7:0])};
                            bit_cnt       <= 8'd0;
                            half_idx      <= 1'b0;
                            nst           <= N_TX_ACK;
                        end else bit_cnt <= bit_cnt + 8'd1;
                    end
                end
                N_TX_ACK: if (hb_end_ev) begin
                    half_idx <= ~half_idx;
                    if (half_idx) begin
                        ack_sr <= {ack_sr[30:0], 1'b0};
                        if (bit_cnt == 8'd31) nst <= N_IDLE;
                        else                  bit_cnt <= bit_cnt + 8'd1;
                    end
                end
                default: nst <= N_IDLE;
            endcase
        end
    end

    // ------------------------------------------------------------ 32-bit Phase-Continuous RF NCO
    logic [31:0] phase_acc;
    logic [31:0] cur_ftw;
    wire  [63:0] fsk_sr;
    logic [6:0]  fsk_bits;
    logic [11:0] sym_cnt;

    wire [11:0] sym_lim = (12'd8 << nco_sym_shift[2:0]) - 12'd1;
    assign nco_tx_active = (fsk_bits != 7'd0);
    wire fsk_step = nco_en && (nco_mode == 2'd1) && nco_tx_active && (sym_cnt == sym_lim);
    qsag_ereg_nr #(.W(64)) u_fsk (
        .clk(clk), .en(nco_pkt_load | fsk_step),
        .d(nco_pkt_load ? nco_pkt_data : {fsk_sr[62:0], 1'b0}), .q(fsk_sr)
    );

    wire fsk_bit = (fsk_bits > 7'd64) ? (16'hD391 >> (fsk_bits - 7'd65)) & 1'b1 : fsk_sr[63];
    // Share ONE 32-bit delta adder for both 2-FSK (+/- delta) and linear FM chirp (+ delta)!
    wire fsk_sub          = (nco_mode == 2'd1) && nco_tx_active && !fsk_bit;
    wire [31:0] add_lhs   = (nco_mode == 2'd2) ? cur_ftw : nco_ftw_base;
    wire [31:0] add_rhs   = ((nco_mode == 2'd1 && !nco_tx_active) || nco_mode == 2'd0)
                            ? 32'd0 : (fsk_sub ? ~nco_ftw_delta : nco_ftw_delta);
    wire [31:0] ftw_sum   = add_lhs + add_rhs + {31'd0, fsk_sub};
    wire [31:0] ftw_eff   = (nco_mode == 2'd2) ? cur_ftw : ftw_sum;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            phase_acc <= '0;
            cur_ftw   <= '0;
            fsk_bits  <= '0;
            sym_cnt   <= '0;
        end else if (nco_pkt_load) begin
            fsk_bits <= 7'd80;
            sym_cnt  <= 12'd0;
            cur_ftw  <= nco_ftw_base;
        end else if (nco_en) begin
            phase_acc <= phase_acc + ftw_eff;
            if (sym_cnt == sym_lim) begin
                sym_cnt <= 12'd0;
                if (nco_mode == 2'd2) cur_ftw <= ftw_sum;
                else if (nco_tx_active) fsk_bits <= fsk_bits - 7'd1;
            end else begin
                sym_cnt <= sym_cnt + 12'd1;
            end
        end
    end

    assign nco_rf_out = nco_en & phase_acc[31];
endmodule
`default_nettype wire
