// Dregg-180 Organ 3: Contactless 13.56 MHz HF-NFC Air-Gap Port + 32-Bit Phase-Continuous NCO.
//
// GOTCHA #2 & Subcarbon R0 Trap T5 silicon fix + unified shift-storage trim:
//   * Clocks a dedicated 6-bit prescaler + half-bit ASK sampler directly off `nfc_clk_buf`
//     (13.56 MHz Schmitt bi_24t input, asynchronous reset `arst_n`).
//   * Generates zero-jitter `847.5 kHz` (`13.56 MHz / 16`) subcarrier directly in `nfc_clk`
//     to gate `nfc_load_mod`, and crosses ONLY the slow half-bit toggle + sampled ASK bit into
//     `clk_core` — eliminating Nyquist aliasing from 2 MHz to 150 MHz `clk_core`!
//   * Unified `pay_sr[143:0]` + `crc_reg[15:0]` eliminates 160 duplicate token storage FFs:
//     checking CRC-16 over all 160 bits (`crc_after_160 == 16'h0000`) holds the approved
//     144-bit token `(nonce, digest_bind, quorum_flags)` directly inside `pay_sr` until consumed!
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
    logic [1:0] nst;
    logic       half_idx;
    logic [31:0] ack_sr;
    wire tx_manchester_core = ack_sr[31] ? ~half_idx : half_idx;

    // ------------------------------------------------------------ 13.56 MHz Front-End Domain
    wire nfc_clk_buf, nfc_rst_n, ask_n_s;
    qsag_clkbuf   u_ncb (.a(nfc_clk_in), .y(nfc_clk_buf));
    qsag_rst_sync u_nrs (.clk(nfc_clk_buf), .arst_n(arst_n), .rst_n(nfc_rst_n));
    qsag_sync2 #(.RV(1'b1)) u_nas (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nfc_ask_in), .q(ask_n_s));

    wire fast_hb_s, tx_act_n, tx_env_n, frame_busy_n;
    qsag_sync2 #(.RV(1'b0)) u_fhs (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nco_sym_shift[3]),     .q(fast_hb_s));
    qsag_sync2 #(.RV(1'b0)) u_txa (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nst == N_TX_ACK),      .q(tx_act_n));
    qsag_sync2 #(.RV(1'b0)) u_txe (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(tx_manchester_core),   .q(tx_env_n));
    qsag_sync2 #(.RV(1'b0)) u_fbn (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nst != N_IDLE),        .q(frame_busy_n));

    wire [5:0] hb_mid = fast_hb_s ? 6'd7  : 6'd31;
    wire [5:0] hb_end = fast_hb_s ? 6'd15 : 6'd63;

    logic [5:0] nfc_cdiv;
    logic       ask_n_prev;
    logic       in_frame_n;
    logic       hb_tgl_n;
    logic       hb_val_n;
    logic       hb_end_tgl_n;

    wire subcarrier_847k = nfc_cdiv[3];
    assign nfc_load_mod  = tx_act_n & tx_env_n & subcarrier_847k;

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
    logic [143:0] pay_sr;   // holds only the 144 token bits directly (zero duplicate token FFs!)
    logic [15:0]  crc_reg;

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
            pay_sr        <= '0;
            crc_reg       <= 16'h6363;
            ack_sr        <= '0;
            token_valid   <= 1'b0;
            nfc_rx_frames <= '0;
            nfc_crc_err   <= 1'b0;
        end else begin
            hb_tgl_q <= hb_tgl_c;
            hb_end_q <= hb_end_c;
            if (token_consume) begin
                token_valid <= 1'b0;
                pay_sr      <= '0;
            end

            unique case (nst)
                N_IDLE: begin
                    // Lock pay_sr while an unconsumed valid token is held!
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
                                end else begin
                                    nst <= N_IDLE;
                                end
                            end else begin
                                bit_cnt <= bit_cnt + 8'd1;
                            end
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
                    end else begin
                        if (bit_cnt < 8'd144) begin
                            pay_sr  <= {pay_sr[142:0], h0_sample};
                            crc_reg <= crc16_step(crc_reg, h0_sample);
                            bit_cnt <= bit_cnt + 8'd1;
                        end else begin
                            // Bits 144..159 are MSB-first CRC-16: compare bit-by-bit against crc_reg[15]!
                            crc_reg <= {crc_reg[14:0], 1'b0};
                            if (crc_reg[15] != h0_sample) begin
                                nfc_crc_err <= 1'b1;
                                pay_sr      <= '0;
                                nst         <= N_IDLE;
                            end else if (bit_cnt == 8'd159) begin
                                token_valid   <= 1'b1;
                                nfc_rx_frames <= nfc_rx_frames + 16'd1;
                                ack_sr        <= {8'h5A, pay_sr[15:0], (8'hA5 ^ pay_sr[7:0])};
                                bit_cnt       <= 8'd0;
                                half_idx      <= 1'b0;
                                nst           <= N_TX_ACK;
                            end else begin
                                bit_cnt <= bit_cnt + 8'd1;
                            end
                        end
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
    logic [31:0] chirp_ftw;
    logic [79:0] fsk_sr;   // 16-bit sync 16'hD391 + 64-bit beacon word
    logic [6:0]  fsk_bits;
    logic [15:0] sym_cnt;

    wire [15:0] sym_lim = (16'd8 << nco_sym_shift[2:0]) - 16'd1;
    assign nco_tx_active = (fsk_bits != 7'd0);

    logic [31:0] ftw_eff;
    always_comb begin
        unique case (nco_mode)
            2'd1:    ftw_eff = nco_tx_active
                               ? (fsk_sr[79] ? (nco_ftw_base + nco_ftw_delta) : (nco_ftw_base - nco_ftw_delta))
                               : nco_ftw_base;
            2'd2:    ftw_eff = chirp_ftw;
            default: ftw_eff = nco_ftw_base;
        endcase
    end

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            phase_acc <= '0;
            chirp_ftw <= '0;
            fsk_sr    <= '0;
            fsk_bits  <= '0;
            sym_cnt   <= '0;
        end else begin
            if (nco_pkt_load) begin
                fsk_sr    <= {16'hD391, nco_pkt_data};
                fsk_bits  <= 7'd80;
                sym_cnt   <= 16'd0;
                chirp_ftw <= nco_ftw_base;
            end else if (nco_en) begin
                phase_acc <= phase_acc + ftw_eff;
                if (nco_mode == 2'd2) begin
                    if (sym_cnt == sym_lim) begin
                        sym_cnt   <= 16'd0;
                        chirp_ftw <= chirp_ftw + nco_ftw_delta;
                    end else begin
                        sym_cnt <= sym_cnt + 16'd1;
                    end
                end else if (nco_tx_active) begin
                    if (sym_cnt == sym_lim) begin
                        sym_cnt  <= 16'd0;
                        fsk_sr   <= {fsk_sr[78:0], 1'b0};
                        fsk_bits <= fsk_bits - 7'd1;
                    end else begin
                        sym_cnt <= sym_cnt + 16'd1;
                    end
                end
            end
        end
    end

    assign nco_rf_out = nco_en & phase_acc[31];
endmodule
`default_nettype wire
