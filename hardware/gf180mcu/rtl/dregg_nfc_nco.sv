// Dregg-180 Organ 3: Contactless 13.56 MHz HF-NFC Air-Gap Port + 32-Bit Phase-Continuous NCO.
//
// GOTCHA #2 silicon fix:
//   * Clocks a dedicated 7-bit prescaler + half-bit ASK sampler directly off `nfc_clk_buf`
//     (13.56 MHz Schmitt bi_24t input, asynchronous reset `arst_n`, declared in SDC as an
//     independent 73.74 ns clock group!).
//   * Generates zero-jitter `847.5 kHz` (`13.56 MHz / 16`) subcarrier directly in the `nfc_clk`
//     domain to gate `nfc_load_mod`, and crosses ONLY the slow `211.875 kHz` (`4.72 us`) half-bit
//     toggle + sampled ASK bit into `clk_core` — eliminating Nyquist aliasing even at 25 MHz
//     `EXT_CLK_BYPASS` or 5 MHz bench bring-up!
`default_nettype none

module dregg_nfc_nco (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         arst_n,            // pad async reset for 13.56 MHz carrier prescaler
    input  wire         srst_n,
    // Physical bi_24t pad signals
    input  wire         nfc_clk_in,        // 13.56 MHz carrier (Schmitt bi_24t)
    input  wire         nfc_ask_in,        // Manchester ASK envelope input (bi_24t)
    output wire         nfc_load_mod,      // 847.5 kHz resistive load-modulation TX (bi_24t)
    output wire         nco_rf_out,        // 32-bit phase-continuous RF output (bi_24t)
    // Co-approval token interface to CapTP Vat
    input  wire         token_consume,
    output logic        token_valid,
    output logic [63:0] token_nonce,
    output logic [63:0] token_digest_bind,
    output logic [15:0] token_quorum_flags,
    output logic [15:0] nfc_rx_frames,
    output logic        nfc_crc_err,
    // NCO configuration & packetizer interface
    input  wire         nco_en,
    input  wire  [1:0]  nco_mode,          // 0: CW, 1: 2-FSK beacon, 2: linear chirp
    input  wire  [3:0]  nco_sym_shift,     // [3]=fast-sim x8 NFC half-bit, [2:0]=NCO sym shift
    input  wire  [31:0] nco_ftw_base,
    input  wire  [31:0] nco_ftw_delta,
    input  wire         nco_pkt_load,
    input  wire  [63:0] nco_pkt_data,
    output wire         nco_tx_active
);
    // ------------------------------------------------------------ 13.56 MHz Front-End Domain
    wire nfc_clk_buf, nfc_rst_n, ask_n_s;
    qsag_clkbuf u_ncb (.a(nfc_clk_in), .y(nfc_clk_buf));
    qsag_rst_sync u_nrs (.clk(nfc_clk_buf), .arst_n(arst_n), .rst_n(nfc_rst_n));
    qsag_sync2 #(.RV(1'b1)) u_nas (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nfc_ask_in), .q(ask_n_s));

    wire  fast_hb_s;
    qsag_sync2 #(.RV(1'b0)) u_fhs (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nco_sym_shift[3]), .q(fast_hb_s));

    // In fast-sim mode (`nco_sym_shift[3]=1`), 16 carrier cycles per half-bit (780 ns -> safe up
    // to 10 MHz clk_core); in standard ISO-14443A mode (`0`), 64 carrier cycles per half-bit
    // (`4.72 us` -> safe down to 1 MHz clk_core!). Subcarrier `nfc_cdiv[3]` is ALWAYS /16 = 847.5 kHz!
    wire [5:0] hb_mid = fast_hb_s ? 6'd7  : 6'd31;
    wire [5:0] hb_end = fast_hb_s ? 6'd15 : 6'd63;

    logic [5:0] nfc_cdiv;
    logic       ask_n_prev;
    logic       in_frame_n;
    logic       hb_tgl_n;
    logic       hb_val_n;
    logic       hb_end_tgl_n;

    wire tx_act_n, tx_env_n;
    qsag_sync2 #(.RV(1'b0)) u_txa (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nst == N_TX_ACK), .q(tx_act_n));
    qsag_sync2 #(.RV(1'b0)) u_txe (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(tx_manchester_core), .q(tx_env_n));

    wire subcarrier_847k = nfc_cdiv[3]; // true 13.56 MHz / 16 = 847.5 kHz!
    assign nfc_load_mod  = tx_act_n & tx_env_n & subcarrier_847k;

    wire frame_busy_n;
    qsag_sync2 #(.RV(1'b0)) u_fbn (.clk(nfc_clk_buf), .rst_n(nfc_rst_n), .d(nst != N_IDLE), .q(frame_busy_n));

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
                nfc_cdiv <= nfc_cdiv + 6'd1; // keep /16 subcarrier free-running
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

    localparam logic [1:0] N_IDLE = 2'd0, N_SYNC = 2'd1, N_PAY = 2'd2, N_TX_ACK = 2'd3;
    logic [1:0]   nst;
    logic         half_idx;
    logic         h0_sample;
    logic [7:0]   bit_cnt;
    logic [7:0]   sync_sr;
    logic [159:0] pay_sr;
    logic [15:0]  crc_reg;
    logic [31:0]  ack_sr;

    wire tx_manchester_core = ack_sr[31] ? ~half_idx : half_idx;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
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
            nfc_rx_frames <= '0;
            nfc_crc_err   <= 1'b0;
        end else begin
            hb_tgl_q <= hb_tgl_c;
            hb_end_q <= hb_end_c;

            unique case (nst)
                N_IDLE: begin
                    if (hb_mid_ev && !hb_val_c) begin
                        // First mid-half-bit sample after falling start edge: h0 = 0 of start bit!
                        h0_sample <= 1'b0;
                        half_idx  <= 1'b1; // next mid-event will be h1 of start bit
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
                        logic dec_bit;
                        dec_bit = h0_sample;
                        if (bit_cnt == 8'd0) begin
                            if (dec_bit != 1'b0) nst <= N_IDLE;
                            else                 bit_cnt <= 8'd1;
                        end else begin
                            sync_sr <= {sync_sr[6:0], dec_bit};
                            if (bit_cnt == 8'd8) begin
                                if ({sync_sr[6:0], dec_bit} == 8'hA5) begin
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
                        logic dec_bit;
                        dec_bit = h0_sample;
                        pay_sr  <= {pay_sr[158:0], dec_bit};
                        if (bit_cnt < 8'd144)
                            crc_reg <= crc16_step(crc_reg, dec_bit);
                        if (bit_cnt == 8'd159) begin
                            logic [159:0] full_pay;
                            full_pay = {pay_sr[158:0], dec_bit};
                            if (crc_reg == full_pay[15:0]) begin
                                nfc_rx_frames <= nfc_rx_frames + 16'd1;
                                ack_sr        <= {8'h5A, full_pay[31:16], (8'hA5 ^ full_pay[23:16])};
                                bit_cnt       <= 8'd0;
                                half_idx      <= 1'b0;
                                nst           <= N_TX_ACK;
                            end else begin
                                nfc_crc_err <= 1'b1;
                                nst         <= N_IDLE;
                            end
                        end else begin
                            bit_cnt <= bit_cnt + 8'd1;
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

    wire pay_accept = (nst == N_PAY) && hb_mid_ev && half_idx &&
                      (h0_sample != hb_val_c) && (bit_cnt == 8'd159) &&
                      (crc_reg == {pay_sr[14:0], h0_sample});
    wire [159:0] pay_final = {pay_sr[158:0], h0_sample};

    always_ff @(posedge clk or negedge srst_n) begin
        if (!srst_n) begin
            token_valid        <= 1'b0;
            token_nonce        <= '0;
            token_digest_bind  <= '0;
            token_quorum_flags <= '0;
        end else if (token_consume) begin
            token_valid        <= 1'b0;
            token_nonce        <= '0;
            token_digest_bind  <= '0;
            token_quorum_flags <= '0;
        end else if (pay_accept) begin
            token_valid        <= 1'b1;
            token_nonce        <= pay_final[159:96];
            token_digest_bind  <= pay_final[95:32];
            token_quorum_flags <= pay_final[31:16];
        end
    end

    // ------------------------------------------------------------ 32-bit Phase-Continuous RF NCO
    logic [31:0] phase_acc;
    logic [31:0] chirp_ftw;
    logic [95:0] fsk_sr;
    logic [6:0]  fsk_bits;
    logic [15:0] sym_cnt;

    wire [15:0] sym_lim = (16'd8 << nco_sym_shift[2:0]) - 16'd1;
    assign nco_tx_active = (fsk_bits != 7'd0);

    logic [31:0] ftw_eff;
    always_comb begin
        unique case (nco_mode)
            2'd1:    ftw_eff = nco_tx_active
                               ? (fsk_sr[95] ? (nco_ftw_base + nco_ftw_delta) : (nco_ftw_base - nco_ftw_delta))
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
                fsk_sr    <= {32'hAAAA_D391, nco_pkt_data};
                fsk_bits  <= 7'd96;
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
                        fsk_sr   <= {fsk_sr[94:0], 1'b0};
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
