// Dregg-180 Organ 3: Contactless 13.56 MHz HF-NFC Air-Gap Port + 32-Bit Phase-Continuous NCO.
//
// All pins sit on ESD-protected, Liberty-characterized gf180mcu_fd_io__bi_24t digital pads
// (zero digital wiring onto unbuffered analog[3:0]):
//   * 13.56 MHz HF-NFC Carrier Recovery & Subcarrier Generator:
//       - Tracks rising edges of the Schmitt-triggered 13.56 MHz carrier input (`nfc_clk_in`),
//         generating exact /16 = 847.5 kHz ISO/IEC 14443 subcarrier and /128 = 105.9375 kbps
//         Manchester bit timing without adding an extra clock tree to CTS.
//       - Decodes Manchester ASK frames (`0xA5` SOF sync byte + 64b approval_nonce +
//         64b req_digest_bind + 16b quorum_flags + 16b ISO-14443A CRC-A, init 0x6363,
//         poly x^16 + x^12 + x^5 + 1), rejecting any Manchester coding violation or CRC mismatch.
//       - Replies with a 32-bit Manchester load-modulation ACK frame on the 847.5 kHz subcarrier
//         (`nfc_load_mod` bi_24t output) when a valid co-approval token is latched.
//   * 32-Bit Phase-Continuous Direct-RF NCO (`nco_rf_out`):
//       - Phase accumulator `phase_acc <= phase_acc + ftw_eff` with sub-Hz frequency resolution.
//       - Supports CW (0), phase-continuous 2-FSK packet beacon (1), and linear FM chirp (2).
`default_nettype none

module dregg_nfc_nco (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         srst_n,
    // Physical bi_24t pad signals
    input  wire         nfc_clk_in,        // 13.56 MHz carrier (Schmitt bi_24t)
    input  wire         nfc_ask_in,        // Manchester ASK envelope input (bi_24t)
    output wire         nfc_load_mod,      // 847.5 kHz resistive load-modulation TX (bi_24t)
    output wire         nco_rf_out,        // 32-bit phase-continuous RF output (bi_24t)
    // Co-approval token interface to CapTP Vat
    input  wire         token_consume,     // clears token after single-use co-approval
    output logic        token_valid,
    output logic [63:0] token_nonce,
    output logic [63:0] token_digest_bind,
    output logic [15:0] token_quorum_flags,
    output logic [15:0] nfc_rx_frames,
    output logic        nfc_crc_err,
    // NCO configuration & packetizer interface
    input  wire         nco_en,
    input  wire  [1:0]  nco_mode,          // 0: CW, 1: 2-FSK beacon, 2: linear chirp
    input  wire  [3:0]  nco_sym_shift,     // symbol period = 2^(nco_sym_shift + 3) core clocks
    input  wire  [31:0] nco_ftw_base,
    input  wire  [31:0] nco_ftw_delta,
    input  wire         nco_pkt_load,
    input  wire  [63:0] nco_pkt_data,
    output wire         nco_tx_active
);
    // ------------------------------------------------------------ 13.56 MHz carrier & ASK sync
    wire nfc_c_s, nfc_a_s;
    qsag_sync2 #(.RV(1'b0)) u_sc (.clk(clk), .rst_n(rst_n), .d(nfc_clk_in), .q(nfc_c_s));
    qsag_sync2 #(.RV(1'b1)) u_sa (.clk(clk), .rst_n(rst_n), .d(nfc_ask_in), .q(nfc_a_s));

    logic       nfc_c_q;
    wire        carrier_tick = nfc_c_s & ~nfc_c_q;
    logic [6:0] cdiv;          // cdiv[3] = /16 (847.5 kHz), cdiv[5:0] = 64-carrier half-bit window
    wire        subcarrier_847k = cdiv[3];

    // ISO/IEC 14443A CRC-A step (reflected 0x8408 / MSB-first 0x1021; we shift MSB-first with 0x1021)
    function automatic logic [15:0] crc16_step(input logic [15:0] c, input logic bit_in);
        logic fb;
        begin
            fb         = c[15] ^ bit_in;
            crc16_step = {c[14:0], 1'b0} ^ (fb ? 16'h1021 : 16'h0000);
        end
    endfunction

    // Manchester RX state machine:
    //   Wait for idle high (`nfc_a_s == 1`), then falling start edge (`1 -> 0`) aligns cdiv = 0.
    //   Each bit = 2 half-bits of 64 carrier cycles (total 128 carrier cycles = 105.9375 kbps;
    //   also supports fast-sim x8 mode when nco_sym_shift[3] is set: 8 carrier cycles per half-bit!).
    wire  [5:0] half_mid = nco_sym_shift[3] ? 6'd3 : 6'd31;
    wire  [5:0] half_end = nco_sym_shift[3] ? 6'd7 : 6'd63;

    localparam logic [2:0] N_IDLE = 3'd0, N_SYNC = 3'd1, N_PAY = 3'd2, N_TX_ACK = 3'd3;
    logic [2:0]   nst;
    logic          ask_prev;
    logic         half_idx;
    logic         h0_sample;
    logic [7:0]   bit_cnt;
    logic [7:0]   sync_sr;
    logic [159:0] pay_sr;
    logic [15:0]  crc_reg;
    logic [31:0]  ack_sr;

    wire tx_manchester_env = ack_sr[31] ? ~half_idx : half_idx;
    assign nfc_load_mod    = (nst == N_TX_ACK) && tx_manchester_env && subcarrier_847k;

    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            nfc_c_q        <= 1'b0;
            cdiv           <= '0;
            nst            <= N_IDLE;
            ask_prev       <= 1'b1;
            half_idx       <= 1'b0;
            h0_sample      <= 1'b0;
            bit_cnt        <= '0;
            sync_sr        <= '0;
            pay_sr         <= '0;
            crc_reg        <= 16'h6363;
            ack_sr         <= '0;
            nfc_rx_frames  <= '0;
            nfc_crc_err    <= 1'b0;
        end else begin
            nfc_c_q <= nfc_c_s;
            if (carrier_tick) begin
                ask_prev <= nfc_a_s;
                cdiv     <= (cdiv == {1'b0, half_end}) ? 7'd0 : (cdiv + 7'd1);

                unique case (nst)
                    N_IDLE: begin
                        // Detect falling edge from idle high -> start of SOF sync byte 0xA5 (MSB=1: 1->0 mid-bit,
                        // preceded by a start bit 0: 0->1!)
                        if (ask_prev && !nfc_a_s) begin
                            cdiv     <= 7'd1;
                            half_idx <= 1'b0;
                            bit_cnt  <= 8'd0;
                            sync_sr  <= 8'd0;
                            nst      <= N_SYNC;
                        end
                    end
                    N_SYNC: begin
                        if (cdiv[5:0] == half_mid) begin
                            if (!half_idx) begin
                                h0_sample <= nfc_a_s;
                            end else begin
                                if (h0_sample == nfc_a_s) begin
                                    nst <= N_IDLE; // Manchester violation
                                end else begin
                                    // start bit 0 (0->1: h0=0,h1=1) then 8-bit 0xA5 sync byte = 9 bits (0..8)
                                    logic dec_bit;
                                    dec_bit = h0_sample; // 1->0 => 1, 0->1 => 0
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
                        end
                        if (cdiv[5:0] == half_end) half_idx <= ~half_idx;
                    end
                    N_PAY: begin
                        if (cdiv[5:0] == half_mid) begin
                            if (!half_idx) begin
                                h0_sample <= nfc_a_s;
                            end else begin
                                if (h0_sample == nfc_a_s) begin
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
                        end
                        if (cdiv[5:0] == half_end) half_idx <= ~half_idx;
                    end
                    N_TX_ACK: begin
                        if (cdiv[5:0] == half_end) begin
                            half_idx <= ~half_idx;
                            if (half_idx) begin
                                ack_sr <= {ack_sr[30:0], 1'b0};
                                if (bit_cnt == 8'd31) nst <= N_IDLE;
                                else                  bit_cnt <= bit_cnt + 8'd1;
                            end
                        end
                    end
                    default: nst <= N_IDLE;
                endcase
            end
        end
    end

    // Secret-cleared co-approval token registers (wiped on tamper / zeroize or single-use consume!)
    wire pay_accept = carrier_tick && (nst == N_PAY) && (cdiv[5:0] == half_mid) && half_idx &&
                      (h0_sample != nfc_a_s) && (bit_cnt == 8'd159) &&
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
    logic [95:0] fsk_sr;       // 32b preamble+sync (0xAAAA_D391) + 64b payload
    logic [6:0]  fsk_bits;
    logic [15:0] sym_cnt;

    wire [15:0] sym_lim = (16'd8 << nco_sym_shift[2:0]) - 16'd1;
    assign nco_tx_active = (fsk_bits != 7'd0);

    logic [31:0] ftw_eff;
    always_comb begin
        unique case (nco_mode)
            2'd1: begin
                if (nco_tx_active)
                    ftw_eff = fsk_sr[95] ? (nco_ftw_base + nco_ftw_delta) : (nco_ftw_base - nco_ftw_delta);
                else
                    ftw_eff = nco_ftw_base;
            end
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
