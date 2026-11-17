// Area proxy: the existing NFC receiver with the NCO inputs tied off and its outputs unused, so that
// synthesis removes the NCO (phase accumulator, FSK shift register, chirp adder).
`default_nettype none
module px_nfc (
    input  wire clk, rst_n, arst_n, srst_n, nfc_clk_in, nfc_ask_in, token_consume,
    output wire nfc_load_mod, token_valid,
    output wire [63:0] token_nonce, token_digest_bind,
    output wire [15:0] token_quorum_flags, nfc_rx_frames,
    output wire nfc_crc_err
);
    dregg_nfc_nco u (
        .clk, .rst_n, .arst_n, .srst_n, .nfc_clk_in, .nfc_ask_in, .nfc_load_mod, .nco_rf_out(),
        .token_consume, .token_valid, .token_nonce, .token_digest_bind, .token_quorum_flags, .nfc_rx_frames,
        .nfc_crc_err, .nco_en(1'b0), .nco_mode(2'd0), .nco_sym_shift(4'd0), .nco_ftw_base(32'd0),
        .nco_ftw_delta(32'd0), .nco_pkt_load(1'b0), .nco_pkt_data(64'd0), .nco_tx_active()
    );
endmodule
`default_nettype wire
