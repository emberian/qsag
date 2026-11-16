// Dregg-180 (QSAG-NI-180) unified 2,112-bit (33 x 64b) zeroizable `latrnq_1` sponge & scratchpad.
//
//   * st[0..24]  25 x 64-bit unified sponge state:
//                  - Keccak-f[1600] lanes 0..24
//                  - Poseidon2 width-12 state directly inside lanes 0..11
//                  - Verifier registers CH/A/B in lanes 12..23
//   * sh[0..7]   8 x 64-bit scratchpad / CapTP SpongeMacaroon staging (addresses 32..39)
//   * Tier-B2 / Tier-A1 Silicon Hardening:
//       - Under `QSAG_LATCH_RF`, all 33 rows use `gf180mcu_fd_sc_mcu7t5v0__latrnq_1` + `icgtp_1`
//         sharing ONE posedge-captured 64-bit write-data hold register (`u_wd_hold`).
//       - Asynchronous `.RN` (`srst_n`) is driven EXCLUSIVELY by flop-registered `secret_rst_n`
//         (0-clock tamper/laser zeroization even if `clk` is stopped, ZERO combinational HD=4
//         decode glitches on `.RN`!), while command-level `wipe` clears all 33 rows synchronously
//         in 1 clock through `u_wd_hold` + `icgtp_1`!
`default_nettype none

module qsag_sponge (
    input  wire         clk,
    input  wire         srst_n,     // flop-registered glitch-free async clear -> RN
    input  wire         wipe,       // synchronous 1-clock clear of all 33 rows
    input  wire         wr_en,
    input  wire  [5:0]  wr_addr,    // 0..24 sponge lanes, 32..39 shadow lanes
    input  wire  [63:0] wr_data,
    input  wire  [5:0]  rd_addr,
    output logic [63:0] rd_data
);
    wire [63:0] st [25];
    wire [63:0] sh [8];

    genvar i;
`ifdef QSAG_LATCH_RF
    wire        any_we = wipe | wr_en;
    wire [63:0] wd_hold_q;
    qsag_ereg_nr #(.W(64)) u_wd_hold (
        .clk(clk), .en(any_we), .d(wipe ? 64'd0 : wr_data), .q(wd_hold_q)
    );
    generate
        for (i = 0; i < 25; i++) begin : g_lane
            wire we = wipe || (wr_en && (wr_addr == 6'(i)));
            wire gate;
            qsag_clkgate_1 u_cg (.clk(clk), .en(we), .gclk(gate));
            qsag_latch_word_rst #(.W(64)) u_lat (.gate(gate), .rst_n(srst_n), .d(wd_hold_q), .q(st[i]));
        end
        for (i = 0; i < 8; i++) begin : g_shadow
            wire we = wipe || (wr_en && (wr_addr == (6'd32 + 6'(i))));
            wire gate;
            qsag_clkgate_1 u_cg (.clk(clk), .en(we), .gclk(gate));
            qsag_latch_word_rst #(.W(64)) u_lat (.gate(gate), .rst_n(srst_n), .d(wd_hold_q), .q(sh[i]));
        end
    endgenerate
`else
    generate
        for (i = 0; i < 25; i++) begin : g_lane
            wire we = wipe || (wr_en && (wr_addr == 6'(i)));
            qsag_ereg #(.W(64)) u_r (.clk(clk), .rst_n(srst_n), .en(we), .d(wipe ? 64'd0 : wr_data), .q(st[i]));
        end
        for (i = 0; i < 8; i++) begin : g_shadow
            wire we = wipe || (wr_en && (wr_addr == (6'd32 + 6'(i))));
            qsag_ereg #(.W(64)) u_s (.clk(clk), .rst_n(srst_n), .en(we), .d(wipe ? 64'd0 : wr_data), .q(sh[i]));
        end
    endgenerate
`endif

    always_comb begin
        rd_data = '0;
        if (rd_addr[5]) begin
            rd_data = sh[rd_addr[2:0]];
        end else begin
            for (int l = 0; l < 25; l++)
                if (rd_addr[4:0] == 5'(l)) rd_data = st[l];
        end
    end
endmodule
`default_nettype wire
