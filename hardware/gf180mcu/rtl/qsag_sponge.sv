// Dregg-180 (QSAG-NI-180) sponge state and scratchpad register file.
//
//   st[0..24]  25 x 64-bit state: Keccak-f[1600] lanes, Poseidon2 width-12 state in lanes 0..11,
//              verifier registers CH/A/B in lanes 12..23.
//   sh[0..7]   8 x 64-bit scratchpad / SpongeMacaroon staging (addresses 32..39). Under
//              QSAG_LATCH_RF these are latrnq_1 rows behind one write-data hold register.
//
// Reset discipline (R1 B2): the asynchronous clear pin (RN) of the latch rows is driven by
// `srst_n` alone, which is a reset/tamper/fault signal built from flop outputs. The command-level
// `wipe` is a decode of the engine's state register and therefore never reaches RN: it clears
// every row synchronously, through the write path, in one clock.
`default_nettype none

module qsag_sponge (
    input  wire         clk,
    input  wire         srst_n,     // registered secret clear -> RN (asynchronous)
    input  wire         wipe,       // synchronous clear of all rows
    // scalar read/write port (wire engine, field engine, word-serial Keccak)
    input  wire         wr_en,
    input  wire  [5:0]  wr_addr,    // 0..24 lanes, 32..39 scratchpad
    input  wire  [63:0] wr_data,
    input  wire  [5:0]  rd_addr,
    output logic [63:0] rd_data,
    // second write port into the scratchpad (used while Keccak owns the scalar port)
    input  wire         sh_ext_we,
    input  wire  [2:0]  sh_ext_addr,
    input  wire  [63:0] sh_ext_wdata,
    // st[i] <- st[i] ^ sh[i] for every set bit i (one clock)
    input  wire  [7:0]  blk_absorb_mask
);
    wire [63:0] st [25];
    wire [63:0] sh [8];

    genvar i;
    generate
        for (i = 0; i < 25; i++) begin : g_lane
            wire sc_we = wr_en && (wr_addr == 6'(i));
            wire ab_w;
            wire [63:0] ab_d;
            if (i < 8) begin : g_ab
                assign ab_w = blk_absorb_mask[i];
                assign ab_d = st[i] ^ sh[i];
            end else begin : g_noab
                assign ab_w = 1'b0;
                assign ab_d = 64'd0;
            end
            wire        we = wipe | ab_w | sc_we;
            wire [63:0] wd = wipe ? 64'd0 : (ab_w ? ab_d : wr_data);
            qsag_ereg_nr #(.W(64)) u_r (.clk(clk), .en(we), .d(wd), .q(st[i]));
        end
    endgenerate

    wire        sh_sc_sel = wr_en && (wr_addr[5:3] == 3'b100);
    wire        sh_any_we = sh_ext_we | sh_sc_sel;
    wire [2:0]  sh_waddr  = sh_ext_we ? sh_ext_addr  : wr_addr[2:0];
    wire [63:0] sh_wdata  = wipe ? 64'd0 : (sh_ext_we ? sh_ext_wdata : wr_data);
`ifdef QSAG_LATCH_RF
    wire [63:0] wd_sh_q;
    qsag_ereg_nr #(.W(64)) u_wd_hold (.clk(clk), .en(wipe | sh_any_we), .d(sh_wdata), .q(wd_sh_q));
    generate
        for (i = 0; i < 8; i++) begin : g_shadow
            wire sh_we = wipe || (sh_any_we && (sh_waddr == 3'(i)));
            wire gate;
            qsag_latgate u_cg (.clk(clk), .en(sh_we), .gclk(gate));
            qsag_latch_word_rst #(.W(64)) u_lat (.gate(gate), .rst_n(srst_n), .d(wd_sh_q), .q(sh[i]));
        end
    endgenerate
`else
    generate
        for (i = 0; i < 8; i++) begin : g_shadow
            wire sh_we = wipe || (sh_any_we && (sh_waddr == 3'(i)));
            qsag_ereg #(.W(64)) u_s (.clk(clk), .rst_n(srst_n), .en(sh_we), .d(sh_wdata), .q(sh[i]));
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
