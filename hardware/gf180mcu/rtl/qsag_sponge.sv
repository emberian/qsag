// QSAG-NI-180 shared 1,600-bit sponge / register file.
//
// 25 lanes of 64 bits. They hold secrets during enclave operations and are cleared together in
// one clock by `wipe` (all write enables, zero data), which costs no per-bit reset:
//   * Keccak-f[1600] state a[x + 5y] = lane x + 5y, permuted in place by qsag_keccak_serial;
//   * Poseidon2 width-12 state in lanes 0..11 and the field registers CH/A/B in lanes 12..23
//     when the field engine owns them.
// One 64-bit read port and one 64-bit write port serve every user. The 8 x 64-bit shadow buffer
// (addresses 32..39) is part of the same address space: it holds the request parameters of the
// enclave operations and the X/Y operand registers of the verifier.
`default_nettype none

module qsag_sponge (
    input  wire         clk,
    input  wire         wipe,      // synchronous clear of lanes and shadow words
    input  wire         wr_en,
    input  wire [5:0]   wr_addr,   // 0..24 lanes, 32..39 shadow
    input  wire [63:0]  wr_data,
    input  wire [5:0]   rd_addr,
    output logic [63:0] rd_data
);
    wire [63:0] st [25];
    wire [63:0] sh [8];
    wire [63:0] wdz = wipe ? 64'd0 : wr_data;

`ifdef QSAG_LATCH_RF
    // Capture the entire write transaction on the rising edge. Latches open in
    // the following low half-cycle, when both data and decoder are stable.
    // This breaks the read/ALU/write transparent loop. No asynchronous wipe claim:
    // clearing this memory requires a running core clock, as for the DFF bank.
    logic [63:0] wd_q;
    logic [5:0] wa_q;
    logic we_q, wipe_q;
    always_ff @(posedge clk) begin
        wd_q <= wdz;
        wa_q <= wr_addr;
        we_q <= wr_en;
        wipe_q <= wipe;
    end
    wire nclk;
    qsag_clkinv u_inv (.a(clk), .y(nclk));
    for (genvar i = 0; i < 33; i++) begin : g_bank
        localparam logic [5:0] ADDR = (i < 25) ? 6'(i) : 6'(i + 7);
        wire gate;
        qsag_clkgate u_cg (.clk(nclk), .en(wipe_q || (we_q && wa_q == ADDR)), .gclk(gate));
        if (i < 25) begin : g_st
            qsag_latch_word u_l (.gate(gate), .d(wd_q), .q(st[i]));
        end else begin : g_sh
            qsag_latch_word u_l (.gate(gate), .d(wd_q), .q(sh[i-25]));
        end
    end
`else
    genvar i;
    generate
        for (i = 0; i < 25; i++) begin : g_lane
            wire we = wr_en && (wr_addr == 6'(i));
            qsag_ereg_nr #(.W(64)) u_r (.clk(clk), .en(we | wipe), .d(wdz), .q(st[i]));
        end
        for (i = 0; i < 8; i++) begin : g_shadow
            wire we = wr_en && (wr_addr == 6'(32 + i));
            qsag_ereg_nr #(.W(64)) u_r (.clk(clk), .en(we | wipe), .d(wdz), .q(sh[i]));
        end
    endgenerate

`endif

    always_comb begin
        rd_data = '0;
        if (rd_addr[5]) rd_data = sh[rd_addr[2:0]];
        else begin
            for (int l = 0; l < 25; l++) if (rd_addr[4:0] == 5'(l)) rd_data = st[l];
        end
    end
endmodule
`default_nettype wire
