// Dregg-180 (QSAG-NI-180) enclave register file: sponge state, scratchpad and key rows in one
// zeroizable bank (R1 A1).
//
//   rows  0..24  st   Keccak-f[1600] lanes; Poseidon2 width-12 state in lanes 0..11; verifier
//                     registers CH/A/B in lanes 12..23                    scalar port (read/write)
//   rows 32..39  sh   scratchpad / SpongeMacaroon staging                 scalar port + aux write
//   key[0..5]         SK.seed, SK.prf, mask key (PK.seed)                 aux write, direct outputs
//   kvat[0..3]        vat root key                                        aux write, direct outputs
//
// Under QSAG_LATCH_RF every row is 64 latrnq_1 cells behind one icgtp_1, fed by one of two
// posedge write-data hold registers:
//   main hold  rows st, from the scalar write port
//   aux hold   rows sh / key / kvat, from the aux write port or, for sh, from the scalar write port
// Two holds exist because the scratchpad is filled from the input stream while Keccak owns the
// scalar port. The aux port wins when both address the aux hold in the same clock; the engine
// only does that with identical data (PUF enrolment copies one word to sh and to a key row).
//
// Reset discipline (R1 B2): the asynchronous clear pin RN of every latch, and of the two hold
// registers, is `srst_n` alone: a reset / tamper / fault signal built from flop outputs. It works
// with the clock stopped. The command-level `wipe` is a decode of the engine state and never
// reaches RN: it clears the st and sh rows synchronously through the write path in one clock.
// Key rows are not touched by `wipe`.
//
// Without QSAG_LATCH_RF the rows are enable flops with the same clock-by-clock behaviour.
`default_nettype none

module qsag_sponge (
    input  wire          clk,
    input  wire          srst_n,     // registered secret clear -> RN (asynchronous)
    input  wire          wipe,       // synchronous clear of the st and sh rows
    // scalar read/write port (wire engine, field engine, Keccak)
    input  wire          wr_en,
    input  wire  [5:0]   wr_addr,    // 0..24 st, 32..39 sh
    input  wire  [63:0]  wr_data,
    input  wire  [5:0]   rd_addr,
    output logic [63:0]  rd_data,
    // aux write port
    input  wire          aux_we,
    input  wire  [4:0]   aux_addr,   // 0..7 sh, 8..13 key[0..5], 14..17 kvat[0..3]
    input  wire  [63:0]  aux_wdata,
    output wire  [383:0] key_q,      // key[i] = key_q[64*i +: 64]
    output wire  [255:0] kvat_q
);
    localparam int N_AUX = 18;

    wire [63:0] st [25];
    wire [63:0] sh [8];

    wire        sc_sh  = wr_en && (wr_addr[5:3] == 3'b100);   // scalar write into the scratchpad
    wire        aux_ld = aux_we | sc_sh | wipe;
    wire [63:0] aux_d  = wipe ? 64'd0 : (aux_we ? aux_wdata : wr_data);
    wire        st_ld  = wr_en | wipe;
    wire [63:0] st_d   = wipe ? 64'd0 : wr_data;

    // row write strobes
    logic [24:0]      st_we;
    logic [N_AUX-1:0] ax_we;
    always_comb begin
        for (int i = 0; i < 25; i++) st_we[i] = wipe || (wr_en && (wr_addr == 6'(i)));
        for (int i = 0; i < N_AUX; i++) ax_we[i] = aux_we && (aux_addr == 5'(i));
        for (int i = 0; i < 8; i++)
            ax_we[i] = wipe || (aux_we && (aux_addr == 5'(i))) || (sc_sh && (wr_addr[2:0] == 3'(i)));
    end

    wire [64*N_AUX-1:0] ax_q;
    genvar i;
`ifdef QSAG_LATCH_RF
    wire [63:0] st_hold_q, ax_hold_q;
    qsag_ereg #(.W(64)) u_st_hold (.clk(clk), .rst_n(srst_n), .en(st_ld),  .d(st_d),  .q(st_hold_q));
    qsag_ereg #(.W(64)) u_ax_hold (.clk(clk), .rst_n(srst_n), .en(aux_ld), .d(aux_d), .q(ax_hold_q));
    generate
        for (i = 0; i < 25; i++) begin : g_lane
            wire gate;
            qsag_latgate u_cg (.clk(clk), .en(st_we[i]), .gclk(gate));
            qsag_latch_word_rst #(.W(64)) u_lat (.gate(gate), .rst_n(srst_n), .d(st_hold_q), .q(st[i]));
        end
        for (i = 0; i < N_AUX; i++) begin : g_aux
            wire gate;
            qsag_latgate u_cg (.clk(clk), .en(ax_we[i]), .gclk(gate));
            qsag_latch_word_rst #(.W(64)) u_lat (.gate(gate), .rst_n(srst_n), .d(ax_hold_q), .q(ax_q[64*i +: 64]));
        end
    endgenerate
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_ld = &{1'b0, st_ld, aux_ld};
    /* verilator lint_on UNUSEDSIGNAL */
`else
    generate
        for (i = 0; i < 25; i++) begin : g_lane
            qsag_ereg #(.W(64)) u_r (.clk(clk), .rst_n(srst_n), .en(st_we[i]), .d(st_d), .q(st[i]));
        end
        for (i = 0; i < N_AUX; i++) begin : g_aux
            qsag_ereg #(.W(64)) u_r (.clk(clk), .rst_n(srst_n), .en(ax_we[i]), .d(aux_d), .q(ax_q[64*i +: 64]));
        end
    endgenerate
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused_ld = &{1'b0, st_ld, aux_ld};
    /* verilator lint_on UNUSEDSIGNAL */
`endif
    generate
        for (i = 0; i < 8; i++) begin : g_sh
            assign sh[i] = ax_q[64*i +: 64];
        end
    endgenerate
    assign key_q  = ax_q[64*8  +: 384];
    assign kvat_q = ax_q[64*14 +: 256];

    always_comb begin
        rd_data = '0;
        if (rd_addr[5]) begin
            rd_data = sh[rd_addr[2:0]];
        end else begin
            for (int l = 0; l < 25; l++)
                if (rd_addr[4:0] == 5'(l)) rd_data = st[l];
        end
    end

`ifndef SYNTHESIS
    // The aux hold carries one word per clock: a scalar scratchpad write that coincides with an
    // aux write must carry the same data (see the header).
    always_ff @(posedge clk)
        if (srst_n && !wipe && aux_we && sc_sh && (aux_wdata != wr_data))
            $error("qsag_sponge: aux and scalar scratchpad writes with different data in one clock");
`endif
endmodule
`default_nettype wire
