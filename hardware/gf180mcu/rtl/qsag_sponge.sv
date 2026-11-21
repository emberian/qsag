// Dregg-180 (QSAG-NI-180) unified enclave register file: sponge state, Fp5/Ext4 verifier registers,
// scratchpad, ZK statement/program pin, SLH-DSA keys, and CapTP Vat root key in one zeroizable bank.
//
// Address map (56 rows x 64 bits = 3,584 bits):
//   rows  0..31  st      Keccak-f[1600] (0..24 + D[0..4] in 25..29 + B[0..1] in 30..31),
//                        Poseidon2-12 (0..11), verifier regs T0/CH/A/B (Ext4: 0..3, 12..23;
//                        Fp5: 0..4, 12..26)            `latq_1`, wiped in 1 clock on `wipe`
//   rows 32..41  sh      scratchpad / X, Y (32..41)    `latq_1`, wiped in 1 clock on `wipe`
//   rows 44..47  zk_pin  verified (prog_digest, root)  `latrnq_1`, 0-clock clear on `srst_n`
//   rows 48..53  key     SK.seed, SK.prf, K_MAC        `latrnq_1`, 0-clock clear on `srst_n`
//   rows 54..57  kvat    CapTP Vat root key K_vat      `latrnq_1`, 0-clock clear on `srst_n`
//
// Single shared 64-bit write-hold register (`u_hold`) feeds all 56 latch rows AND external
// latch consumers (`dregg_captp_vat`, `dregg_nfc_nco`), eliminating duplicate 64-bit hold FFs.
`default_nettype none

module qsag_sponge (
    input  wire          clk,
    input  wire          srst_n,           // pure FF-registered secret clear -> RN (0-clock zeroize)
    input  wire          wipe,             // synchronous 1-clock clear of public/scratch st & sh rows
    // scalar read/write port (wire engine, field engine, Keccak)
    input  wire          wr_en,
    input  wire  [5:0]   wr_addr,          // 0..31 st, 32..41 sh
    input  wire  [63:0]  wr_data,
    input  wire  [5:0]   rd_addr,          // 0..31 st, 32..41 sh, 44..47 zk_pin, 48..53 key, 54..57 kvat
    output logic [63:0]  rd_data,
    // aux write port (mutually exclusive with wr_en except when writing identical in_data in S_VLD)
    input  wire          aux_we,
    input  wire  [4:0]   aux_addr,         // 0..9 sh, 10..13 zk_pin, 14..19 key, 20..23 kvat
    input  wire  [63:0]  aux_wdata,
    input  wire          ext_hold_en,      // latch aux_wdata into hold_q for external latch banks
    output wire  [63:0]  hold_q,
    output wire  [127:0] kmac_q            // {key[5], key[4]} direct feed to GF(2^128) unit
);
    localparam int N_ST  = 32;
    localparam int N_AUX = 24;             // 10 sh + 4 zk_pin + 6 key + 4 kvat

    wire [63:0] st [N_ST];
    wire [63:0] ax [N_AUX];

    wire        sc_sh   = wr_en && (wr_addr >= 6'd32) && (wr_addr <= 6'd41);
    wire        sc_st   = wr_en && (wr_addr < 6'd32);
    wire        use_aux = aux_we | ext_hold_en;
    wire [63:0] hold_d  = wipe ? 64'd0 : (use_aux ? aux_wdata : wr_data);

    logic [N_ST-1:0]  st_we;
    logic [N_AUX-1:0] ax_we;
    always_comb begin
        for (int i = 0; i < N_ST; i++)
            st_we[i] = wipe || (sc_st && (wr_addr == 6'(i)));
        for (int i = 0; i < 10; i++)
            ax_we[i] = wipe || (aux_we && (aux_addr == 5'(i))) || (sc_sh && (wr_addr == 6'(32 + i)));
        for (int i = 10; i < N_AUX; i++)
            ax_we[i] = aux_we && (aux_addr == 5'(i));
    end

    wire [6:0] rn_br;
    qsag_rst_tree #(.N(7)) u_rntree (.a(srst_n), .y(rn_br));

    genvar i;
`ifdef QSAG_LATCH_RF
    wire hold_ld = wipe | sc_st | sc_sh | use_aux;
    qsag_ereg_nr #(.W(64)) u_hold (.clk(clk), .en(hold_ld), .d(hold_d), .q(hold_q));
    generate
        for (i = 0; i < N_ST; i++) begin : g_lane
            wire gate;
            qsag_latgate u_cg (.clk(clk), .en(st_we[i]), .gclk(gate));
            qsag_latch_word #(.W(64)) u_lat (.gate(gate), .d(hold_q), .q(st[i]));
        end
        for (i = 0; i < 10; i++) begin : g_sh
            wire gate;
            qsag_latgate u_cg (.clk(clk), .en(ax_we[i]), .gclk(gate));
            qsag_latch_word #(.W(64)) u_lat (.gate(gate), .d(hold_q), .q(ax[i]));
        end
        for (i = 10; i < N_AUX; i++) begin : g_sec
            wire gate;
            qsag_latgate u_cg (.clk(clk), .en(ax_we[i]), .gclk(gate));
            qsag_latch_word_rst #(.W(64)) u_lat (.gate(gate), .rst_n(rn_br[(i - 10) / 2]), .d(hold_q), .q(ax[i]));
        end
    endgenerate
`else
    qsag_ereg_nr #(.W(64)) u_hold (.clk(clk), .en(ext_hold_en), .d(aux_wdata), .q(hold_q));
    generate
        for (i = 0; i < N_ST; i++) begin : g_lane
            qsag_ereg_nr #(.W(64)) u_r (.clk(clk), .en(st_we[i]), .d(hold_d), .q(st[i]));
        end
        for (i = 0; i < 10; i++) begin : g_sh
            qsag_ereg_nr #(.W(64)) u_r (.clk(clk), .en(ax_we[i]), .d(hold_d), .q(ax[i]));
        end
        for (i = 10; i < N_AUX; i++) begin : g_sec
            qsag_ereg #(.W(64)) u_r (.clk(clk), .rst_n(rn_br[(i - 10) / 2]), .en(ax_we[i]), .d(aux_wdata), .q(ax[i]));
        end
    endgenerate
`endif

    assign kmac_q = {ax[19], ax[18]};

    // Shared 56-line one-hot decoder + AOI22/NAND/NOR OR-bus
    logic [N_ST-1:0]  rs_st;
    logic [N_AUX-1:0] rs_ax;
    always_comb begin
        for (int k = 0; k < N_ST; k++)
            rs_st[k] = (rd_addr == 6'(k));
        for (int k = 0; k < 10; k++)
            rs_ax[k] = (rd_addr == 6'(32 + k));
        for (int k = 10; k < N_AUX; k++)
            rs_ax[k] = (rd_addr == 6'(44 + k - 10));

        rd_data = 64'd0;
        for (int k = 0; k < N_ST; k++)
            rd_data = rd_data | ({64{rs_st[k]}} & st[k]);
        for (int k = 0; k < N_AUX; k++)
            rd_data = rd_data | ({64{rs_ax[k]}} & ax[k]);
    end

`ifndef SYNTHESIS
    always_ff @(posedge clk)
        if (srst_n && !wipe && aux_we && (sc_st || sc_sh) && (aux_wdata != wr_data))
            $error("qsag_sponge: concurrent aux and scalar writes with different data");
`endif
endmodule
`default_nettype wire
