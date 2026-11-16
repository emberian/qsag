// Dregg-180 (QSAG-NI-180) unified 1,600-bit sponge state + clock-gated latq_1 scratchpad.
//
//   * st[0..24]  25 x 64-bit unified sponge state:
//                  - Keccak-f[1600] lanes 0..24 (5-clock-per-round in-place parallel port)
//                  - Poseidon2 width-12 state in lanes 0..11 (parallel fast port, zero duplicate FFs!)
//                  - Verifier registers CH/A/B in lanes 12..23
//   * sh[0..7]   8 x 64-bit clock-gated transparent-latch register file (addresses 32..39),
//                using one shared posedge-captured write-data hold register + icgtp_2 high-phase
//                clock gates driving gf180mcu_fd_sc_mcu7t5v0__latq_1 cells.
//   * GOTCHA #4 1-Clock Shadow Block Absorb (`blk_absorb_xor`):
//                While Keccak or Poseidon2 permutes `st[0..24]`, incoming words stream concurrently
//                into `sh[0..7]` with zero port contention, and `blk_absorb_xor` XORs up to 8 words
//                (`blk_absorb_mask[7:0]`) from `sh[0..7]` into `st[0..7]` in ONE single clock!
`default_nettype none

module qsag_sponge (
    input  wire              clk,
    input  wire              wipe,
    // scalar read/write port
    input  wire              wr_en,
    input  wire  [5:0]       wr_addr,         // 0..24 lanes, 32..39 shadow latches
    input  wire  [63:0]      wr_data,
    input  wire  [5:0]       rd_addr,
    output logic [63:0]      rd_data,
    // 1-clock 64-byte shadow-to-sponge parallel block absorb
    input  wire  [7:0]       blk_absorb_mask, // bit i=1: st[i] <= st[i] ^ sh[i] in 1 clock!
    // parallel state view & fast engine ports (lanes 0..24 and 0..11)
    output wire  [25*64-1:0] st_flat_o,
    input  wire  [24:0]      kc_we,
    input  wire  [25*64-1:0] kc_wdata,
    input  wire  [11:0]      p2_we,
    input  wire  [12*64-1:0] p2_wdata
);
    wire [63:0] st [25];
    wire [63:0] sh [8];

    genvar i;
    generate
        for (i = 0; i < 25; i++) begin : g_lane
            wire        sc_we = wr_en && (wr_addr == 6'(i));
            wire        p2_w  = (i < 12) ? p2_we[i] : 1'b0;
            wire [63:0] p2_d  = (i < 12) ? p2_wdata[64*i +: 64] : 64'd0;
            wire        ab_w  = (i < 8)  ? blk_absorb_mask[i] : 1'b0;
            wire [63:0] ab_d  = (i < 8)  ? (st[i] ^ sh[i]) : 64'd0;
            wire        we    = wipe | kc_we[i] | p2_w | ab_w | sc_we;
            wire [63:0] wd    = wipe     ? 64'd0 :
                                kc_we[i] ? kc_wdata[64*i +: 64] :
                                p2_w     ? p2_d :
                                ab_w     ? ab_d : wr_data;
            qsag_ereg_nr #(.W(64)) u_r (.clk(clk), .en(we), .d(wd), .q(st[i]));
            assign st_flat_o[64*i +: 64] = st[i];
        end
    endgenerate

    wire        sh_sel = wr_en && (wr_addr[5:3] == 3'b100);
    wire [63:0] wd_sh_q;
    qsag_ereg_nr #(.W(64)) u_wd_hold (
        .clk(clk), .en(wipe | sh_sel), .d(wipe ? 64'd0 : wr_data), .q(wd_sh_q)
    );
    generate
        for (i = 0; i < 8; i++) begin : g_shadow
            wire sh_we = wipe || (sh_sel && (wr_addr[2:0] == 3'(i)));
            wire gate;
            qsag_clkgate u_cg (.clk(clk), .en(sh_we), .gclk(gate));
            qsag_latch_word #(.W(64)) u_lat (.gate(gate), .d(wd_sh_q), .q(sh[i]));
        end
    endgenerate

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
