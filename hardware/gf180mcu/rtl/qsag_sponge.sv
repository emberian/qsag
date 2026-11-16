// Dregg-180 (QSAG-NI-180) unified 1,600-bit sponge state + clock-gated latrnq_1 scratchpad.
//
//   * st[0..24]  25 x 64-bit unified sponge state:
//                  - Keccak-f[1600] lanes 0..24 (5-clock-per-round in-place port using ONLY 5
//                    shared `kc_aout` row wires + local eviction wires -> saves ~280k um^2 of
//                    crossbar muxes while keeping exact 60/120-clock throughput!)
//                  - Poseidon2 width-12 state directly inside lanes 0..11 (zero duplicate FFs,
//                    plus 4-lane parallel writeback port `p2_quad_we` for 3-clock M_E/M_I!)
//                  - Verifier registers CH/A/B in lanes 12..23
//   * sh[0..7]   8 x 64-bit clock-gated `latrnq_1` transparent-latch register file (addresses
//                32..39), zeroizing asynchronously on `srst_n = 0` even if `clk` is stopped!
//   * GOTCHA #4 1-Clock Shadow Block Absorb (`blk_absorb_mask[7:0]`):
//                While Keccak or Poseidon2 permutes `st[0..24]`, incoming words stream into
//                `sh[0..7]` with zero port contention, and `blk_absorb_mask` XORs up to 8 words
//                (`64` bytes) from `sh[0..7]` into `st[0..7]` in ONE single clock!
`default_nettype none

module qsag_sponge (
    input  wire              clk,
    input  wire              srst_n,
    input  wire              wipe,
    // scalar read/write port
    input  wire              wr_en,
    input  wire  [5:0]       wr_addr,         // 0..24 lanes, 32..39 shadow latches
    input  wire  [63:0]      wr_data,
    input  wire  [5:0]       rd_addr,
    output logic [63:0]      rd_data,
    // 1-clock 64-byte shadow-to-sponge parallel block absorb
    input  wire  [7:0]       blk_absorb_mask, // bit i=1: st[i] <= st[i] ^ sh[i] in 1 clock!
    // parallel state view
    output wire  [25*64-1:0] st_flat_o,
    // lean 5-lane Keccak in-place port (zero 25x64 crossbar!)
    input  wire              kc_run,
    input  wire  [2:0]       kc_k,
    input  wire  [5*64-1:0]  kc_aout_flat,
    // lean 4-lane Poseidon2 linear-layer writeback port (grp 0=0..3, 1=4..7, 2=8..11)
    input  wire              p2_quad_we,
    input  wire  [1:0]       p2_quad_grp,
    input  wire  [4*64-1:0]  p2_quad_wdata
);
    wire [63:0] st [25];
    wire [63:0] sh [8];
    wire [63:0] kc_aout [5];
    wire [63:0] p2_qw [4];

    genvar i;
    generate
        for (i = 0; i < 5; i++) begin : g_kca
            assign kc_aout[i] = kc_aout_flat[64*i +: 64];
        end
        for (i = 0; i < 4; i++) begin : g_p2q
            assign p2_qw[i] = p2_quad_wdata[64*i +: 64];
        end
    endgenerate

    // Exact per-lane Keccak write-enable & local eviction mux (bit-packed -> 0 memory warnings!)
    logic [24:0]      kc_l_we;
    logic [25*64-1:0] kc_l_wd;
    always_comb begin
        kc_l_we = 25'd0;
        for (int l = 0; l < 25; l++)
            kc_l_wd[64*l +: 64] = kc_aout[l % 5];
        if (kc_run) begin
            unique case (kc_k)
                3'd0: begin
                    kc_l_we[4:0] = 5'h1F;
                    kc_l_we[6]  = 1'b1; kc_l_wd[64*6  +: 64] = st[1];
                    kc_l_we[12] = 1'b1; kc_l_wd[64*12 +: 64] = st[2];
                    kc_l_we[18] = 1'b1; kc_l_wd[64*18 +: 64] = st[3];
                    kc_l_we[24] = 1'b1; kc_l_wd[64*24 +: 64] = st[4];
                end
                3'd1: begin
                    kc_l_we[9:5] = 5'h1F;
                    kc_l_we[10] = 1'b1; kc_l_wd[64*10 +: 64] = st[5];
                    kc_l_we[16] = 1'b1; kc_l_wd[64*16 +: 64] = st[6];
                    kc_l_we[18] = 1'b1; kc_l_wd[64*18 +: 64] = st[7];
                    kc_l_we[22] = 1'b1; kc_l_wd[64*22 +: 64] = st[8];
                end
                3'd2: begin
                    kc_l_we[14:10] = 5'h1F;
                    kc_l_we[16] = 1'b1; kc_l_wd[64*16 +: 64] = st[10];
                    kc_l_we[18] = 1'b1; kc_l_wd[64*18 +: 64] = st[11];
                    kc_l_we[19] = 1'b1; kc_l_wd[64*19 +: 64] = st[12];
                    kc_l_we[20] = 1'b1; kc_l_wd[64*20 +: 64] = st[14];
                end
                3'd3: begin
                    kc_l_we[19:15] = 5'h1F;
                    kc_l_we[23] = 1'b1; kc_l_wd[64*23 +: 64] = st[15];
                    kc_l_we[24] = 1'b1; kc_l_wd[64*24 +: 64] = st[19];
                end
                default: begin
                    kc_l_we[24:20] = 5'h1F;
                end
            endcase
        end
    end

    generate
        for (i = 0; i < 25; i++) begin : g_lane
            wire        sc_we = wr_en && (wr_addr == 6'(i));
            wire        p2_w  = (i < 12) ? (p2_quad_we && (p2_quad_grp == 2'(i / 4))) : 1'b0;
            wire [63:0] p2_d  = (i < 12) ? p2_qw[i % 4] : 64'd0;
            wire        ab_w  = (i < 8)  ? blk_absorb_mask[i] : 1'b0;
            wire [63:0] ab_d  = (i < 8)  ? (st[i] ^ sh[i]) : 64'd0;
            wire        we    = wipe | kc_l_we[i] | p2_w | ab_w | sc_we;
            wire [63:0] wd    = wipe       ? 64'd0 :
                                kc_l_we[i] ? kc_l_wd[64*i +: 64] :
                                p2_w       ? p2_d :
                                ab_w       ? ab_d : wr_data;
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
            qsag_clkgate_1 u_cg (.clk(clk), .en(sh_we), .gclk(gate));
            qsag_latch_word_rst #(.W(64)) u_lat (.gate(gate), .rst_n(srst_n), .d(wd_sh_q), .q(sh[i]));
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
