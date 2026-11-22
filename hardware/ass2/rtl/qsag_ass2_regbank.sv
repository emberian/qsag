// Unified 2,560-bit 0-clock tamper-wipeable secret bank (`R1..R15` + `S0..S24`):
//   - Partitioned into 5 local 8-row octets (`8 x 64` latches each):
//       * Local `buf_4` per bit per octet (`fanout = 8`, zero 40-sink global write nets)
//       * Local `aoi22_1` + `nand4_1` 8:1 read reduction per octet so only `5 x 64 = 320`
//         wires cross between octets (eliminating 2,560-wire routing congestion!)
//   - Registered `bank_rdata_o` (`qsag_ass2_cg_dff`) severs the regbank read tree from
//     downstream ALU/crypto cones (< 12 ns SS arrival!).
//   - Address encoding: `bank_raddr_i[5] == 0` -> `R[bank_raddr_i[3:0]]` (`0` reads `0`),
//                       `bank_raddr_i[5] == 1` -> `S[bank_raddr_i[4:0]]` (`0..24`).
module qsag_ass2_regbank (
    input  logic        clk,
    input  logic        srst_n,
    input  logic        zeroize_i,
    input  logic        s_clear_i,
    input  logic        r_we_i,
    input  logic [3:0]  r_waddr_i,
    input  logic [63:0] r_wdata_i,
    input  logic        s_we_i,
    input  logic [4:0]  s_waddr_i,
    input  logic [63:0] s_wdata_i,
    input  logic        bank_re_i,
    input  logic [5:0]  bank_raddr_i,
    output logic [63:0] bank_rdata_o,
    output logic [63:0] r4_o
`ifndef SYNTHESIS
    , output logic [63:0] dbg_regs_o [16]
    , output logic [63:0] dbg_spg_o  [25]
`endif
);
    wire write_zero = zeroize_i || s_clear_i;
    wire any_we     = write_zero || (r_we_i && r_waddr_i != 4'd0) || (s_we_i && s_waddr_i < 5'd25);
    wire [63:0] mux_wdata = write_zero ? 64'd0 : (s_we_i ? s_wdata_i : r_wdata_i);

    logic [63:0] regs_int [16];
    logic [63:0] spg_int  [25];
    assign regs_int[0] = 64'd0;
    assign r4_o        = regs_int[4];

`ifndef SYNTHESIS
    assign dbg_regs_o = regs_int;
    assign dbg_spg_o  = spg_int;
`endif

`ifdef GF180_SRAM_MACRO
    logic [63:0] wdata_q;
    qsag_ass2_cg_dff #(.W(64)) u_whold (
        .clk(clk), .rst_n(srst_n), .en(any_we), .d(mux_wdata), .q(wdata_q)
    );

    wire [7:0] rst_branch;
    for (genvar b = 0; b < 8; b++) begin : g_rst_buf
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_8 u_rbuf (.I(srst_n), .Z(rst_branch[b]));
    end

    // Per-octet local write-data buffers (fanout = 8 latches per `buf_4` instead of 40 global sinks!)
    wire [63:0] oct_wdata [5];
    for (genvar oct = 0; oct < 5; oct++) begin : g_oct_wbuf
        for (genvar bit_i = 0; bit_i < 64; bit_i++) begin : g_bit
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_4 u_dbuf (
                .I(wdata_q[bit_i]), .Z(oct_wdata[oct][bit_i])
            );
        end
    end

    // Preserve exact `g_gpr[1..15].g_bit[0..63].u_lat` & `g_spg[0..24].g_bit[0..63].u_lat`
    // hierarchy names for 4-state foundry gate-level physical latch census & tamper verification!
    for (genvar r = 1; r < 16; r++) begin : g_gpr
        localparam int OCT_IDX = (r - 1) / 8;
        wire row_en = zeroize_i || (r_we_i && (r_waddr_i == 4'(r)));
        wire gclk_raw, gclk;
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_2 u_icg (
            .CLK(clk), .E(row_en), .TE(1'b0), .Q(gclk_raw)
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 u_gbuf (.I(gclk_raw), .Z(gclk));
        for (genvar k = 0; k < 64; k++) begin : g_bit
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_lat (
                .D(oct_wdata[OCT_IDX][k]), .E(gclk), .RN(rst_branch[r / 5]), .Q(regs_int[r][k])
            );
        end
    end

    for (genvar s = 0; s < 25; s++) begin : g_spg
        localparam int OCT_IDX = (15 + s) / 8;
        wire row_en = zeroize_i || s_clear_i || (s_we_i && (s_waddr_i == 5'(s)));
        wire gclk_raw, gclk;
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_2 u_icg (
            .CLK(clk), .E(row_en), .TE(1'b0), .Q(gclk_raw)
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 u_gbuf (.I(gclk_raw), .Z(gclk));
        for (genvar k = 0; k < 64; k++) begin : g_bit
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_lat (
                .D(oct_wdata[OCT_IDX][k]), .E(gclk), .RN(rst_branch[3 + (s / 5)]), .Q(spg_int[s][k])
            );
        end
    end
`else
    for (genvar r = 1; r < 16; r++) begin : g_gpr_sim
        always_ff @(posedge clk or negedge srst_n) begin
            if (!srst_n) regs_int[r] <= 64'd0;
            else if (zeroize_i) regs_int[r] <= 64'd0;
            else if (r_we_i && r_waddr_i == 4'(r)) regs_int[r] <= mux_wdata;
        end
    end
    for (genvar s = 0; s < 25; s++) begin : g_spg_sim
        always_ff @(posedge clk or negedge srst_n) begin
            if (!srst_n) spg_int[s] <= 64'd0;
            else if (write_zero) spg_int[s] <= 64'd0;
            else if (s_we_i && s_waddr_i == 5'(s)) spg_int[s] <= mux_wdata;
        end
    end
    wire unused_any_we = any_we;
`endif

    // Zero-adder one-hot row decode + 5 local 8:1 octet reductions
    wire [39:0] rsel;
    wire [63:0] row_q [40];
    for (genvar i = 0; i < 15; i++) begin : g_rsel_gpr
        assign rsel[i]  = !bank_raddr_i[5] && (bank_raddr_i[3:0] == 4'(i + 1));
        assign row_q[i] = regs_int[i + 1];
    end
    for (genvar j = 0; j < 25; j++) begin : g_rsel_spg
        assign rsel[15 + j]  = bank_raddr_i[5] && (bank_raddr_i[4:0] == 5'(j));
        assign row_q[15 + j] = spg_int[j];
    end
    wire unused_raddr4 = !bank_raddr_i[5] && bank_raddr_i[4];

    wire [63:0] oct_rdata [5];
`ifdef GF180_SRAM_MACRO
    for (genvar oct = 0; oct < 5; oct++) begin : g_oct_rd
        wire [7:0] rsel_buf;
        for (genvar r = 0; r < 8; r++) begin : g_sbuf
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_4 u_sbuf (
                .I(rsel[8*oct + r]), .Z(rsel_buf[r])
            );
        end
        for (genvar k = 0; k < 64; k++) begin : g_k
            wire [3:0] pair_n;
            for (genvar p = 0; p < 4; p++) begin : g_p
                (* keep *) gf180mcu_fd_sc_mcu7t5v0__aoi22_1 u_aoi (
                    .A1(rsel_buf[2*p]),     .A2(row_q[8*oct + 2*p][k]),
                    .B1(rsel_buf[2*p + 1]), .B2(row_q[8*oct + 2*p + 1][k]),
                    .ZN(pair_n[p])
                );
            end
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__nand4_1 u_n4 (
                .A1(pair_n[0]), .A2(pair_n[1]), .A3(pair_n[2]), .A4(pair_n[3]),
                .ZN(oct_rdata[oct][k])
            );
        end
    end
`else
    for (genvar oct = 0; oct < 5; oct++) begin : g_oct_rd_sim
        assign oct_rdata[oct] = (rsel[8*oct + 0] ? row_q[8*oct + 0] : 64'd0)
                              | (rsel[8*oct + 1] ? row_q[8*oct + 1] : 64'd0)
                              | (rsel[8*oct + 2] ? row_q[8*oct + 2] : 64'd0)
                              | (rsel[8*oct + 3] ? row_q[8*oct + 3] : 64'd0)
                              | (rsel[8*oct + 4] ? row_q[8*oct + 4] : 64'd0)
                              | (rsel[8*oct + 5] ? row_q[8*oct + 5] : 64'd0)
                              | (rsel[8*oct + 6] ? row_q[8*oct + 6] : 64'd0)
                              | (rsel[8*oct + 7] ? row_q[8*oct + 7] : 64'd0);
    end
    wire unused_raddr_warn = unused_raddr4;
`endif

    wire [63:0] bank_rdata_comb = (oct_rdata[0] | oct_rdata[1])
                                | (oct_rdata[2] | oct_rdata[3])
                                | oct_rdata[4];

    qsag_ass2_cg_dff #(.W(64)) u_rdata (
        .clk(clk), .rst_n(srst_n), .en(bank_re_i), .d(bank_rdata_comb), .q(bank_rdata_o)
    );
endmodule
