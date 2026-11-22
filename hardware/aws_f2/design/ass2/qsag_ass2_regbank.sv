// Unified 2,560-bit 0-clock tamper-wipeable secret bank (`R1..R15` + `S0..S24`):
//   - Pre-decoded 40-bit one-hot row-enable + balanced OR-of-ANDs read tree so ABC maps
//     pairs directly to `aoi22_1` (9.88 um^2/port vs 28.53 um^2/port priority muxes).
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
    input  logic [5:0]  bank_raddr_i,
    output logic [63:0] bank_rdata_o,
    output logic [63:0] regs_o [16],
    output logic [63:0] spg_o  [25]
);
    wire write_zero = zeroize_i || s_clear_i;
    wire any_we     = write_zero || (r_we_i && r_waddr_i != 4'd0) || (s_we_i && s_waddr_i < 5'd25);
    wire [63:0] mux_wdata = write_zero ? 64'd0 : (s_we_i ? s_wdata_i : r_wdata_i);

`ifdef GF180_SRAM_MACRO
    logic [63:0] wdata_q;
    qsag_ass2_cg_dff #(.W(64)) u_whold (
        .clk(clk), .rst_n(srst_n), .en(any_we), .d(mux_wdata), .q(wdata_q)
    );

    wire [7:0] rst_branch;
    for (genvar b = 0; b < 8; b++) begin : g_rst_buf
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_8 u_rbuf (.I(srst_n), .Z(rst_branch[b]));
    end

    wire [63:0] wdata_buf;
    for (genvar bit_i = 0; bit_i < 64; bit_i++) begin : g_wbuf
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_4 u_dbuf (.I(wdata_q[bit_i]), .Z(wdata_buf[bit_i]));
    end

    assign regs_o[0] = 64'd0;
    for (genvar r = 1; r < 16; r++) begin : g_gpr
        wire row_en = zeroize_i || (r_we_i && (r_waddr_i == 4'(r)));
        wire gclk_raw, gclk;
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_2 u_icg (
            .CLK(clk), .E(row_en), .TE(1'b0), .Q(gclk_raw)
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 u_gbuf (.I(gclk_raw), .Z(gclk));
        for (genvar k = 0; k < 64; k++) begin : g_bit
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_lat (
                .D(wdata_buf[k]), .E(gclk), .RN(rst_branch[r / 5]), .Q(regs_o[r][k])
            );
        end
    end

    for (genvar s = 0; s < 25; s++) begin : g_spg
        wire row_en = zeroize_i || s_clear_i || (s_we_i && (s_waddr_i == 5'(s)));
        wire gclk_raw, gclk;
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_2 u_icg (
            .CLK(clk), .E(row_en), .TE(1'b0), .Q(gclk_raw)
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 u_gbuf (.I(gclk_raw), .Z(gclk));
        for (genvar k = 0; k < 64; k++) begin : g_bit
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_lat (
                .D(wdata_buf[k]), .E(gclk), .RN(rst_branch[3 + (s / 5)]), .Q(spg_o[s][k])
            );
        end
    end
`else
    assign regs_o[0] = 64'd0;
    for (genvar r = 1; r < 16; r++) begin : g_gpr_sim
        always_ff @(posedge clk or negedge srst_n) begin
            if (!srst_n) regs_o[r] <= 64'd0;
            else if (zeroize_i) regs_o[r] <= 64'd0;
            else if (r_we_i && r_waddr_i == 4'(r)) regs_o[r] <= mux_wdata;
        end
    end
    for (genvar s = 0; s < 25; s++) begin : g_spg_sim
        always_ff @(posedge clk or negedge srst_n) begin
            if (!srst_n) spg_o[s] <= 64'd0;
            else if (write_zero) spg_o[s] <= 64'd0;
            else if (s_we_i && s_waddr_i == 5'(s)) spg_o[s] <= mux_wdata;
        end
    end
    wire unused_any_we = any_we;
`endif

    // Shared 40-way one-hot decode + balanced OR-of-ANDs read network
    wire [39:0] rsel;
    wire [63:0] row_masked [40];
    for (genvar i = 0; i < 15; i++) begin : g_rm_gpr
        assign rsel[i]       = (bank_raddr_i == 6'(i + 1));
        assign row_masked[i] = rsel[i] ? regs_o[i + 1] : 64'd0;
    end
    for (genvar j = 0; j < 25; j++) begin : g_rm_spg
        assign rsel[15 + j]       = (bank_raddr_i == 6'(16 + j));
        assign row_masked[15 + j] = rsel[15 + j] ? spg_o[j] : 64'd0;
    end

    wire [63:0] grp8 [5];
    for (genvar g = 0; g < 5; g++) begin : g_grp
        assign grp8[g] = (row_masked[8*g + 0] | row_masked[8*g + 1])
                       | (row_masked[8*g + 2] | row_masked[8*g + 3])
                       | (row_masked[8*g + 4] | row_masked[8*g + 5])
                       | (row_masked[8*g + 6] | row_masked[8*g + 7]);
    end
    assign bank_rdata_o = (grp8[0] | grp8[1]) | (grp8[2] | grp8[3]) | grp8[4];
endmodule
