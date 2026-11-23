// Unified 2,560-bit 0-clock tamper-wipeable secret bank (`R1..R15` + `S0..S24`):
//   - Dual-phase zero-borrow write clocking (`set_max_time_borrow 0.0` clean across all 9 corners):
//       * `u_rdata` (shared as `wdata_q`) & `row_sel_n_q` launch on `posedge clk` (`t = 0`);
//       * `nor2_2(.A1(clk), .A2(row_sel_n_q))` holds `latrnq_1.E == 0` throughout `clk == 1`
//         (`t = 0 .. T/2`, glitch-free) and opens `E == 1` only during `clk == 0` (`t = T/2 .. T`).
//   - Hierarchical 5-octet (`5 x 8 = 40`) upsizable `aoi22_2 + nand2_2 + or2_2` read mux
//     (`0` `aoi222_1` cells, `0` `(* keep *)` sizing handicaps on combinational read gates!).
//   - Preserves exact `g_gpr[1..15].g_bit[0..63].u_lat` & `g_spg[0..24].g_bit[0..63].u_lat`
//     physical `latrnq_1` census (`2,560` secret latches).
module qsag_ass2_regbank (
    input  logic        clk,
    input  logic        srst_n,
    input  logic        zeroize_i,
    input  logic        s_clear_i,
    input  logic        zeroize_r3_spg_i = 1'b0,
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
    wire write_zero = zeroize_i || s_clear_i || zeroize_r3_spg_i;
    wire any_we     = write_zero || (r_we_i && r_waddr_i != 4'd0) || (s_we_i && s_waddr_i < 5'd25);
    wire [63:0] mux_wdata = write_zero ? 64'd0 : (s_we_i ? s_wdata_i : r_wdata_i);

    logic [63:0] regs_int [16];
    logic [63:0] spg_int  [25];
    assign regs_int[0] = 64'd0;

`ifndef SYNTHESIS
    assign dbg_regs_o = regs_int;
    assign dbg_spg_o  = spg_int;
`endif

`ifdef GF180_SRAM_MACRO
    for (genvar k = 0; k < 64; k++) begin : g_r4_buf
        gf180mcu_fd_sc_mcu7t5v0__buf_2 u_r4b (.I(regs_int[4][k]), .Z(r4_o[k]));
    end

    // Reads (`bank_re_i`) and writes (`any_we`) occur on strictly disjoint core/crypto clocks.
    // Sharing `u_rdata` as `wdata_q` saves 64 FFs AND synchronously clears `bank_rdata_o` on `zeroize_i`!
    wire [63:0] wdata_q = bank_rdata_o;

    wire [7:0] rst_branch;
    for (genvar b = 0; b < 8; b++) begin : g_rst_buf
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_8 u_rbuf (.I(srst_n), .Z(rst_branch[b]));
    end

    wire write_active_q, sel_gclk, sel_clk;
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__dffrnq_1 u_wact (
        .CLK(clk), .D(any_we), .RN(rst_branch[0]), .Q(write_active_q)
    );
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__icgtp_2 u_sel_icg (
        .CLK(clk), .E(any_we || write_active_q), .TE(1'b0), .Q(sel_gclk)
    );
    (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 u_sel_cbuf (
        .I(sel_gclk), .Z(sel_clk)
    );

    wire [63:0] wdata_buf;
    for (genvar bit_i = 0; bit_i < 64; bit_i++) begin : g_wbuf
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__buf_4 u_dbuf (
            .I(wdata_q[bit_i]), .Z(wdata_buf[bit_i])
        );
    end

    for (genvar r = 1; r < 16; r++) begin : g_gpr
        wire row_en      = zeroize_i || ((r >= 3) && zeroize_r3_spg_i) || (r_we_i && (r_waddr_i == 4'(r)));
        wire row_sel_n_d = ~(any_we && row_en);
        wire row_sel_n_q, gclk_raw, gclk;
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__dffsnq_1 u_rsel (
            .CLK(sel_clk), .D(row_sel_n_d), .SETN(rst_branch[r / 5]), .Q(row_sel_n_q)
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__nor2_2 u_gclk (
            .A1(clk), .A2(row_sel_n_q), .ZN(gclk_raw)
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 u_gbuf (.I(gclk_raw), .Z(gclk));
        for (genvar k = 0; k < 64; k++) begin : g_bit
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_lat (
                .D(wdata_buf[k]), .E(gclk), .RN(rst_branch[r / 5]), .Q(regs_int[r][k])
            );
        end
    end

    for (genvar s = 0; s < 25; s++) begin : g_spg
        wire row_en      = write_zero || (s_we_i && (s_waddr_i == 5'(s)));
        wire row_sel_n_d = ~(any_we && row_en);
        wire row_sel_n_q, gclk_raw, gclk;
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__dffsnq_1 u_rsel (
            .CLK(sel_clk), .D(row_sel_n_d), .SETN(rst_branch[3 + (s / 5)]), .Q(row_sel_n_q)
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__nor2_2 u_gclk (
            .A1(clk), .A2(row_sel_n_q), .ZN(gclk_raw)
        );
        (* keep *) gf180mcu_fd_sc_mcu7t5v0__clkbuf_4 u_gbuf (.I(gclk_raw), .Z(gclk));
        for (genvar k = 0; k < 64; k++) begin : g_bit
            (* keep *) gf180mcu_fd_sc_mcu7t5v0__latrnq_1 u_lat (
                .D(wdata_buf[k]), .E(gclk), .RN(rst_branch[3 + (s / 5)]), .Q(spg_int[s][k])
            );
        end
    end
`else
    assign r4_o = regs_int[4];
    for (genvar r = 1; r < 16; r++) begin : g_gpr_sim
        always_ff @(posedge clk or negedge srst_n) begin
            if (!srst_n) regs_int[r] <= 64'd0;
            else if (zeroize_i || ((r >= 3) && zeroize_r3_spg_i)) regs_int[r] <= 64'd0;
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
`endif

    // Zero-adder one-hot row decode across 40 rows (`5 x 8 = 40`)
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

    wire [63:0] grp_rdata [5];
`ifdef GF180_SRAM_MACRO
    for (genvar grp = 0; grp < 5; grp++) begin : g_octet_rd
        wire [7:0] rsel_buf;
        for (genvar r = 0; r < 8; r++) begin : g_sbuf
            gf180mcu_fd_sc_mcu7t5v0__buf_4 u_sbuf (
                .I(rsel[8*grp + r]), .Z(rsel_buf[r])
            );
        end
        for (genvar k = 0; k < 64; k++) begin : g_k
            wire [3:0] pair_n;
            for (genvar p = 0; p < 4; p++) begin : g_p
                gf180mcu_fd_sc_mcu7t5v0__aoi22_1 u_aoi2 (
                    .A1(rsel_buf[2*p]),     .A2(row_q[8*grp + 2*p][k]),
                    .B1(rsel_buf[2*p + 1]), .B2(row_q[8*grp + 2*p + 1][k]),
                    .ZN(pair_n[p])
                );
            end
            gf180mcu_fd_sc_mcu7t5v0__nand4_2 u_n4 (
                .A1(pair_n[0]), .A2(pair_n[1]), .A3(pair_n[2]), .A4(pair_n[3]),
                .ZN(grp_rdata[grp][k])
            );
        end
    end
    wire unused_raddr_warn = unused_raddr4;
`else
    for (genvar grp = 0; grp < 5; grp++) begin : g_octet_sim
        assign grp_rdata[grp] = (rsel[8*grp + 0] ? row_q[8*grp + 0] : 64'd0)
                              | (rsel[8*grp + 1] ? row_q[8*grp + 1] : 64'd0)
                              | (rsel[8*grp + 2] ? row_q[8*grp + 2] : 64'd0)
                              | (rsel[8*grp + 3] ? row_q[8*grp + 3] : 64'd0)
                              | (rsel[8*grp + 4] ? row_q[8*grp + 4] : 64'd0)
                              | (rsel[8*grp + 5] ? row_q[8*grp + 5] : 64'd0)
                              | (rsel[8*grp + 6] ? row_q[8*grp + 6] : 64'd0)
                              | (rsel[8*grp + 7] ? row_q[8*grp + 7] : 64'd0);
    end
    wire unused_raddr_warn = unused_raddr4;
`endif

    wire [63:0] bank_rdata_comb = (grp_rdata[0] | grp_rdata[1])
                                | (grp_rdata[2] | grp_rdata[3])
                                | grp_rdata[4];
    qsag_ass2_cg_dff #(.W(64)) u_rdata (
        .clk(clk), .rst_n(srst_n), .en(any_we || bank_re_i),
        .d(any_we ? mux_wdata : bank_rdata_comb), .q(bank_rdata_o)
    );
endmodule
