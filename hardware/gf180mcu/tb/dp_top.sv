// Datapath unit-test harness: sponge register file + arithmetic unit + field engine.
`default_nettype none
module dp_top (
    input  wire         clk,
    input  wire         rst_n,
    input  wire         start,
    input  wire [3:0]   op,
    input  wire [5:0]   d,
    input  wire [5:0]   s1,
    input  wire [5:0]   s2,
    input  wire [2:0]   n,
    input  wire         dir,
    input  wire [63:0]  xw,
    output wire         busy,
    output wire         done,
    output wire         eq,
    output wire [63:0]  res,
    // direct access (engine idle)
    input  wire         tb_we,
    input  wire [5:0]   tb_addr,
    input  wire [63:0]  tb_wdata,
    output wire [63:0]  tb_rdata,
    // Keccak
    input  wire         k_start,
    input  wire         k_turbo,
    output wire         k_done
);
    wire [5:0]   fe_rd, fe_wa;
    wire         fe_we;
    wire [1:0]   pm, rk;
    wire [3:0]   pk;
    wire [2:0]   rm;
    wire         krc, acc_clr, acc_we, ld_opa, ld_opb, ld_res, mul_start, mul_asel, mul_bsel;
    wire         mul_last, mul_busy, cv_zero;
    wire [6:0]   rc_idx;
    wire [63:0]  rc, cv, port, k_wd;
    wire [5:0]   k_rd, k_wa;
    wire         k_we, k_busy;
    wire [127:0] kmac_q;

    qsag_field_engine u_fe (
        .clk, .rst_n, .start, .op, .d, .s1, .s2, .n, .dir, .busy, .done, .eq,
        .rd_addr(fe_rd), .wr_en(fe_we), .wr_addr(fe_wa),
        .pm, .pk, .rm, .rk, .krc, .acc_clr, .acc_we, .ld_opa, .ld_opb, .ld_res,
        .mul_start, .mul_asel, .mul_bsel, .mul_last, .cv_zero, .rc_idx
    );
    qsag_p2_rc u_rc (.idx(rc_idx), .rc(rc));
    qsag_gl64_karatsuba_csa u_alu (
        .clk, .rst_n, .port, .xw, .rc, .pm, .pk, .rm, .rk, .krc, .acc_clr, .acc_we,
        .ld_opa, .ld_opb, .ld_res, .mul_start, .mul_asel, .mul_bsel,
        .mul_busy, .mul_last, .cv, .cv_zero, .res
    );
    qsag_keccak_serial u_kc (
        .clk, .rst_n, .srst_n(rst_n), .start(k_start), .turbo(k_turbo), .fault_inj(1'b0),
        .busy(k_busy), .done(k_done),
        .rd_addr(k_rd), .port, .wr_en(k_we), .wr_addr(k_wa), .wr_data(k_wd)
    );
    wire [63:0]  sp_hold_u;
    qsag_sponge u_sp (
        .clk, .srst_n(rst_n), .wipe(!rst_n),
        .wr_en(busy ? fe_we : k_busy ? k_we : tb_we),
        .wr_addr(busy ? fe_wa : k_busy ? k_wa : tb_addr),
        .wr_data(busy ? cv : k_busy ? k_wd : tb_wdata),
        .rd_addr(busy ? fe_rd : k_busy ? k_rd : tb_addr), .rd_data(port),
        .aux_we(1'b0), .aux_addr(5'd0), .aux_wdata(64'd0),
        .ext_hold_en(1'b0), .hold_q(sp_hold_u), .kmac_q(kmac_q)
    );
    assign tb_rdata = port;
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, mul_busy, kmac_q, sp_hold_u};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire
