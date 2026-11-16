// Datapath unit-test harness: sponge register file + arithmetic unit + field engine.
// The testbench may write and read the register file directly while the engine is idle.
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
    input  wire         k_en,
    input  wire [4:0]   k_idx
);
    wire [5:0]  fe_rd, fe_wa;
    wire        fe_we;
    wire [1:0]  pm, rk;
    wire [3:0]  pk;
    wire [2:0]  rm;
    wire        krc, acc_clr, acc_we, ld_opa, ld_opb, ld_res, mul_start, mul_asel, mul_bsel;
    wire        mul_last, mul_busy, cv_zero;
    wire [6:0]  rc_idx;
    wire [63:0] rc, cv, port, krcw;

    qsag_field_engine u_fe (
        .clk, .rst_n, .start, .op, .d, .s1, .s2, .n, .dir, .busy, .done, .eq,
        .rd_addr(fe_rd), .wr_en(fe_we), .wr_addr(fe_wa),
        .pm, .pk, .rm, .rk, .krc, .acc_clr, .acc_we, .ld_opa, .ld_opb, .ld_res,
        .mul_start, .mul_asel, .mul_bsel, .mul_last, .cv_zero, .rc_idx
    );
    qsag_p2_rc u_rc (.idx(rc_idx), .rc(rc));
    qsag_keccak_rc u_krc (.idx(k_idx), .rc(krcw));
    qsag_gl64_karatsuba_csa u_alu (
        .clk, .rst_n, .port, .xw, .rc, .pm, .pk, .rm, .rk, .krc, .acc_clr, .acc_we,
        .ld_opa, .ld_opb, .ld_res, .mul_start, .mul_asel, .mul_bsel,
        .mul_busy, .mul_last, .cv, .cv_zero, .res
    );
    qsag_sponge u_sp (
        .clk, .rst_n, .k_en, .k_rc(krcw),
        .wr_en(busy ? fe_we : tb_we), .wr_addr(busy ? fe_wa : tb_addr),
        .wr_data(busy ? cv : tb_wdata),
        .rd_addr(busy ? fe_rd : tb_addr), .rd_data(port)
    );
    assign tb_rdata = port;
    wire unused = &{1'b0, mul_busy};
endmodule
`default_nettype wire
