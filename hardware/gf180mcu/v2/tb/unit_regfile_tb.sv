// Unit bench top for the register file: dregg_regfile behind dregg_rst, with a row dump.
`default_nettype none
module unit_regfile_tb (
    input  wire          clk,
    input  wire          por_n,
    input  wire          tamper_n,
    input  wire          zreq,
    input  wire          h_en,
    input  wire  [63:0]  h_d,
    output wire  [63:0]  h_q,
    input  wire          we,
    input  wire  [6:0]   waddr,
    input  wire  [1:0]   out_we,
    input  wire  [3:0]   wipe,
    input  wire  [6:0]   kw_we,
    input  wire  [319:0] kc_d,
    input  wire  [63:0]  kb_d,
    output wire  [447:0] kw_q,
    input  wire  [6:0]   raddr,
    output wire  [63:0]  rdata,
    output wire  [127:0] out_q,
    output wire          srst_n,
    input  wire  [6:0]   dump_row,
    output logic [63:0]  dump_data,
    output wire  [7:0]   nrows_o, key0_o, kwork0_o, scratch0_o, pin0_o, out0_o
);
`include "dregg_defs.svh"
    wire rst_n, fc, tl;
    wire [71:0] wl_en;
    dregg_rst u_rst (.clk(clk), .por_n(por_n), .tamper_n(tamper_n), .zreq(zreq), .rst_n(rst_n), .srst_n(srst_n),
                     .fault_control(fc), .tampered(tl));
    dregg_regfile u_rf (.clk(clk), .srst_n(srst_n), .h_en(h_en), .h_d(h_d), .h_q(h_q), .we(we), .waddr(waddr),
                        .out_we(out_we), .wipe(wipe), .kw_we(kw_we), .kc_d(kc_d), .kb_d(kb_d), .kw_q(kw_q),
                        .raddr(raddr), .rdata(rdata), .out_q(out_q), .wl_en_o(wl_en));
    wire [NROWS-1:0] col [64];
    genvar b;
    generate
        for (b = 0; b < 64; b++) begin : g_col
            assign col[b] = u_rf.g_bit[b].u_s.q_all;
        end
    endgenerate
    always_comb begin
        dump_data = '0;
        for (int i = 0; i < 64; i++) if (dump_row < 7'(NROWS)) dump_data[i] = col[i][dump_row];
    end
    assign nrows_o = 8'(NROWS);
    assign key0_o = 8'(KEY0);
    assign kwork0_o = 8'(KWORK0);
    assign scratch0_o = 8'(SCRATCH0);
    assign pin0_o = 8'(PIN0);
    assign out0_o = 8'(OUT0);
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, rst_n, fc, tl, wl_en};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire
