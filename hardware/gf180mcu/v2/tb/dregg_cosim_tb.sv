// Co-simulation bench top: dregg_core with a loadable ROM, a word-level link, the FRAM pins, the
// stage 3 / 4 interface stand-ins, a state dump, the fixture backdoor, and the two lockstep references
// (the unmodified qsag_keccak_serial and qsag_anchor_spi run beside their v2 copies).
`default_nettype none

module dregg_cosim_tb #(
    parameter bit H_SHADOW = 1'b1,
    parameter bit KEC_WAIT_AFTER_STORE = 1'b1,
    parameter bit FRAM_DONE_PAD = 1'b1
) (
    input  wire         clk,
    input  wire         por_n,
    input  wire         tamper_n,
    input  wire         in_valid,
    input  wire         in_first,
    input  wire  [63:0] in_data,
    output wire         in_take,
    output wire         out_valid,
    output wire  [63:0] out_data,
    input  wire         out_take,
    input  wire         ld_we,
    input  wire  [1:0]  ld_sel,
    input  wire  [10:0] ld_addr,
    input  wire  [63:0] ld_data,
    output wire         fram_cs_n,
    output wire         fram_sck,
    output wire         fram_mosi,
    input  wire         fram_miso,
    input  wire         puf_present,
    input  wire  [255:0] puf_secret,
    input  wire         ent_present,
    output wire         ent_req,
    input  wire         ent_valid,
    input  wire  [127:0] ent_data,
    output wire         own_start,
    output wire         own_valid,
    output wire  [2:0]  own_idx,
    output wire  [63:0] own_data,
    input  wire         own_done,
    input  wire         own_ok,
    output wire         verify_ok,
    output wire         fault,
    output wire         ready,
    output wire         cmd_active,
    output wire         link_wait,
    output wire         stall,
    output wire         fault_now,
    output wire  [5:0]  fault_why,
    output wire  [10:0] pc,
    // backdoor (fixtures) and dump
    input  wire         bd_rf_we,
    input  wire  [6:0]  bd_row,
    input  wire  [63:0] bd_data,
    input  wire         bd_fl_we,
    input  wire  [8:0]  bd_flags,
    input  wire  [127:0] bd_nonce,
    input  wire  [6:0]  dump_row,
    output logic [63:0] dump_data,
    output wire  [8:0]  dump_flags,   // {nonce_valid, key_attr[3:0], verify_ok, f_anchor, f_mac, key_valid}
    output wire  [127:0] dump_nonce,
    output wire         dump_dev_ok,
    output wire  [63:0] dump_h,
    output logic        lock_err,     // a lockstep reference disagreed (sticky)
    output wire  [31:0] assert_count, // failed checks in dregg_core
    output wire  [7:0]  nrows_o,
    output wire  [7:0]  key0_o
);
`include "dregg_defs.svh"
    wire [10:0] rom_addr;
    wire [27:0] rom_word;
    wire [6:0]  const_idx;
    wire [63:0] const_data;
    wire        const_ok, disp_hit;
    wire [7:0]  disp_op;
    wire [10:0] disp_addr;
    wire [1:0]  disp_class;
    wire [11:0] rom_len, rom_used;
    wire        puf_req, busy, rst_n_o, srst_n_o;
    wire [1:0]  puf_idx;

    dregg_urom_sim u_rom (
        .clk(clk), .ld_we(ld_we), .ld_sel(ld_sel), .ld_addr(ld_addr), .ld_data(ld_data),
        .rom_addr(rom_addr), .rom_word(rom_word), .const_idx(const_idx), .const_data(const_data), .const_ok(const_ok),
        .disp_op(disp_op), .disp_hit(disp_hit), .disp_addr(disp_addr), .disp_class(disp_class),
        .rom_len(rom_len), .rom_used(rom_used)
    );

    dregg_core #(.H_SHADOW(H_SHADOW), .KEC_WAIT_AFTER_STORE(KEC_WAIT_AFTER_STORE), .FRAM_DONE_PAD(FRAM_DONE_PAD)) dut (
        .clk(clk), .por_n(por_n), .tamper_n(tamper_n),
        .in_valid(in_valid), .in_first(in_first), .in_data(in_data), .in_take(in_take),
        .out_valid(out_valid), .out_data(out_data), .out_take(out_take),
        .rom_addr(rom_addr), .rom_word(rom_word), .const_idx(const_idx), .const_data(const_data), .const_ok(const_ok),
        .disp_op(disp_op), .disp_hit(disp_hit), .disp_addr(disp_addr), .disp_class(disp_class),
        .rom_len(rom_len), .rom_used(rom_used),
        .fram_cs_n(fram_cs_n), .fram_sck(fram_sck), .fram_mosi(fram_mosi), .fram_miso(fram_miso),
        .puf_present(puf_present), .puf_req(puf_req), .puf_idx(puf_idx), .puf_valid(1'b1),
        .puf_data(puf_secret[64*puf_idx +: 64]),
        .ent_present(ent_present), .ent_req(ent_req), .ent_valid(ent_valid), .ent_data(ent_data),
        .own_start(own_start), .own_valid(own_valid), .own_idx(own_idx), .own_data(own_data),
        .own_done(own_done), .own_ok(own_ok),
        .verify_ok(verify_ok), .fault(fault), .ready(ready), .busy(busy), .rst_n_o(rst_n_o), .srst_n_o(srst_n_o),
        .cmd_active(cmd_active), .link_wait(link_wait), .stall(stall), .fault_now(fault_now), .fault_why(fault_why),
        .pc(pc)
    );

    // ------------------------------------------------------------ dump
    wire [NROWS-1:0] col [64];
    genvar b;
    generate
        for (b = 0; b < 64; b++) begin : g_col
            assign col[b] = dut.u_rf.g_bit[b].u_s.q_all;
        end
    endgenerate
    always_comb begin
        dump_data = '0;
        for (int i = 0; i < 64; i++)
            if (dump_row < 7'(NROWS)) dump_data[i] = col[i][dump_row];
    end
    assign dump_flags  = {dut.u_seq.nonce_valid, dut.u_seq.key_attr, dut.u_seq.v_ok, dut.u_seq.f_anchor,
                          dut.u_seq.f_mac, dut.u_seq.key_valid};
    assign dump_nonce  = dut.u_seq.nonce;
    assign dump_dev_ok = dut.u_seq.dev_ok;
    assign dump_h      = dut.u_rf.h_q;
    assign assert_count = dut.assert_count;
    assign nrows_o      = 8'(NROWS);
    assign key0_o       = 8'(KEY0);

    // ------------------------------------------------------------ lockstep references
    wire        k_busy, k_done, k_wr_en;
    wire [5:0]  k_rd_addr, k_wr_addr;
    wire [63:0] k_wr_data;
    qsag_keccak_serial u_kref (
        .clk(clk), .rst_n(srst_n_o), .srst_n(srst_n_o), .start(dut.kec_start), .turbo(dut.kec_turbo), .fault_inj(1'b0),
        .busy(k_busy), .done(k_done), .rd_addr(k_rd_addr), .port(dut.rf_rdata),
        .wr_en(k_wr_en), .wr_addr(k_wr_addr), .wr_data(k_wr_data)
    );
    wire        a_stb, a_done, a_busy, a_cs_n, a_sck, a_mosi;
    wire [63:0] a_rx;
    qsag_anchor_spi u_aref (
        .clk(clk), .rst_n(dut.u_fm.a_rst_n), .div(FRAM_DIV), .start(dut.u_fm.s_start), .write(dut.u_fm.s_write),
        .addr({10'd0, dut.u_fm.s_slot, 5'd0}), .stb(a_stb), .go(dut.u_fm.go), .rx(a_rx), .tx(dut.u_fm.tx),
        .done(a_done), .busy(a_busy), .cs_n(a_cs_n), .sck(a_sck), .mosi(a_mosi), .miso(fram_miso)
    );
    wire k_bad = {k_busy, k_done, k_wr_en, k_rd_addr} != {dut.kec_busy, dut.kec_done, dut.kec_wr_en, dut.kec_rd_addr}
               || (k_wr_en && {k_wr_addr, k_wr_data} != {dut.kec_wr_addr, dut.kec_wr_data});
    wire a_bad = {a_stb, a_done, a_busy, a_cs_n, a_sck, a_mosi, a_rx}
               != {dut.u_fm.a_stb, dut.u_fm.a_done, dut.u_fm.a_busy, fram_cs_n, fram_sck, fram_mosi, dut.u_fm.a_rx};
    initial lock_err = 1'b0;
    always_ff @(posedge clk) if (srst_n_o && (k_bad || a_bad)) begin
        if (!lock_err) $display("LOCKSTEP mismatch: keccak %0d anchor %0d", k_bad, a_bad);
        lock_err <= 1'b1;
    end

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, puf_req, busy, rst_n_o, bd_rf_we, bd_row, bd_data, bd_fl_we, bd_flags, bd_nonce};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire
