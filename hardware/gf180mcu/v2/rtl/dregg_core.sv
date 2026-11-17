// Dregg-180 v2 core: register file, word unit, Keccak unit, framer, egress, FRAM port, sequencer and
// reset control. The microcode ROM and the host link are outside (dregg_top adds the generated ROM and
// the SPI link; the co-simulation bench adds a loadable ROM and a word-level link).
//
// Word-level link:  in_valid / in_first / in_data / in_take   request words (in_first: first of a frame)
//                   out_valid / out_data / out_take            response words
`default_nettype none

module dregg_core #(
    parameter bit H_SHADOW = 1'b1,              // see dregg_seq
    parameter bit KEC_WAIT_AFTER_STORE = 1'b1,  // see dregg_seq
    parameter bit FRAM_DONE_PAD = 1'b1          // see dregg_fram
) (
    input  wire         clk,
    input  wire         por_n,
    input  wire         tamper_n,
    // link
    input  wire         in_valid,
    input  wire         in_first,
    input  wire  [63:0] in_data,
    output wire         in_take,
    output wire         out_valid,
    output wire  [63:0] out_data,
    input  wire         out_take,
    // microcode ROM
    output wire  [10:0] rom_addr,
    input  wire  [27:0] rom_word,
    output wire  [6:0]  const_idx,
    input  wire  [63:0] const_data,
    input  wire         const_ok,
    output wire  [7:0]  disp_op,
    input  wire         disp_hit,
    input  wire  [10:0] disp_addr,
    input  wire  [1:0]  disp_class,
    input  wire  [11:0] rom_len,
    input  wire  [11:0] rom_used,
    // FRAM pads
    output wire         fram_cs_n,
    output wire         fram_sck,
    output wire         fram_mosi,
    input  wire         fram_miso,
    // stage 3 and 4 interfaces (dregg_seq)
    input  wire         puf_present,
    output wire         puf_req,
    output wire  [1:0]  puf_idx,
    input  wire         puf_valid,
    input  wire  [63:0] puf_data,
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
    // pins
    output wire         verify_ok,
    output wire         fault,
    output wire         ready,
    output wire         busy,
    output wire         rst_n_o,      // synchronised pad reset (for the link)
    output wire         srst_n_o,
    // observation
    output wire         cmd_active,
    output wire         link_wait,
    output wire         stall,
    output wire         fault_now,
    output wire  [5:0]  fault_why,
    output wire  [10:0] pc
);
    wire rst_n, srst_n, fault_control, tampered;
    wire fault_mac, fault_anchor;
    dregg_rst u_rst (.clk(clk), .por_n(por_n), .tamper_n(tamper_n), .zreq(fault_now), .rst_n(rst_n), .srst_n(srst_n),
                     .fault_control(fault_control), .tampered(tampered));
    assign rst_n_o  = rst_n;
    assign srst_n_o = srst_n;
    assign fault    = fault_mac | fault_anchor | fault_control | tampered;

    // ------------------------------------------------------------ register file
    wire         h_en, rf_we;
    wire [63:0]  h_d, h_q, rf_rdata;
    wire [6:0]   rf_waddr, rf_raddr;
    wire [1:0]   rf_out_we;
    wire [3:0]   rf_wipe;
    wire [6:0]   kw_we;
    wire [319:0] kc_d;
    wire [63:0]  kb_d;
    wire [447:0] kw_q;
    wire [127:0] out_q;
    wire [71:0]  wl_en;
    dregg_regfile u_rf (
        .clk(clk), .srst_n(srst_n), .h_en(h_en), .h_d(h_d), .h_q(h_q),
        .we(rf_we), .waddr(rf_waddr), .out_we(rf_out_we), .wipe(rf_wipe),
        .kw_we(kw_we), .kc_d(kc_d), .kb_d(kb_d), .kw_q(kw_q),
        .raddr(rf_raddr), .rdata(rf_rdata), .out_q(out_q), .wl_en_o(wl_en)
    );

    // ------------------------------------------------------------ word unit
    wire [63:0] wu_h, wu_x, wu_y;
    wire [4:0]  wu_op;
    wire [6:0]  wu_un;
    wire        wu_cy, wu_ne, wu_un_ok;
    dregg_word_unit u_wu (.h(wu_h), .x(wu_x), .op(wu_op), .un(wu_un), .y(wu_y), .cy(wu_cy), .ne(wu_ne), .un_ok(wu_un_ok));

    // ------------------------------------------------------------ Keccak unit
    wire        kec_start, kec_turbo, kec_busy, kec_done, kec_last, kec_wr_en;
    wire [5:0]  kec_rd_addr, kec_wr_addr;
    wire [63:0] kec_wr_data;
    dregg_keccak_serial u_kec (
        .clk(clk), .rst_n(srst_n), .srst_n(srst_n), .start(kec_start), .turbo(kec_turbo), .fault_inj(1'b0),
        .busy(kec_busy), .done(kec_done), .rd_addr(kec_rd_addr), .port(rf_rdata),
        .wr_en(kec_wr_en), .wr_addr(kec_wr_addr), .wr_data(kec_wr_data),
        .kw_we(kw_we), .kc_d(kc_d), .kb_d(kb_d), .kw_q(kw_q), .last(kec_last)
    );

    // ------------------------------------------------------------ framer
    wire        fr_idle, fr_hdr_valid, fr_take_hdr, fr_take_din, fr_drain, fr_din_valid, fr_drained, fr_rem_lt2;
    wire        fr_in_magic_ok;
    wire [7:0]  fr_in_op;
    wire [63:0] fr_din, fr_hdr;
    wire [21:0] fr_remaining;
    dregg_framer u_fr (
        .clk(clk), .srst_n(srst_n), .in_valid(in_valid), .in_first(in_first), .in_data(in_data), .in_take(in_take),
        .idle(fr_idle), .hdr_valid(fr_hdr_valid), .take_hdr(fr_take_hdr), .take_din(fr_take_din), .drain(fr_drain),
        .din_valid(fr_din_valid), .din(fr_din), .drained(fr_drained), .rem_lt2(fr_rem_lt2),
        .in_magic_ok(fr_in_magic_ok), .in_op(fr_in_op), .hdr(fr_hdr), .remaining(fr_remaining)
    );

    // ------------------------------------------------------------ egress
    wire        eg_hdr, eg_fail, eg_ok, eg_push, eg_can_push, eg_wr_slot, eg_push_room, eg_flush, eg_flushed, eg_idle;
    wire [15:0] eg_n;
    wire [1:0]  eg_sel;
    dregg_egress u_eg (
        .clk(clk), .srst_n(srst_n), .req_op(fr_hdr[15:8]), .hdr(eg_hdr), .fail(eg_fail), .hdr_n(eg_n), .hdr_ok(eg_ok),
        .push(eg_push), .can_push(eg_can_push), .wr_slot(eg_wr_slot), .push_room(eg_push_room),
        .flush(eg_flush), .flushed(eg_flushed), .idle(eg_idle), .out_q(out_q),
        .out_valid(out_valid), .out_data(out_data), .out_take(out_take), .out_sel(eg_sel)
    );

    // ------------------------------------------------------------ FRAM port
    wire        fm_start, fm_write, fm_slot, fm_rword, fm_wword, fm_done, fm_abort, fm_fin, fm_open, fm_writing;
    wire [63:0] fm_rx;
    wire [1:0]  fm_left;
    dregg_fram #(.DONE_PAD(FRAM_DONE_PAD)) u_fm (
        .clk(clk), .srst_n(srst_n), .abort(fm_abort), .s_start(fm_start), .s_write(fm_write), .s_slot(fm_slot),
        .s_rword(fm_rword), .s_wword(fm_wword), .s_done(fm_done), .tx(rf_rdata), .rx(fm_rx), .fin(fm_fin),
        .open(fm_open), .writing(fm_writing), .left(fm_left),
        .cs_n(fram_cs_n), .sck(fram_sck), .mosi(fram_mosi), .miso(fram_miso)
    );

    // ------------------------------------------------------------ sequencer
    wire rd_used, key_wr, key_wr_boot;
    dregg_seq #(.H_SHADOW(H_SHADOW), .KEC_WAIT_AFTER_STORE(KEC_WAIT_AFTER_STORE)) u_seq (
        .clk(clk), .srst_n(srst_n),
        .rom_addr(rom_addr), .rom_word(rom_word), .const_idx(const_idx), .const_data(const_data), .const_ok(const_ok),
        .disp_op(disp_op), .disp_hit(disp_hit), .disp_addr(disp_addr), .disp_class(disp_class),
        .rom_len(rom_len), .rom_used(rom_used),
        .h_en(h_en), .h_d(h_d), .h_q(h_q), .rf_we(rf_we), .rf_waddr(rf_waddr), .rf_out_we(rf_out_we),
        .rf_wipe(rf_wipe), .rf_raddr(rf_raddr), .rf_rdata(rf_rdata),
        .wu_h(wu_h), .wu_x(wu_x), .wu_op(wu_op), .wu_un(wu_un), .wu_y(wu_y), .wu_cy(wu_cy), .wu_ne(wu_ne),
        .wu_un_ok(wu_un_ok),
        .kec_start(kec_start), .kec_turbo(kec_turbo), .kec_last(kec_last), .kec_rd_addr(kec_rd_addr),
        .kec_wr_en(kec_wr_en), .kec_wr_addr(kec_wr_addr), .kec_wr_data(kec_wr_data),
        .fr_idle(fr_idle), .fr_hdr_valid(fr_hdr_valid), .fr_take_hdr(fr_take_hdr), .fr_take_din(fr_take_din),
        .fr_drain(fr_drain), .fr_din_valid(fr_din_valid), .fr_din(fr_din), .fr_drained(fr_drained),
        .fr_rem_lt2(fr_rem_lt2), .fr_in_magic_ok(fr_in_magic_ok), .fr_in_op(fr_in_op), .fr_hdr(fr_hdr),
        .fr_remaining(fr_remaining),
        .eg_hdr(eg_hdr), .eg_fail(eg_fail), .eg_n(eg_n), .eg_ok(eg_ok), .eg_push(eg_push), .eg_can_push(eg_can_push),
        .eg_wr_slot(eg_wr_slot), .eg_push_room(eg_push_room), .eg_flush(eg_flush), .eg_flushed(eg_flushed),
        .eg_idle(eg_idle),
        .fm_start(fm_start), .fm_write(fm_write), .fm_slot(fm_slot), .fm_rword(fm_rword), .fm_wword(fm_wword),
        .fm_done(fm_done), .fm_abort(fm_abort), .fm_rx(fm_rx), .fm_fin(fm_fin), .fm_open(fm_open),
        .fm_writing(fm_writing), .fm_left(fm_left),
        .puf_present(puf_present), .puf_req(puf_req), .puf_idx(puf_idx), .puf_valid(puf_valid), .puf_data(puf_data),
        .ent_present(ent_present), .ent_req(ent_req), .ent_valid(ent_valid), .ent_data(ent_data),
        .own_start(own_start), .own_valid(own_valid), .own_idx(own_idx), .own_data(own_data), .own_done(own_done),
        .own_ok(own_ok),
        .fault_now(fault_now), .fault_why(fault_why), .verify_ok(verify_ok), .fault_mac(fault_mac),
        .fault_anchor(fault_anchor), .ready(ready), .busy(busy),
        .cmd_active(cmd_active), .link_wait(link_wait), .stall(stall), .pc_o(pc), .rd_used(rd_used),
        .key_wr(key_wr), .key_wr_boot(key_wr_boot)
    );

`ifndef SYNTHESIS
    // ------------------------------------------------------------ assertions (checked in every simulation)
    `include "dregg_defs.svh"
    logic [71:0] open_q;        // rows transparent in this clock
    logic        push_q, pushh_q;
    logic [6:0]  rsrc_q;
    always_ff @(posedge clk or negedge srst_n)
        if (!srst_n) begin
            open_q  <= '0;
            push_q  <= 1'b0;
            pushh_q <= 1'b0;
            rsrc_q  <= '0;
        end else begin
            open_q  <= wl_en;
            push_q  <= |rf_out_we;
            pushh_q <= (|rf_out_we) && (rom_word[27:23] == OP_PUSH) && rom_word[6];
            rsrc_q  <= rf_raddr;
        end
    wire a_rd_key = rd_used && (rf_raddr >= 7'(KEY0)) && (rf_raddr < 7'(KEY0 + N_KEYS));
    // A failed check prints once and counts; the bench fails the run if the count is not zero.
    /* verilator lint_off MULTIDRIVEN */
    int unsigned assert_count;
    initial assert_count = 0;
    /* verilator lint_on MULTIDRIVEN */
`define DREGG_CHECK(ok, text) \
        if (!(ok)) begin \
            assert_count <= assert_count + 1; \
            if (assert_count < 20) $display("ASSERT FAILED: %s (pc %0d, row %0d)", text, pc, rf_raddr); \
        end
    always_ff @(posedge clk) if (srst_n) begin
        // 8.2 (6): a row is never read while transparent
        `DREGG_CHECK(!(rd_used && rf_raddr < 7'd72 && open_q[rf_raddr]), "row read while transparent")
        // key rows are read only by the first clock of KMOV
        `DREGG_CHECK(!(a_rd_key && !(rom_word[27:23] == OP_KMOV && !kec_busy)), "key row read by a non-KMOV instruction")
        // 8.2 (3): a key row is written only by the boot interface or by KEYWR inside the key range
        `DREGG_CHECK(!(key_wr && !key_wr_boot && !(rom_word[27:23] == OP_KEYWR && pc >= KEY_LO && pc <= KEY_HI)),
                     "key row written outside the key range")
        // key rows never drive the FRAM data: a FRAM word is taken only from the three record rows
        `DREGG_CHECK(!(fm_wword && !(rf_raddr == FRAM_SRC0 || rf_raddr == FRAM_SRC1 || rf_raddr == FRAM_SRC2)),
                     "FRAM WWORD sends a row outside the record rows")
        // key rows never drive the egress: an out row opens only on a PUSH, and the row that went through
        // the hold register for it is not a key row
        `DREGG_CHECK(!((|rf_out_we) && rom_word[27:23] != OP_PUSH), "out row opened by a non-PUSH instruction")
        `DREGG_CHECK(!((|rf_out_we) && !rom_word[6] && a_rd_key), "PUSH of a key row")
        // 8.2 (1): a data word reaches the link only from an out row
        `DREGG_CHECK(!(out_valid && out_take && (eg_sel == 2'd1) && out_data !== out_q[63:0]), "egress word is not out row 0")
        `DREGG_CHECK(!(out_valid && out_take && (eg_sel == 2'd2) && out_data !== out_q[127:64]), "egress word is not out row 1")
        `DREGG_CHECK(!(out_valid && out_take && (eg_sel == 2'd3) && out_data !== 64'd0), "padding word is not zero")
        // the sequencer cannot leave the ROM
        `DREGG_CHECK(!(ready && !fault_now && {1'b0, pc} >= rom_len), "micro-PC outside the ROM without a fault")
        // the Keccak unit addresses lanes only (assumed by the formal proof of the sequencer)
        `DREGG_CHECK(!(kec_busy && ((kec_rd_addr >= 6'd25) || (kec_wr_en && (kec_wr_addr >= 6'd25)))),
                     "Keccak unit address outside the lanes")
        // an out row is never offered to the link while transparent
        `DREGG_CHECK(!(out_valid && (eg_sel == 2'd1) && open_q[OUT0]), "out row 0 offered while transparent")
        `DREGG_CHECK(!(out_valid && (eg_sel == 2'd2) && open_q[OUT0 + 1]), "out row 1 offered while transparent")
    end
`undef DREGG_CHECK
    wire unused_a = &{1'b0, push_q, pushh_q, rsrc_q, kec_done};
`else
    wire unused_s = &{1'b0, wl_en, rd_used, key_wr, key_wr_boot, eg_sel, kec_busy, kec_done};
`endif
endmodule
`default_nettype wire
