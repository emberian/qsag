// Formal harness for dregg_seq (with dregg_rules): every input is free, so the properties in dregg_seq
// (ifdef FORMAL) are checked for every ROM content, every data value and every unit behaviour.
// The ROM word is free but stable while the address is unchanged. One further assumption: the Keccak unit addresses rows 0..24 (lane_addr in the unit is 5 * row + x; the
// simulation checks it on the real unit, dregg_core "Keccak unit address outside the lanes").
`default_nettype none
module fv_seq (
    input wire clk,
    input wire [27:0] rom_word, input wire [63:0] const_data, input wire const_ok, input wire disp_hit,
    input wire [10:0] disp_addr, input wire [1:0] disp_class, input wire [11:0] rom_used,
    input wire [63:0] h_q, input wire [63:0] rf_rdata, input wire [63:0] wu_y, input wire wu_cy, input wire wu_ne,
    input wire wu_un_ok, input wire kec_last, input wire [5:0] kec_rd_addr, input wire kec_wr_en,
    input wire [5:0] kec_wr_addr, input wire [63:0] kec_wr_data, input wire fr_hdr_valid, input wire fr_din_valid,
    input wire [63:0] fr_din, input wire fr_drained, input wire fr_rem_lt2, input wire fr_in_magic_ok,
    input wire [7:0] fr_in_op, input wire [63:0] fr_hdr, input wire [21:0] fr_remaining, input wire eg_can_push,
    input wire eg_wr_slot, input wire eg_push_room, input wire eg_flushed, input wire eg_idle, input wire [63:0] fm_rx,
    input wire fm_fin, input wire fm_open, input wire fm_writing, input wire [1:0] fm_left, input wire puf_present,
    input wire puf_valid, input wire [63:0] puf_data, input wire ent_present, input wire ent_valid,
    input wire [127:0] ent_data, input wire own_done, input wire own_ok
);
    (* anyconst *) wire [11:0] rom_len;         // the image length: any value, constant over time
    logic init = 1'b1;
    always_ff @(posedge clk) init <= 1'b0;
    wire srst_n = !init;
    always_comb begin
        assume (kec_rd_addr < 6'd25);
        assume (kec_wr_addr < 6'd25);
    end
    // the ROM is a function of the address: while the address does not change, neither does the word
    wire [10:0] rom_addr;
    logic [10:0] addr_q;
    logic [27:0] word_q;
    always_ff @(posedge clk) begin
        addr_q <= rom_addr;
        word_q <= rom_word;
        if (!init && addr_q == rom_addr) assume (rom_word == word_q);

    end
    /* verilator lint_off PINCONNECTEMPTY */
    dregg_seq dut (
        .clk(clk), .srst_n(srst_n), .rom_addr(rom_addr), .rom_word(rom_word), .const_idx(), .const_data(const_data),
        .const_ok(const_ok), .disp_op(), .disp_hit(disp_hit), .disp_addr(disp_addr), .disp_class(disp_class),
        .rom_len(rom_len), .rom_used(rom_used), .h_en(), .h_d(), .h_q(h_q), .rf_we(), .rf_waddr(), .rf_out_we(),
        .rf_wipe(), .rf_raddr(), .rf_rdata(rf_rdata), .wu_h(), .wu_x(), .wu_op(), .wu_un(), .wu_y(wu_y), .wu_cy(wu_cy),
        .wu_ne(wu_ne), .wu_un_ok(wu_un_ok), .kec_start(), .kec_turbo(), .kec_last(kec_last), .kec_rd_addr(kec_rd_addr),
        .kec_wr_en(kec_wr_en), .kec_wr_addr(kec_wr_addr), .kec_wr_data(kec_wr_data), .fr_idle(),
        .fr_hdr_valid(fr_hdr_valid), .fr_take_hdr(), .fr_take_din(), .fr_drain(), .fr_din_valid(fr_din_valid),
        .fr_din(fr_din), .fr_drained(fr_drained), .fr_rem_lt2(fr_rem_lt2), .fr_in_magic_ok(fr_in_magic_ok),
        .fr_in_op(fr_in_op), .fr_hdr(fr_hdr), .fr_remaining(fr_remaining), .eg_hdr(), .eg_fail(), .eg_n(), .eg_ok(),
        .eg_push(), .eg_can_push(eg_can_push), .eg_wr_slot(eg_wr_slot), .eg_push_room(eg_push_room), .eg_flush(),
        .eg_flushed(eg_flushed), .eg_idle(eg_idle), .fm_start(), .fm_write(), .fm_slot(), .fm_rword(), .fm_wword(),
        .fm_done(), .fm_abort(), .fm_rx(fm_rx), .fm_fin(fm_fin), .fm_open(fm_open), .fm_writing(fm_writing),
        .fm_left(fm_left), .puf_present(puf_present), .puf_req(), .puf_idx(), .puf_valid(puf_valid),
        .puf_data(puf_data), .ent_present(ent_present), .ent_req(), .ent_valid(ent_valid), .ent_data(ent_data),
        .own_start(), .own_valid(), .own_idx(), .own_data(), .own_done(own_done), .own_ok(own_ok), .fault_now(),
        .fault_why(), .verify_ok(), .fault_mac(), .fault_anchor(), .ready(), .busy(), .cmd_active(), .link_wait(),
        .stall(), .pc_o(), .rd_used(), .key_wr(), .key_wr_boot()
    );
endmodule
`default_nettype wire
