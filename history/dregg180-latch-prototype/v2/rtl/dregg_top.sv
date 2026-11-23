// Dregg-180 v2, configuration S, stage 2 top level: dregg_core with the generated microcode ROM
// (dregg_urom, from the model's assembler) and the SPI host link.
//
// Pads: clock, reset, SPI 4, IRQ, FAULT, VERIFY_OK, FRAM SPI 4, tamper.
// The stage 3 and 4 organs do not exist yet. Their interfaces to the sequencer are ports of this module
// (puf_*: device secret at boot; ent_*: conditioned nonce; own_*: owner authorisation), so a bench or
// the organs can be attached without touching the core. Tied off (puf_present = 0), the chip answers
// diagnostics and hashing and refuses provisioning, as the model does without those interfaces.
`default_nettype none

module dregg_top #(
    parameter bit IR_STAGE = 1'b0,              // see dregg_seq
    parameter bit RA_STAGE = 1'b0
) (
    input  wire         clk,
    input  wire         por_n,
    input  wire         tamper_n,
    // SPI host link
    input  wire         spi_sck,
    input  wire         spi_cs_n,
    input  wire         spi_mosi,
    output wire         spi_miso,
    output wire         spi_miso_oe,
    output wire         irq,
    // status pins
    output wire         fault,
    output wire         verify_ok,
    // FRAM
    output wire         fram_cs_n,
    output wire         fram_sck,
    output wire         fram_mosi,
    input  wire         fram_miso,
    // stage 3 and 4 interfaces
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
    input  wire         own_ok
);
    wire        in_valid, in_first, in_take, out_valid, out_take;
    wire [63:0] in_data, out_data;
    wire [10:0] rom_addr, disp_addr, pc;
    wire [27:0] rom_word;
    wire [6:0]  const_idx;
    wire [63:0] const_data;
    wire        const_ok, disp_hit;
    wire [7:0]  disp_op;
    wire [1:0]  disp_class;
    wire [11:0] rom_len, rom_used;
    wire        ready, busy, rst_n, srst_n, cmd_active, link_wait, stall, fault_now;
    wire [5:0]  fault_why;

    dregg_urom u_rom (
        .rom_addr(rom_addr), .rom_word(rom_word), .const_idx(const_idx), .const_data(const_data), .const_ok(const_ok),
        .disp_op(disp_op), .disp_hit(disp_hit), .disp_addr(disp_addr), .disp_class(disp_class),
        .rom_len(rom_len), .rom_used(rom_used)
    );

    dregg_core #(.IR_STAGE(IR_STAGE), .RA_STAGE(RA_STAGE)) u_core (
        .clk(clk), .por_n(por_n), .tamper_n(tamper_n),
        .in_valid(in_valid), .in_first(in_first), .in_data(in_data), .in_take(in_take),
        .out_valid(out_valid), .out_data(out_data), .out_take(out_take),
        .rom_addr(rom_addr), .rom_word(rom_word), .const_idx(const_idx), .const_data(const_data), .const_ok(const_ok),
        .disp_op(disp_op), .disp_hit(disp_hit), .disp_addr(disp_addr), .disp_class(disp_class),
        .rom_len(rom_len), .rom_used(rom_used),
        .fram_cs_n(fram_cs_n), .fram_sck(fram_sck), .fram_mosi(fram_mosi), .fram_miso(fram_miso),
        .puf_present(puf_present), .puf_req(puf_req), .puf_idx(puf_idx), .puf_valid(puf_valid), .puf_data(puf_data),
        .ent_present(ent_present), .ent_req(ent_req), .ent_valid(ent_valid), .ent_data(ent_data),
        .own_start(own_start), .own_valid(own_valid), .own_idx(own_idx), .own_data(own_data),
        .own_done(own_done), .own_ok(own_ok),
        .verify_ok(verify_ok), .fault(fault), .ready(ready), .busy(busy), .rst_n_o(rst_n), .srst_n_o(srst_n),
        .cmd_active(cmd_active), .link_wait(link_wait), .stall(stall), .fault_now(fault_now), .fault_why(fault_why),
        .pc(pc)
    );

    dregg_spi_link u_link (
        .clk(clk), .rst_n(rst_n), .por_n(por_n),
        .sck(spi_sck), .cs_n(spi_cs_n), .mosi(spi_mosi), .miso(spi_miso), .miso_oe(spi_miso_oe), .irq(irq),
        .in_valid(in_valid), .in_first(in_first), .in_data(in_data), .in_take(in_take),
        .out_valid(out_valid), .out_data(out_data), .out_take(out_take),
        .busy(busy), .fault(fault), .verify_ok(verify_ok), .ready(ready)
    );

    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, srst_n, cmd_active, link_wait, stall, fault_now, fault_why, pc};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire
