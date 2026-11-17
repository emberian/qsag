// Chip-level bench top: dregg_top (generated ROM, SPI link) with the interface stand-ins and taps.
`default_nettype none
module dregg_chip_tb (
    input  wire         clk,
    input  wire         por_n,
    input  wire         tamper_n,
    input  wire         spi_sck,
    input  wire         spi_cs_n,
    input  wire         spi_mosi,
    output wire         spi_miso,
    output wire         spi_miso_oe,
    output wire         irq,
    output wire         fault,
    output wire         verify_ok,
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
    output wire         ready,
    output wire         cmd_active,
    output wire         link_wait,
    output wire         fault_now,
    output wire  [31:0] assert_count
);
    wire       puf_req;
    wire [1:0] puf_idx;
    dregg_top dut (
        .clk(clk), .por_n(por_n), .tamper_n(tamper_n),
        .spi_sck(spi_sck), .spi_cs_n(spi_cs_n), .spi_mosi(spi_mosi), .spi_miso(spi_miso), .spi_miso_oe(spi_miso_oe),
        .irq(irq), .fault(fault), .verify_ok(verify_ok),
        .fram_cs_n(fram_cs_n), .fram_sck(fram_sck), .fram_mosi(fram_mosi), .fram_miso(fram_miso),
        .puf_present(puf_present), .puf_req(puf_req), .puf_idx(puf_idx), .puf_valid(1'b1),
        .puf_data(puf_secret[64*puf_idx +: 64]),
        .ent_present(ent_present), .ent_req(ent_req), .ent_valid(ent_valid), .ent_data(ent_data),
        .own_start(own_start), .own_valid(own_valid), .own_idx(own_idx), .own_data(own_data),
        .own_done(own_done), .own_ok(own_ok)
    );
    assign ready        = dut.ready;
    assign cmd_active   = dut.cmd_active;
    assign link_wait    = dut.link_wait;
    assign fault_now    = dut.fault_now;
    assign assert_count = dut.u_core.assert_count;
    /* verilator lint_off UNUSEDSIGNAL */
    wire unused = &{1'b0, puf_req};
    /* verilator lint_on UNUSEDSIGNAL */
endmodule
`default_nettype wire
