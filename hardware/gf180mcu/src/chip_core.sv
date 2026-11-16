// SPDX-License-Identifier: Apache-2.0
// QSAG-NI-180 chip core for wafer.space GF180MCU Run 3, SLOT_0P5X0P5.
// Port signature identical to wafer-space/gf180mcu-project-template `chip_core`.
//
//   inputs[0]   EXT_CLK_BYPASS (pull-up: 1 = clk_pad is the core clock)
//   inputs[2:1] IO_MODE        (pull-down: 00 = SPI)
//   inputs[3]   CS_N           (pull-up)
// The bidir pad map is in rtl/qsag_io_shell.sv and README.md.

`default_nettype none

module chip_core #(
    parameter NUM_INPUT_PADS  = 4,
    parameter NUM_BIDIR_PADS  = 38,
    parameter NUM_ANALOG_PADS = 4
    )(
    `ifdef USE_POWER_PINS
    inout  wire VDD,
    inout  wire VSS,
    `endif

    input  wire clk,       // clk_pad
    input  wire rst_n,     // rst_n_pad (active low, asynchronous)

    input  wire [NUM_INPUT_PADS-1:0] input_in,   // Input value
    output wire [NUM_INPUT_PADS-1:0] input_pu,   // Pull-up
    output wire [NUM_INPUT_PADS-1:0] input_pd,   // Pull-down

    input  wire [NUM_BIDIR_PADS-1:0] bidir_in,   // Input value
    output wire [NUM_BIDIR_PADS-1:0] bidir_out,  // Output value
    output wire [NUM_BIDIR_PADS-1:0] bidir_oe,   // Output enable
    output wire [NUM_BIDIR_PADS-1:0] bidir_cs,   // Input type (0=CMOS Buffer, 1=Schmitt Trigger)
    output wire [NUM_BIDIR_PADS-1:0] bidir_sl,   // Slew rate (0=fast, 1=slow)
    output wire [NUM_BIDIR_PADS-1:0] bidir_ie,   // Input enable
    output wire [NUM_BIDIR_PADS-1:0] bidir_pu,   // Pull-up
    output wire [NUM_BIDIR_PADS-1:0] bidir_pd,   // Pull-down

    inout  wire [NUM_ANALOG_PADS-1:0] analog  // Analog (unused)
);
    localparam logic [31:0] HW_REV = 32'h0180_0001;

    wire        bypass  = input_in[0];
    wire [1:0]  io_mode = input_in[2:1];
    wire        cs_n    = input_in[3];
    assign input_pu = 4'b1001;
    assign input_pd = 4'b0110;

    wire        clk_core, rst_core_n, srst_n, zeroize, fault_glitch, fault_tamper, clk_mon;
    wire [31:0] clk_tel;
    wire [63:0] csr;
    wire        tamper_n;

    wire        trng_take, trng_valid, trng_ok, rct_fail, apt_fail, trng_bit;
    wire [63:0] trng_word;

    wire        an_start, an_write, an_stb, an_go, an_done, an_busy;
    wire [15:0] an_addr;
    wire [63:0] an_rx, an_tx;
    wire        an_cs_n, an_sck, an_mosi, an_miso;

    wire        in_valid, in_pop, out_ready, out_push;
    wire [63:0] in_data, out_data;
    wire        verify_ok, key_valid, fault_anchor, fault_mac, fault_control, eng_busy, rx_overrun, tx_underrun;

    qsag_gals_clk_rst u_clk (
        .clk_pad(clk), .rst_n_pad(rst_n), .bypass(bypass), .tamper_n(tamper_n), .csr(csr),
        .trng_bit(trng_bit), .clk_core(clk_core), .rst_core_n(rst_core_n), .srst_n(srst_n),
        .zeroize(zeroize), .fault_glitch(fault_glitch), .fault_tamper(fault_tamper),
        .clk_mon(clk_mon), .tel(clk_tel)
    );

    qsag_trng u_trng (
        .clk(clk_core), .rst_n(rst_core_n), .en(csr[25]), .take(trng_take), .word(trng_word),
        .valid(trng_valid), .ok(trng_ok), .rct_fail(rct_fail), .apt_fail(apt_fail), .raw_bit(trng_bit)
    );

    qsag_anchor_spi u_anchor (
        .clk(clk_core), .rst_n(rst_core_n), .div(csr[24:21]), .start(an_start), .write(an_write),
        .addr(an_addr), .stb(an_stb), .go(an_go), .rx(an_rx), .tx(an_tx), .done(an_done),
        .busy(an_busy), .cs_n(an_cs_n), .sck(an_sck), .mosi(an_mosi), .miso(an_miso)
    );

    wire fault = fault_glitch | fault_tamper | fault_anchor | fault_mac | rct_fail | apt_fail
               | rx_overrun | tx_underrun | fault_control;
    wire [63:0] tel0 = {HW_REV[31:16], 4'd0, eng_busy, key_valid, io_mode, bypass, rx_overrun, tx_underrun,
                        trng_ok, apt_fail, rct_fail, fault_tamper, fault_glitch, clk_tel};

    qsag_wire_engine u_engine (
        .clk(clk_core), .rst_n(rst_core_n), .srst_n(srst_n), .zeroize(zeroize),
        .in_valid(in_valid), .in_data(in_data), .in_pop(in_pop),
        .out_ready(out_ready), .out_data(out_data), .out_push(out_push),
        .an_start(an_start), .an_write(an_write), .an_addr(an_addr), .an_stb(an_stb), .an_go(an_go),
        .an_rx(an_rx), .an_tx(an_tx), .an_done(an_done),
        .trng_valid(trng_valid), .trng_word(trng_word), .trng_ok(trng_ok), .trng_take(trng_take),
        .tel0(tel0), .tel1({HW_REV[15:0], 16'd0}), .csr(csr),
        .verify_ok(verify_ok), .key_valid_o(key_valid), .fault_anchor(fault_anchor),
        .fault_mac(fault_mac), .fault_control(fault_control), .busy(eng_busy)
    );

    qsag_io_shell u_io (
        .clk_core(clk_core), .rst_core_n(rst_core_n), .arst_n(rst_n), .io_mode(io_mode), .cs_n(cs_n),
        .bidir_in(bidir_in), .bidir_out(bidir_out), .bidir_oe(bidir_oe), .bidir_cs(bidir_cs),
        .bidir_pu(bidir_pu), .bidir_pd(bidir_pd),
        .in_valid(in_valid), .in_data(in_data), .in_pop(in_pop),
        .out_ready(out_ready), .out_data(out_data), .out_push(out_push),
        .verify_ok(verify_ok), .fault(fault), .busy(eng_busy), .clk_mon(clk_mon),
        .an_cs_n(an_cs_n), .an_sck(an_sck), .an_mosi(an_mosi), .an_miso(an_miso),
        .tamper_n(tamper_n), .rx_overrun(rx_overrun), .tx_underrun(tx_underrun)
    );

    assign bidir_sl = {NUM_BIDIR_PADS{csr[19]}};
    assign bidir_ie = ~bidir_oe;

    wire unused = &{1'b0, an_busy};
endmodule

`default_nettype wire
