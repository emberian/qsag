// Full-chip testbench top: chip_core with the pad-ring signals exposed, plus the internal
// core clock for the runt-pulse monitor.
`default_nettype none
`timescale 1ps / 1ps
module tb_top (
    input  wire        clk,
    input  wire        rst_n,
    input  wire [3:0]  input_in,
    output wire [3:0]  input_pu,
    output wire [3:0]  input_pd,
    input  wire [37:0] bidir_in,
    output wire [37:0] bidir_out,
    output wire [37:0] bidir_oe,
    output wire [37:0] bidir_cs,
    output wire [37:0] bidir_sl,
    output wire [37:0] bidir_ie,
    output wire [37:0] bidir_pu,
    output wire [37:0] bidir_pd,
    output wire        clk_core_mon
);
    wire [3:0] analog;
    chip_core #(.NUM_INPUT_PADS(4), .NUM_BIDIR_PADS(38), .NUM_ANALOG_PADS(4)) dut (
        .clk(clk), .rst_n(rst_n),
        .input_in(input_in), .input_pu(input_pu), .input_pd(input_pd),
        .bidir_in(bidir_in), .bidir_out(bidir_out), .bidir_oe(bidir_oe), .bidir_cs(bidir_cs),
        .bidir_sl(bidir_sl), .bidir_ie(bidir_ie), .bidir_pu(bidir_pu), .bidir_pd(bidir_pd),
        .analog(analog)
    );
    assign clk_core_mon = dut.clk_core;
endmodule
`default_nettype wire
