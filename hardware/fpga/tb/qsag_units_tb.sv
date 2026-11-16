// Simulation harness: every QSAG-NI unit side by side, driven by tb/sim_qsag_ni_fpga.cpp.
module qsag_units_tb (
    input  logic          clk,
    input  logic          rst,
    // Goldilocks multiplier, both tilings
    input  logic [63:0]   mul_a,
    input  logic [63:0]   mul_b,
    output logic [63:0]   mul_r,
    output logic [63:0]   mul_r16,
    // wide reducer
    input  logic [135:0]  red_x,
    output logic [63:0]   red_r,
    // S-box
    input  logic [63:0]   sb_x,
    output logic [63:0]   sb_y,
    // Ext4 MAC
    input  logic [255:0]  e_a,
    input  logic [255:0]  e_b,
    input  logic [255:0]  e_c,
    output logic [255:0]  e_y,
    // Poseidon2 ring core
    input  logic          ring_in_valid,
    output logic          ring_in_ready,
    input  logic [767:0]  ring_in_state,
    input  logic          ring_in_jive,
    input  logic [15:0]   ring_in_tag,
    output logic          ring_out_valid,
    output logic [767:0]  ring_out_state,
    output logic          ring_out_jive,
    output logic [15:0]   ring_out_tag,
    output logic          ring_busy,
    // Poseidon2 pipelined core
    input  logic          pipe_in_valid,
    input  logic [767:0]  pipe_in_state,
    input  logic          pipe_in_jive,
    input  logic [15:0]   pipe_in_tag,
    output logic          pipe_out_valid,
    output logic [767:0]  pipe_out_state,
    output logic          pipe_out_jive,
    output logic [15:0]   pipe_out_tag,
    // Keccak, one and two rounds per clock
    input  logic          kec_start,
    input  logic          kec_nr12,
    input  logic [1599:0] kec_state_i,
    output logic          kec1_busy,
    output logic          kec1_done,
    output logic [1599:0] kec1_state_o,
    output logic          kec2_busy,
    output logic          kec2_done,
    output logic [1599:0] kec2_state_o,
    // GF(2^128)
    input  logic [127:0]  gf_a,
    input  logic [127:0]  gf_b,
    output logic [127:0]  tower_r,
    output logic [127:0]  gf_r
);
    qsag_gl64_dsp_mul #(.AW(26), .BW(17)) u_mul   (.clk(clk), .a(mul_a), .b(mul_b), .r(mul_r));
    qsag_gl64_dsp_mul #(.AW(16), .BW(16)) u_mul16 (.clk(clk), .a(mul_a), .b(mul_b), .r(mul_r16));
    qsag_gl64_reduce u_red (.clk(clk), .x(red_x), .r(red_r));
    qsag_p2_sbox7 u_sbox (.clk(clk), .x(sb_x), .y(sb_y));
    qsag_ext4_mac u_ext4 (.clk(clk), .a(e_a), .b(e_b), .c(e_c), .y(e_y));

    qsag_poseidon2_12_fpga #(.TAGW(16)) u_ring (
        .clk(clk), .rst(rst), .in_valid(ring_in_valid), .in_ready(ring_in_ready),
        .in_state(ring_in_state), .in_jive(ring_in_jive), .in_tag(ring_in_tag),
        .out_valid(ring_out_valid), .out_state(ring_out_state), .out_jive(ring_out_jive),
        .out_tag(ring_out_tag), .busy(ring_busy));

    qsag_poseidon2_12_pipe #(.TAGW(16)) u_pipe (
        .clk(clk), .rst(rst), .in_valid(pipe_in_valid), .in_state(pipe_in_state),
        .in_jive(pipe_in_jive), .in_tag(pipe_in_tag),
        .out_valid(pipe_out_valid), .out_state(pipe_out_state), .out_jive(pipe_out_jive),
        .out_tag(pipe_out_tag));

    qsag_keccak_turboshake #(.RPC(1)) u_kec1 (
        .clk(clk), .rst(rst), .start(kec_start), .nr12(kec_nr12), .state_i(kec_state_i),
        .busy(kec1_busy), .done(kec1_done), .state_o(kec1_state_o));
    qsag_keccak_turboshake #(.RPC(2)) u_kec2 (
        .clk(clk), .rst(rst), .start(kec_start), .nr12(kec_nr12), .state_i(kec_state_i),
        .busy(kec2_busy), .done(kec2_done), .state_o(kec2_state_o));

    qsag_gf128_tower_mul u_tower (.clk(clk), .a(gf_a), .b(gf_b), .r(tower_r));
    qsag_gf128_clmul u_gf (.clk(clk), .a(gf_a), .b(gf_b), .r(gf_r));
endmodule
